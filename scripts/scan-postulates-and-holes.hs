{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as BSC
import Data.IORef
import Data.List (isSuffixOf, sort)
import Data.Word (Word32)
import Foreign
import Foreign.C.ConstPtr (ConstPtr (..))
import System.Directory
import System.Environment
import System.FilePath
import System.IO
import TreeSitter

data TSLanguage_

foreign import ccall unsafe "tree_sitter_agda"
  c_tree_sitter_agda :: IO (Ptr TSLanguage_)

agdaLanguage :: IO Language
agdaLanguage = c_tree_sitter_agda >>= unsafeToLanguage . ConstPtr . castPtr

type Pst = (FilePath, Int, ByteString, ByteString)
type Hol = (FilePath, Int, ByteString)

norm :: ByteString -> ByteString
norm = BSC.unwords . BSC.words

textOf :: ByteString -> Node -> IO ByteString
textOf src n = do
  s <- nodeStartByte n
  e <- nodeEndByte n
  pure $ BS.take (fromIntegral (e - s)) (BS.drop (fromIntegral s) src)

rowOf :: Node -> IO Int
rowOf n = succ . fromIntegral . pointRow <$> nodeStartPoint n

childrenOf :: Node -> IO [Node]
childrenOf n = do
  c <- nodeChildCount n
  if c == 0 then pure [] else mapM (nodeChild n) [0 .. c - 1]

childByType :: ByteString -> Node -> IO (Maybe Node)
childByType ty parent = childrenOf parent >>= go
  where
    go []     = pure Nothing
    go (n:ns) = nodeType n >>= \t -> if t == ty then pure (Just n) else go ns

firstNamedChild :: Node -> IO (Maybe Node)
firstNamedChild n = do
  c <- nodeNamedChildCount n
  if c == 0 then pure Nothing else Just <$> nodeNamedChild n 0

isHole :: ByteString -> Bool
isHole bs = bs == "?"
         || BS.length bs >= 2 && BS.head bs == 0x21 && BS.last bs == 0x21

processFunction :: FilePath -> ByteString -> Node -> IO (Maybe Pst)
processFunction path src fn = do
  mLhs  <- childByType "lhs" fn
  mRhs  <- childByType "rhs" fn
  mExpr <- maybe (pure Nothing) firstNamedChild mRhs
  case (mLhs, mExpr) of
    (Just lhs, Just expr) -> do
      name <- norm <$> textOf src lhs
      typ  <- norm <$> textOf src expr
      row  <- rowOf fn
      pure $ Just (path, row, name, typ)
    _ -> pure Nothing

lineAt :: [ByteString] -> Int -> ByteString
lineAt ls r
  | r >= 1 && r <= length ls = ls !! (r - 1)
  | otherwise                = ""

walk
  :: IORef [Pst] -> IORef [Hol]
  -> FilePath -> ByteString -> [ByteString]
  -> Node -> IO ()
walk psRef hsRef path src ls node = do
  ty <- nodeType node
  case ty of
    "comment" -> pure ()
    "postulate" -> childrenOf node >>= mapM_ \c -> do
      ct <- nodeType c
      when (ct == "function") do
        mi <- processFunction path src c
        forM_ mi \p -> modifyIORef' psRef (p :)
    "qid" -> do
      txt <- textOf src node
      when (isHole txt) do
        row <- rowOf node
        modifyIORef' hsRef ((path, row, norm (lineAt ls row)) :)
    _ -> childrenOf node >>= mapM_ (walk psRef hsRef path src ls)

scanFile :: IORef [Pst] -> IORef [Hol] -> Parser -> FilePath -> IO ()
scanFile psRef hsRef parser path = do
  src <- BS.readFile path
  mtree <- parserParseByteString parser Nothing src
  forM_ mtree \tree -> do
    root <- treeRootNode tree
    walk psRef hsRef path src (BS.split 0x0A src) root
    unsafeTreeDelete tree

findAgda :: FilePath -> IO [FilePath]
findAgda dir = do
  entries <- listDirectory dir
  fmap concat . forM entries $ \e ->
    if e == "_build" || take 1 e == "."
      then pure []
      else do
        let p = dir </> e
        isDir <- doesDirectoryExist p
        if isDir
          then findAgda p
          else pure [p | ".agda" `isSuffixOf` p]

stripDot :: FilePath -> FilePath
stripDot ('.':'/':r) = r
stripDot p           = p

prefix :: FilePath -> Int -> B.Builder
prefix f l = B.stringUtf8 (stripDot f) <> B.char7 ':' <> B.intDec l <> B.stringUtf8 ": "

emitPst :: Pst -> B.Builder
emitPst (f, l, n, t) = prefix f l <> B.byteString n <> B.stringUtf8 " : " <> B.byteString t <> B.char7 '\n'

emitHol :: Hol -> B.Builder
emitHol (f, l, x) = prefix f l <> B.byteString x <> B.char7 '\n'

section :: String -> String -> (a -> B.Builder) -> [a] -> B.Builder
section title empty render xs =
  B.stringUtf8 title <> B.char7 '\n'
    <> if null xs
         then B.stringUtf8 empty <> B.char7 '\n'
         else foldMap render xs

main :: IO ()
main = do
  args <- getArgs
  setCurrentDirectory (case args of (a:_) -> a; _ -> ".")
  lang <- agdaLanguage
  withParser \parser -> do
    ok <- parserSetLanguage parser lang
    unless ok (error "tree-sitter: failed to set Agda language (ABI mismatch?)")
    psRef <- newIORef []
    hsRef <- newIORef []
    sort <$> findAgda "." >>= mapM_ (scanFile psRef hsRef parser)
    psts <- reverse <$> readIORef psRef
    hols <- reverse <$> readIORef hsRef
    B.hPutBuilder stdout $
      section "## Postulates" "NO POSTULATES" emitPst psts
        <> B.char7 '\n'
        <> section "## Holes" "NO HOLES" emitHol hols
