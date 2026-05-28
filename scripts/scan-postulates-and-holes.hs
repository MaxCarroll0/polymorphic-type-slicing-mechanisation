{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as B
import Data.IORef
import Data.List (sort, isSuffixOf)
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
agdaLanguage = do
  p <- c_tree_sitter_agda
  unsafeToLanguage (ConstPtr (castPtr p))

data Item
  = Pst FilePath Int ByteString ByteString
  | Hol FilePath Int ByteString

slice :: ByteString -> Word32 -> Word32 -> ByteString
slice src s e =
  let s' = fromIntegral s
      e' = fromIntegral e
  in BS.take (e' - s') (BS.drop s' src)

isSp :: Word8 -> Bool
isSp w = w == 0x20 || w == 0x09 || w == 0x0a || w == 0x0d

norm :: ByteString -> ByteString
norm = BS.intercalate " " . filter (not . BS.null) . BS.splitWith isSp

stripLeadingColon :: ByteString -> ByteString
stripLeadingColon bs =
  let s = BS.dropWhile (== 0x20) bs
  in case BS.uncons s of
       Just (c, r) | c == 0x3A -> BS.dropWhile (== 0x20) r
       _                       -> bs

childrenOf :: Node -> IO [Node]
childrenOf n = do
  c <- nodeChildCount n
  if c == 0 then pure [] else mapM (nodeChild n) [0 .. c - 1]

findKid :: ByteString -> [Node] -> IO (Maybe Node)
findKid _ [] = pure Nothing
findKid w (n:ns) = do
  t <- nodeType n
  if t == w then pure (Just n) else findKid w ns

textOf :: ByteString -> Node -> IO ByteString
textOf src n = do
  s <- nodeStartByte n
  e <- nodeEndByte n
  pure (slice src s e)

rowOf :: Node -> IO Int
rowOf n = do
  p <- nodeStartPoint n
  pure (fromIntegral (pointRow p) + 1)

processFunction :: FilePath -> ByteString -> Node -> IO (Maybe Item)
processFunction path src fn = do
  cs <- childrenOf fn
  mLhs <- findKid "lhs" cs
  mRhs <- findKid "rhs" cs
  case (mLhs, mRhs) of
    (Just lhs, Just rhs) -> do
      n <- norm <$> textOf src lhs
      t <- stripLeadingColon . norm <$> textOf src rhs
      row <- rowOf fn
      pure (Just (Pst path row n t))
    _ -> pure Nothing

isNamedHole :: ByteString -> Bool
isNamedHole bs = BS.length bs >= 2 && BS.head bs == 0x21 && BS.last bs == 0x21

isBareQ :: ByteString -> Bool
isBareQ bs = bs == "?"

lineAt :: [ByteString] -> Int -> ByteString
lineAt ls r
  | r >= 1 && r <= length ls = ls !! (r - 1)
  | otherwise                = ""

walk :: FilePath -> ByteString -> [ByteString] -> Node -> IORef [Item] -> IO ()
walk path src ls node ref = do
  ty <- nodeType node
  case ty of
    "comment"   -> pure ()
    "postulate" -> do
      cs <- childrenOf node
      forM_ cs $ \c -> do
        ct <- nodeType c
        when (ct == "function") $ do
          mi <- processFunction path src c
          forM_ mi $ \i -> modifyIORef' ref (i :)
    "qid" -> do
      txt <- textOf src node
      when (isBareQ txt || isNamedHole txt) $ do
        row <- rowOf node
        modifyIORef' ref (Hol path row (norm (lineAt ls row)) :)
    _ -> childrenOf node >>= mapM_ (\c -> walk path src ls c ref)

scanFile :: Parser -> FilePath -> IO [Item]
scanFile parser path = do
  src <- BS.readFile path
  let ls = BS.split 0x0A src
  mtree <- parserParseByteString parser Nothing src
  case mtree of
    Nothing -> pure []
    Just tree -> do
      root <- treeRootNode tree
      ref <- newIORef []
      walk path src ls root ref
      items <- reverse <$> readIORef ref
      unsafeTreeDelete tree
      pure items

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

emitPst :: Item -> B.Builder
emitPst (Pst f l n t) =
  B.stringUtf8 (stripDot f) <> B.charUtf8 ':' <> B.intDec l
    <> B.stringUtf8 ": " <> B.byteString n
    <> B.stringUtf8 " : " <> B.byteString t <> B.charUtf8 '\n'
emitPst _ = mempty

emitHol :: Item -> B.Builder
emitHol (Hol f l t) =
  B.stringUtf8 (stripDot f) <> B.charUtf8 ':' <> B.intDec l
    <> B.stringUtf8 ": " <> B.byteString t <> B.charUtf8 '\n'
emitHol _ = mempty

main :: IO ()
main = do
  args <- getArgs
  let root = case args of (a:_) -> a; _ -> "."
  setCurrentDirectory root
  lang <- agdaLanguage
  withParser $ \parser -> do
    ok <- parserSetLanguage parser lang
    unless ok (error "tree-sitter: failed to set Agda language (ABI mismatch?)")
    files <- sort <$> findAgda "."
    items <- concat <$> mapM (scanFile parser) files
    let psts = [ x | x@Pst{} <- items ]
        hols = [ x | x@Hol{} <- items ]
    let header s = B.stringUtf8 s <> B.charUtf8 '\n'
        absent s = B.stringUtf8 s <> B.charUtf8 '\n'
        body = header "## Postulates"
            <> (if null psts then absent "NO POSTULATES" else mconcat (map emitPst psts))
            <> B.charUtf8 '\n'
            <> header "## Holes"
            <> (if null hols then absent "NO HOLES" else mconcat (map emitHol hols))
    B.hPutBuilder stdout body
