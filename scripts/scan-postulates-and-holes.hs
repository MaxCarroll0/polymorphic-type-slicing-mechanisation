{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.IORef
import Data.List (isSuffixOf, sort)
import Data.Word (Word8)
import Foreign
import Foreign.C.ConstPtr (ConstPtr (..))
import System.Directory
import System.Environment
import System.FilePath
import TreeSitter

foreign import ccall unsafe "tree_sitter_agda"
  tree_sitter_agda :: IO (Ptr ())

-- BSC.words splits on Haskell isSpace which matches 0xA0 — that byte appears
-- as a UTF-8 continuation byte, so do byte-wise whitespace splitting.
asciiWs :: Word8 -> Bool
asciiWs w = w == 0x20 || w == 0x09 || w == 0x0a || w == 0x0d

norm :: ByteString -> ByteString
norm = BS.intercalate " " . filter (not . BS.null) . BS.splitWith asciiWs

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

isHole :: ByteString -> Bool
isHole bs = bs == "?"
         || BS.length bs >= 2 && BS.head bs == 0x21 && BS.last bs == 0x21

type Pst = (FilePath, Int, ByteString, ByteString)
type Hol = (FilePath, Int, ByteString)

walk :: IORef [Pst] -> IORef [Hol] -> FilePath -> ByteString -> [ByteString] -> Node -> IO ()
walk psRef hsRef path src ls = go
  where
    go node = nodeType node >>= \case
      "comment" -> pure ()
      "postulate" -> childrenOf node >>= mapM_ \c -> do
        ct <- nodeType c
        when (ct == "function") do
          mLhs <- childByType "lhs" c
          mRhs <- childByType "rhs" c >>= maybe (pure Nothing) \rhs -> do
            cnt <- nodeNamedChildCount rhs
            if cnt == 0 then pure Nothing else Just <$> nodeNamedChild rhs 0
          forM_ ((,) <$> mLhs <*> mRhs) \(lhs, expr) -> do
            n <- norm <$> textOf src lhs
            t <- norm <$> textOf src expr
            r <- rowOf c
            modifyIORef' psRef ((path, r, n, t) :)
      "qid" -> do
        txt <- textOf src node
        when (isHole txt) do
          r <- rowOf node
          let line = if r >= 1 && r <= length ls then ls !! (r - 1) else ""
          modifyIORef' hsRef ((path, r, norm line) :)
      _ -> childrenOf node >>= mapM_ go

scanFile :: IORef [Pst] -> IORef [Hol] -> Parser -> FilePath -> IO ()
scanFile psRef hsRef parser path = do
  src <- BS.readFile path
  parserParseByteString parser Nothing src >>= mapM_ \tree -> do
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

main :: IO ()
main = do
  args <- getArgs
  setCurrentDirectory $ case args of (a:_) -> a; _ -> "."
  langPtr <- tree_sitter_agda
  lang <- unsafeToLanguage (ConstPtr (castPtr langPtr))
  withParser \parser -> do
    ok <- parserSetLanguage parser lang
    unless ok (error "tree-sitter: failed to set Agda language")
    psRef <- newIORef []
    hsRef <- newIORef []
    sort <$> findAgda "." >>= mapM_ (scanFile psRef hsRef parser)
    psts <- reverse <$> readIORef psRef
    hols <- reverse <$> readIORef hsRef
    let prefix f l = BSC.pack (dropDot f ++ ':' : show l ++ ": ")
        dropDot ('.':'/':r) = r; dropDot p = p
    BS.putStr "## Postulates\n"
    if null psts then BS.putStr "NO POSTULATES\n"
    else forM_ psts \(f, l, n, t) -> BS.putStr (BS.concat [prefix f l, n, " : ", t, "\n"])
    BS.putStr "\n## Holes\n"
    if null hols then BS.putStr "NO HOLES\n"
    else forM_ hols \(f, l, x) -> BS.putStr (BS.concat [prefix f l, x, "\n"])
