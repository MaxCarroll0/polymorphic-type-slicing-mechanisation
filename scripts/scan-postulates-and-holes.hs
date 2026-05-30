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

-- BSC.words matches 0xA0 which is a UTF-8 continuation byte — split byte-wise.
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

colOf :: Node -> IO Int
colOf n = fromIntegral . pointColumn <$> nodeStartPoint n

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

stripLeadingColon :: ByteString -> ByteString
stripLeadingColon bs =
  let bs' = BS.dropWhile (\w -> w == 0x20 || w == 0x09) bs
  in case BS.uncons bs' of
       Just (0x3A, r) -> BS.dropWhile (\w -> w == 0x20 || w == 0x09) r
       _              -> bs

firstByte :: ByteString -> Word8
firstByte bs = case BS.uncons (BS.dropWhile (\w -> w == 0x20 || w == 0x09) bs) of
  Just (b, _) -> b
  Nothing     -> 0

type Pend = (Int, ByteString, ByteString)

-- tree-sitter-agda splits multi-line decls into multiple function nodes;
-- merge orphan `: type` and `→ ...` continuations into the pending decl.
processFns :: IORef [Pst] -> FilePath -> ByteString -> [Node] -> IO ()
processFns psRef path src ns0 = drive Nothing ns0 >>= emit
  where
    emit Nothing = pure ()
    emit (Just (r, n, t)) = modifyIORef' psRef ((path, r, n, t) :)
    drive pend [] = pure pend
    drive pend (c : rest) = nodeType c >>= \case
      "function" -> do
        mLhs <- childByType "lhs" c
        mRhs <- childByType "rhs" c
        r    <- rowOf c
        case (mLhs, mRhs) of
          (Just lhs, Just rhs) -> do
            cnt <- nodeNamedChildCount rhs
            nm <- norm <$> textOf src lhs
            ty <- if cnt == 0
                    then pure ""
                    else nodeNamedChild rhs 0 >>= fmap norm . textOf src
            emit pend
            drive (Just (r, nm, ty)) rest
          (Just lhs, Nothing) -> do
            raw <- textOf src lhs
            case firstByte raw of
              0x3A -> do
                let t = norm (stripLeadingColon raw)
                case pend of
                  Just (pr, pn, pt) | BS.null pt -> drive (Just (pr, pn, t)) rest
                  Just (pr, pn, pt)              -> drive (Just (pr, pn, pt <> " " <> t)) rest
                  Nothing                        -> drive Nothing rest
              0xE2 -> case pend of
                Just (pr, pn, pt) -> drive (Just (pr, pn, pt <> " " <> norm raw)) rest
                Nothing           -> drive Nothing rest
              _ -> do
                emit pend
                drive (Just (r, norm raw, "")) rest
          _ -> drive pend rest
      _ -> drive pend rest

spanBodyFns :: Int -> [Node] -> IO ([Node], [Node])
spanBodyFns _    []       = pure ([], [])
spanBodyFns pc xs@(n : rest) = do
  ty <- nodeType n
  if ty /= "function" then pure ([], xs) else do
    c <- colOf n
    if c > pc
      then do
        (run, after) <- spanBodyFns pc rest
        pure (n : run, after)
      else pure ([], xs)

-- tree-sitter-agda puts postulate-body decls as detached top-level function
-- siblings of the keyword; sweep them up until indent drops to the keyword.
walkSeq
  :: IORef [Pst] -> IORef [Hol]
  -> FilePath -> ByteString -> [ByteString]
  -> Maybe Int -> [Node] -> IO ()
walkSeq _     _     _    _   _  _    []       = pure ()
walkSeq psRef hsRef path src ls inP (n : ns) = do
  ty <- nodeType n
  case ty of
    "comment"   -> walkSeq psRef hsRef path src ls inP ns
    "postulate" -> do
      childrenOf n >>= processFns psRef path src
      pc <- colOf n
      walkSeq psRef hsRef path src ls (Just pc) ns
    "function" -> do
      cc <- colOf n
      case inP of
        Just pc | cc > pc -> do
          (run, after) <- spanBodyFns pc (n : ns)
          processFns psRef path src run
          walkSeq psRef hsRef path src ls inP after
        _ -> do
          walk psRef hsRef path src ls n
          walkSeq psRef hsRef path src ls Nothing ns
    _ -> do
      walk psRef hsRef path src ls n
      walkSeq psRef hsRef path src ls Nothing ns

walk :: IORef [Pst] -> IORef [Hol] -> FilePath -> ByteString -> [ByteString] -> Node -> IO ()
walk psRef hsRef path src ls node = nodeType node >>= \case
  "comment"   -> pure ()
  "postulate" -> childrenOf node >>= processFns psRef path src
  "qid" -> do
    txt <- textOf src node
    when (isHole txt) do
      r <- rowOf node
      let line = if r >= 1 && r <= length ls then ls !! (r - 1) else ""
      modifyIORef' hsRef ((path, r, norm line) :)
  _ -> childrenOf node >>= walkSeq psRef hsRef path src ls Nothing

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
    if e == "_build" || take 1 e == "." || take 6 e == "result"
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
    BS.putStr "Holes mark in-progress proof fragments (UNMECHANISED in the dissertation).\n\n"
    if null hols then BS.putStr "NO HOLES\n"
    else forM_ hols \(f, l, x) -> BS.putStr (BS.concat [prefix f l, x, "\n"])
