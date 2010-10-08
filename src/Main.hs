module Main where

import Codec.Digest.SHA
import Codec.Crypto.AES
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Parallel.Strategies
import Data.Int
import Data.List
import Data.Maybe
import Data.Serialize
import Data.Word
import Numeric
import Prelude hiding (catch)
import System.Directory
import System.Environment
import System.FilePath
import System.IO
import System.Posix.Process
import System.Random
import qualified Codec.Binary.UTF8.String as U8
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map as M
import qualified Data.Vector.Unboxed as VU
import qualified System.FilePath.Find as SFF
import qualified System.Random.MWC as MWC

import Index

type Hash = BS.ByteString

type PwBytes = BS.ByteString

myName :: String
myName = "cryptogether"

chunkSize :: Word64
chunkSize = 10 * 1024^2

saltLength :: Int
saltLength = 32

iv0 :: BS.ByteString
iv0 = BS.pack $ replicate 16 0

strongHash :: PwBytes -> BS.ByteString -> Hash
strongHash pw salt = iterate (hash SHA256) (pw `BS.append` salt) !! 65535

withPw :: Bool -> (BS.ByteString -> IO a) -> IO a
withPw verify f = do
  hSetEcho stdin False
  hPutStr stderr "password: "
  hFlush stderr
  pw <- getLine
  hPutStrLn stderr ""
  let
    fin = hSetEcho stdin True >> f (BS.pack $ U8.encode pw)
  if verify
    then do
      hPutStr stderr "verify: "
      hFlush stderr
      pw2 <- getLine
      hPutStrLn stderr ""
      if pw == pw2 then fin
        else
          hPutStrLn stderr "Passwords do not match." >> hFlush stderr >>
          withPw True f
    else fin

withLock :: FilePath -> IO a -> IO a
withLock dir f = do
  pid <- getProcessID
  ifUnlocked dir $ bracket_
    (writeFile (dir </> "lock") $ show pid)
    (removeFile (dir </> "lock"))
    f

ifUnlocked :: FilePath -> IO a -> IO a
ifUnlocked dir f = do
  lockExists <- doesFileExist (dir </> "lock")
  when lockExists $ error "Lock file exists."
  f

saltPw :: FilePath -> PwBytes -> IO Hash
saltPw dir pwBytes = strongHash pwBytes <$> BS.readFile (dir </> "salt")

createSalt :: FilePath -> PwBytes -> IO ()
createSalt dir pwBytes = do
  salt <- BS.pack . VU.toList <$> MWC.withSystemRandom
    (flip MWC.uniformVector saltLength :: MWC.GenIO -> IO (VU.Vector Word8))
  BS.writeFile (dir </> "salt") salt

arcAddFile :: FilePath -> PwBytes -> FilePath -> IO ()
arcAddFile dir pwBytes file = withLock dir $ do
  encKey <- saltPw dir pwBytes
  putStrLn $ "Adding " ++ show file
  index <- readIndex dir encKey
  when (isJust . M.lookup file $ fileData index) $
    error "Filename already exists in archive."
  d <- BSL.readFile file
  chunks <- makeChunks dir $ crypt CTR encKey iv0 Encrypt d
  writeIndex dir encKey $
    index {fileData = M.insert file chunks (fileData index)}

arcList :: FilePath -> PwBytes -> IO ()
arcList dir pwBytes = ifUnlocked dir $ do
  encKey <- saltPw dir pwBytes
  index <- readIndex dir encKey
  putStr . unlines . map (\ (k, v) -> show k ++ " " ++ show (chunksToSize v)) .
    M.toList $ fileData index

arcExtractFile :: FilePath -> PwBytes -> FilePath -> IO ()
arcExtractFile dir pwBytes file = do
  encKey <- saltPw dir pwBytes
  index <- readIndex dir encKey
  putStrLn $ "Extracting " ++ show file
  doesFileExist file >>= \ t ->
    when t (error "Extracted filename already exists.")
  case M.lookup file $ fileData index of
    Nothing -> error "Filename doesn't exist in archive."
    Just chunks -> BSL.writeFile file =<<
      crypt CTR encKey iv0 Decrypt <$> readChunks dir chunks

arcRemoveFile :: FilePath -> PwBytes -> FilePath -> IO ()
arcRemoveFile dir pwBytes file = withLock dir $ do
  encKey <- saltPw dir pwBytes
  index <- readIndex dir encKey
  case M.lookup file $ fileData index of
    Nothing -> error "Filename doesn't exist in archive."
    Just chunks -> do
      mapM_ (removeFile . (dir </>) . toHex) $ init chunks
      writeIndex dir encKey $
        index {fileData = M.delete file (fileData index)}

writeIndex :: FilePath -> Hash -> Index -> IO ()
writeIndex dir encKey =
  BS.writeFile (dir </> "index") . crypt' CTR encKey iv0 Encrypt . encode

readIndex :: FilePath -> Hash -> IO Index
readIndex dir encKey = doesFileExist (dir </> "index") >>= \ t -> if t
  then do
    let
      badPw = error "Index corrupt, or wrong password?"
      catchBadPw :: ErrorCall -> a
      catchBadPw _ = badPw
    -- it was possible to get Prelude.chr (error)s if i didn't put my catch
    -- around everything.  putting it just around the decode doesn't catch
    -- everything oddly, which seems strange for strict serialization?  idk
    flip catch catchBadPw $ do
      c <- BS.readFile (dir </> "index")
      case decode $ crypt' CTR encKey iv0 Decrypt c of
        Left _ -> badPw
        Right index -> if indexVersion index == 0
          then return index
          else error "Index file version unknown, or wrong password?"
  else return $ Index 0 M.empty

toHex :: (Integral a) => a -> String
toHex a = showHex a ""

makeChunks :: FilePath -> BSL.ByteString -> IO [Word64]
makeChunks dir d = if BSL.null d
  then return [0]
  else do
    chunkId <- MWC.withSystemRandom (MWC.uniform :: MWC.GenIO -> IO Word64)
    let
      (chunkPure, rest) = BSL.splitAt (fromIntegral chunkSize) d
      (chunk, finalInfo) = if BSL.null rest
        then
          (chunkPure `BSL.append`
          BSL.replicate (fromIntegral chunkSize - l) 0, Just l)
        else (chunkPure, Nothing)
        where l = BSL.length chunkPure
      chunkF = dir </> toHex chunkId
    yikes <- doesFileExist chunkF
    when yikes $ error "Impossibly-unlikely collision occurred!"
    BSL.writeFile chunkF chunk
    case finalInfo of
      Nothing -> (chunkId:) <$> makeChunks dir rest
      Just l -> return [chunkId, fromIntegral l]

readChunks :: FilePath -> [Word64] -> IO BSL.ByteString
readChunks _dir [0] = return BSL.empty
readChunks dir (chunkId:chunkSize:[]) =
  BSL.take (fromIntegral chunkSize) <$> readSingleChunk dir chunkId
readChunks dir (chunkId:rest) =
  liftM2 BSL.append (readSingleChunk dir chunkId) (readChunks dir rest)

readSingleChunk :: FilePath -> Word64 -> IO BSL.ByteString
readSingleChunk dir chunkId = BSL.readFile $ dir </> toHex chunkId

chunksToSize [0] = 0
chunksToSize cs = chunkSize * (fromIntegral (length cs) - 2) + last cs

lookCheck :: Bool -> FilePath -> IO ()
lookCheck shouldExist dir = do
  doesDirectoryExist dir >>= \ t -> if t
    then do
      unless shouldExist . error $ show dir ++ " already exists."
      let
        notArc = error $ show dir ++ " is not a " ++ myName ++ " archive."
      doesFileExist (dir </> "index") >>= \ t2 -> unless t2 notArc
      doesFileExist (dir </> "salt") >>= \ t2 -> unless t2 notArc
    else do
      doesFileExist dir >>= \ t -> when t (error $
        show dir ++ " is a file, not a " ++ myName ++ " archive directory.")
      when shouldExist . error $ show dir ++ " doesn't exist."

binOrM :: IO Bool -> IO Bool -> IO Bool
binOrM a b = a >>= \ r -> if r then return True else b

binAndM :: IO Bool -> IO Bool -> IO Bool
binAndM a b = a >>= \ r -> if r then b else return False

andM :: [IO Bool] -> IO Bool
andM = join . foldM (\ a b -> return $ binAndM a b) (return True)

filesRec :: [FilePath] -> IO [FilePath]
filesRec files = do
  andM $ map (\ f -> binOrM (doesFileExist f) (doesDirectoryExist f)) files
  nub . concat <$>
    mapM (SFF.find SFF.always $ SFF.fileType SFF./=? SFF.Directory) files

main :: IO ()
main = do
  args <- getArgs
  let
    usage = error "Command usage incorrect."
    addFiles dir pwBytes = (mapM_ (arcAddFile dir pwBytes) =<<) . filesRec
  case args of
    "c":dir:[] -> usage
    "c":dir:files -> lookCheck False dir >> withPw True (\ pwBytes -> do
      createDirectory dir
      createSalt dir pwBytes
      addFiles dir pwBytes files
      )
    "a":dir:[] -> usage
    "a":dir:files -> lookCheck True dir >> withPw False (\ pwBytes ->
      addFiles dir pwBytes files)
    "l":dir:[] -> lookCheck True dir >> withPw False (arcList dir)
    "x":dir:[] -> usage
    "x":dir:files -> lookCheck True dir >> withPw False (\ pwBytes ->
      -- todo: directory extract/remove
      mapM_ (arcExtractPath dir pwBytes) files)
    "r":dir:[] -> usage
    "r":dir:files -> lookCheck True dir >> withPw False (\ pwBytes ->
      mapM_ (arcRemoveFile dir pwBytes) files)
    _ -> usage
