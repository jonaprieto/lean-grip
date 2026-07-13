-- Attoparsec JSON leaf-scalar counter benchmark
-- Counts: numbers, strings, true/false/null each = 1 leaf
-- Object keys are NOT counted (only values)
-- No DOM/tree built; count is accumulated directly as Int

{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Attoparsec.ByteString as A
import qualified Data.ByteString            as BS
import           System.Clock               (Clock(Monotonic), getTime, toNanoSecs)
import           Control.Exception          (evaluate)
import           Data.IORef

-- | Skip ASCII whitespace: space, tab, newline, carriage-return
skipWS :: A.Parser ()
skipWS = A.skipWhile isWS
  where
    isWS w = w == 0x20 || w == 0x09 || w == 0x0A || w == 0x0D

-- | Parse a JSON value and return its leaf count
-- Numbers, strings, true/false/null = 1
-- Arrays/objects = sum of children (container adds 0)
jsonValue :: A.Parser Int
jsonValue = do
  skipWS
  w <- A.peekWord8'
  case w of
    0x22 -> jsonString          -- '"'
    0x7B -> jsonObject          -- '{'
    0x5B -> jsonArray           -- '['
    0x74 -> jsonTrue            -- 't'
    0x66 -> jsonFalse           -- 'f'
    0x6E -> jsonNull            -- 'n'
    _    -> jsonNumber          -- digit or '-'

-- | Parse a JSON string (escape-naive: just scan to next '"')
-- Returns 1 (the string is one leaf scalar)
jsonString :: A.Parser Int
jsonString = do
  _ <- A.word8 0x22            -- opening '"'
  A.skipWhile (/= 0x22)        -- skip until closing '"'
  _ <- A.word8 0x22            -- closing '"'
  return 1

-- | Parse a JSON number (integer or float, with optional leading '-')
-- Returns 1
jsonNumber :: A.Parser Int
jsonNumber = do
  -- optional minus
  _ <- A.option () (A.word8 0x2D >> return ())  -- '-'
  -- integer part: must have at least one digit
  _ <- A.takeWhile1 isDigit
  -- optional fractional part
  _ <- A.option () $ do
    _ <- A.word8 0x2E  -- '.'
    _ <- A.takeWhile1 isDigit
    return ()
  -- optional exponent
  _ <- A.option () $ do
    _ <- A.satisfy (\x -> x == 0x65 || x == 0x45)  -- 'e' or 'E'
    _ <- A.option () (A.satisfy (\x -> x == 0x2B || x == 0x2D) >> return ())
    _ <- A.takeWhile1 isDigit
    return ()
  return 1
  where
    isDigit w = w >= 0x30 && w <= 0x39

-- | Parse "true" keyword
jsonTrue :: A.Parser Int
jsonTrue = do
  _ <- A.string "true"
  return 1

-- | Parse "false" keyword
jsonFalse :: A.Parser Int
jsonFalse = do
  _ <- A.string "false"
  return 1

-- | Parse "null" keyword
jsonNull :: A.Parser Int
jsonNull = do
  _ <- A.string "null"
  return 1

-- | Parse a JSON array; return sum of element leaf counts
jsonArray :: A.Parser Int
jsonArray = do
  _ <- A.word8 0x5B       -- '['
  skipWS
  -- check for empty array
  isEmpty <- A.option False $ do
    _ <- A.word8 0x5D     -- ']'
    return True
  if isEmpty
    then return 0
    else do
      !first <- jsonValue
      !rest  <- accumulateCommaList 0
      skipWS
      _ <- A.word8 0x5D   -- ']'
      return (first + rest)

-- | Parse a JSON object; return sum of leaf counts of VALUES only
-- (object keys are strings but NOT counted)
jsonObject :: A.Parser Int
jsonObject = do
  _ <- A.word8 0x7B       -- '{'
  skipWS
  -- check for empty object
  isEmpty <- A.option False $ do
    _ <- A.word8 0x7D     -- '}'
    return True
  if isEmpty
    then return 0
    else do
      !first <- keyValue
      !rest  <- accumulateCommaKV 0
      skipWS
      _ <- A.word8 0x7D   -- '}'
      return (first + rest)

-- | Parse "key" : value and return the VALUE leaf count only
keyValue :: A.Parser Int
keyValue = do
  skipWS
  _ <- jsonString         -- consume key (count discarded)
  skipWS
  _ <- A.word8 0x3A       -- ':'
  !v <- jsonValue         -- parse value
  return v                -- do NOT add key's count

-- | After parsing first element of array, accumulate the rest
accumulateCommaList :: Int -> A.Parser Int
accumulateCommaList !acc = do
  skipWS
  hasComma <- A.option False $ do
    _ <- A.word8 0x2C     -- ','
    return True
  if hasComma
    then do
      !v <- jsonValue
      accumulateCommaList (acc + v)
    else return acc

-- | After parsing first key-value of object, accumulate the rest
accumulateCommaKV :: Int -> A.Parser Int
accumulateCommaKV !acc = do
  skipWS
  hasComma <- A.option False $ do
    _ <- A.word8 0x2C     -- ','
    return True
  if hasComma
    then do
      !v <- keyValue
      accumulateCommaKV (acc + v)
    else return acc

-- | Top-level: parse a complete JSON document
parseJSON :: BS.ByteString -> Either String Int
parseJSON bs =
  A.parseOnly (jsonValue <* skipWS <* A.endOfInput) bs

-- | Get monotonic time in nanoseconds
nowNS :: IO Integer
nowNS = toNanoSecs <$> getTime Monotonic

main :: IO ()
main = do
  let path = "/Users/jonaprieto/research/grip/bench/data/canada.json"
  bs <- BS.readFile path  -- read entire file into memory before timing

  -- warm-up / correctness check
  case parseJSON bs of
    Left err -> error $ "Parse error (warmup): " ++ err
    Right n  ->
      if n /= 111130
        then error $ "Wrong count! Got " ++ show n ++ " but expected 111130"
        else return ()

  -- best-of-20 timing.
  -- We use an IORef to store the ByteString so GHC cannot float
  -- `parseJSON bs` into a CAF computed once outside the loop.
  bsRef <- newIORef bs
  let runs = 20 :: Int

  let doRun :: IO Integer
      doRun = do
        -- Read bs via IORef so optimizer cannot cache the parse result.
        input <- readIORef bsRef
        t0 <- nowNS
        -- Force the Int result fully before stopping the clock.
        !n <- case A.parseOnly (jsonValue <* skipWS <* A.endOfInput) input of
                Left  err -> error $ "Parse error in run: " ++ err
                Right x   -> evaluate x
        -- Use n to prevent the optimizer from eliding the call.
        _ <- evaluate n
        t1 <- nowNS
        return (t1 - t0)

  times <- mapM (\_ -> doRun) [1..runs]
  let bestNS = minimum times
  let bestMS = fromIntegral bestNS / 1.0e6 :: Double

  -- final result (use the warmup count which we know is 111130)
  case parseJSON bs of
    Left  err -> error $ "Final parse error: " ++ err
    Right n   -> do
      putStrLn $ "count=" ++ show n
      putStrLn $ "best_ms=" ++ show bestMS
