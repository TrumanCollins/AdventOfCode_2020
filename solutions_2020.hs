{-# Language ScopedTypeVariables #-}
{-# Language DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}

import Data.List
import Data.Char
import Data.Int
import Data.Bits
import Data.Maybe
import Data.Function
import Numeric
import qualified Data.Set as S
import Data.Foldable (toList)  -- For sequences.
import qualified Data.Bifunctor as BF
import qualified Data.Sequence as SQ
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as HMS
import qualified GHC.Ix as IX
import qualified Data.Array as A
import qualified Data.Array.Unboxed as UA
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as UVM
import qualified Data.Graph.Inductive.Graph as GR
import qualified Data.Graph.Inductive.PatriciaTree as GRPT
import qualified Data.Graph.Inductive.Query.DFS as GRDFS
import Control.Applicative
import Control.Monad
import System.IO (hFlush, stdout)
import System.Clock
import Text.Printf

-- Helper functions for time calculations.

convertTimeToDouble :: TimeSpec -> Double
convertTimeToDouble tm = fromIntegral (sec tm) + fromIntegral (nsec tm) / 1.0e9

computeElapsedTime :: TimeSpec -> TimeSpec -> Double
computeElapsedTime startTime endTime
  = convertTimeToDouble endTime - convertTimeToDouble startTime

-- Time the computation, then print the answer along with the elapsed time. Check that the result is
-- what it should be, and if not, print an error message showing the answer computed and the
-- expected answer.

computeAndCheck :: (Integral a, Show a, PrintfArg a) => IO a -> a -> IO String
computeAndCheck solveFn correctAns = do

  -- Time the computation and make sure the calculation is done before the second time is read.

  startTime <- getTime Realtime
  result    <- solveFn
  endTime   <- result `seq` getTime Realtime

  -- Print and label the result, and left pad the answer so the timings line up.

  let diff = computeElapsedTime startTime endTime
      diffStr = printf "%0.5f sec" diff
      ansStr = show result
      ansPaddedStr = foldl' (\acc _ -> ' ' : acc) ansStr [(length ansStr)..14]
      resultStr = if result == correctAns
                  then ansPaddedStr ++ "  (" ++ diffStr ++ ")"
                  else printf "Error: expected %d, but computed %d. (%s)" correctAns result diffStr
  return resultStr

-- Same as above, but for String.

computeAndCheckS :: IO String -> String -> IO String
computeAndCheckS solveFn correctAns = do

  -- Time the computation and make sure the calculation is done before the second time is read.

  startTime <- getTime Realtime
  result    <- solveFn
  endTime   <- result `seq` getTime Realtime

  -- Print and label the result, and left pad the answer so the timings line up.

  let diff = computeElapsedTime startTime endTime
      diffStr = printf "%0.5f sec" diff
      ansStr = show result
      resultStr = if result == correctAns
                  then ansStr ++ "  (" ++ diffStr ++ ")"
                  else printf "Error: expected %s, but computed %s. (%s)" correctAns result diffStr
  return resultStr

-- Compute the value associated with the given puzzle, check for the correct answer, then print the
-- result.

computeCheckAndPrint :: (Integral a, Show a, PrintfArg a) => IO a -> String -> a -> IO ()
computeCheckAndPrint puzzleFn puzzleName correctAns = do
  result <- computeAndCheck puzzleFn correctAns
  putStrLn $ mconcat ["Result ", puzzleName, ": ", result]
  hFlush stdout

-- Same as above, but for a string output.

computeCheckAndPrintS :: IO String -> String -> String -> IO ()
computeCheckAndPrintS puzzleFn puzzleName correctAns = do
  result <- computeAndCheckS puzzleFn correctAns
  putStrLn $ mconcat ["Result ", puzzleName, ": ", result]
  hFlush stdout

-- Read a file of integers and return all of them as a list of Ints. The integers are separated by
-- whitespace or newlines.

readAllIntsFromFile :: String -> IO [Int]
readAllIntsFromFile fileName = fmap (map read . words) (readFile fileName)

-- Parser functions.

-- A parser of a given type (a) is a function that takes a string and return of list of pairs of
-- things of type (a) and remaining strings. An empty list indicates the parseing function failed,
-- and a result with more than one pair indicates that there was more than one valid parse of a
-- thing of type (a) at the start of the input string.

-- This is necessary to allow the Parser type to be made into instances of classes. P is a dummy
-- constructor.

newtype Parser a = P (String -> [(a, String)])

-- Using this newtype, a parsing function can be applied to a string using a function that removes
-- the dummy constructor. Before the function can be applied, it needs to be removed from the
-- parser context. Just return the function.

parse :: Parser a -> String -> [(a, String)]
parse (P p) = p

-- Define a parser called item which just takes the first character and fails for empty input.

item :: Parser Char
item = P (\case
             []       -> []
             (x : xs) -> [(x, xs)])

-- This makes Parser part of the Functor class.
-- Now: parse (fmap toUpper item) "abc"
--      [('A', "bc")]

instance Functor Parser where
  fmap g p = P(\inp -> case parse p inp of
                         [] -> []
                         [(v, out)] -> [(g v, out)]
                         _          -> [])  -- This case won't ever happen, but removes warning.

-- Pure just adds its argument to the result in the parse pair.
-- for <*>, this will return the first and third character.
--   three :: Parser (Char, Char)
--   three = pure g <*> item <*> item <*> item
--     where g x y z = (x, z)

instance Applicative Parser where
  pure v = P (\inp -> [(v, inp)])
  pg <*> px = P (\inp -> case parse pg inp of
                           [] -> []
                           [(g, out)] -> parse (fmap g px) out
                           _          -> [])  -- This case won't ever happen, but removes warning.

-- Make this an instance of Monad. Now:
-- three :: Parser (Char, Char)
-- three = do
--   x <- item
--   item
--   z <- item
--   return (x, z)

instance Monad Parser where
  -- (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  p >>= f = P (\inp -> case parse p inp of
                         [] -> []
                         [(v, out)] -> parse (f v) out
                         _          -> [])  -- This case won't ever happen, but removes warning.

-- This is the alternative class associated with Applicative.

instance Alternative Parser where
  empty = P (const [])
  p <|> q = P (\inp -> case parse p inp of
                         [] -> parse q inp
                         [(v, out)] -> [(v,out)]
                         _          -> [])  -- This case won't ever happen, but removes warning.

-- Define a parser that succeeds for a single character if it
-- satisfies the given predicate.
-- For example:
-- digit :: Parser Char
-- digit = sat isDigit

sat :: (Char -> Bool) -> Parser Char
sat p = do
  x <- item
  if p x then return x else empty

-- Now some basic parsers:

digit :: Parser Char
digit = sat isDigit

lower :: Parser Char
lower = sat isLower

upper :: Parser Char
upper = sat isUpper

letter :: Parser Char
letter = sat isAlpha

alphanum :: Parser Char
alphanum = sat isAlphaNum

-- Parse an alpha-numeric character or space.

alphanumSp :: Parser Char
alphanumSp = sat isAlphaNum <|> sat (== ' ')

-- Parse an identifier beginning with a letter and alpha-numeric after that.

ident :: Parser String
ident = do
  x <- letter
  xs <- many alphanum
  return (x : xs)

-- Similar to the above, but it can start with a number too and have spaces in it.

identWithSp :: Parser String
identWithSp = do
  x <- alphanum
  xs <- many alphanumSp
  return (x : xs)

-- Consume spaces.

space :: Parser ()
space = do
  _ <- many (sat isSpace)
  return ()

-- Consume one or more newline characters.

newline :: Parser ()
newline = do
  _ <- many (sat (== '\n'))
  return ()

-- Consume whitespace except newlines.

spaceNotNL :: Parser ()
spaceNotNL = do
  _ <- many (sat isSpaceNotNL)
  return ()
  where
    isSpaceNotNL :: Char -> Bool
    isSpaceNotNL ch
      | isSpace ch && ch /= '\n' = True
      | otherwise = False

-- Match a specific character in the input.

char :: Char -> Parser Char
char x = sat (== x)

-- Match a specific string in the input.

string :: String -> Parser String
string [] = return []
string (x : xs) = do
  _ <- char x
  _ <- string xs
  return (x:xs)

-- Parse and return a natural number.

nat :: Parser Int
nat = do
  xs <- some digit
  return (read xs)

-- Parse and return an integer with optional negative sign.

int :: Parser Int
int = do
    _ <- char '-'
    n <- nat
    return (-n)
  <|>
    nat

-- Given a parser, return a new one that consumes any whitespace before and after the thing parsed.

token :: Parser a -> Parser a
token p = do
  space
  v <- p
  space
  return v

-- Tokenized things.

identifier :: Parser String
identifier = token ident

natural :: Parser Int
natural = token nat

integer :: Parser Int
integer = token int

symbol :: String -> Parser String
symbol xs = token (string xs)

-- Parse a comma followed by an identifier, and return that string.

commaIdent :: Parser String
commaIdent = do
  _ <- symbol ","
  identifier

-- Parse a comma-separated list of identifiers and return the list of them.

cslOfIdents :: Parser [String]
cslOfIdents = do
  n  <- identifier
  ns <- many commaIdent
  return (n : ns)

-- Parse a comma followed by a natural number, and return that number.

commaNat :: Parser Int
commaNat = do
  _ <- symbol ","
  natural

-- Parse a comma-separated list of natural numbers and return the list of them.

cslOfNats :: Parser [Int]
cslOfNats = do
  n  <- natural
  ns <- many commaNat
  return (n : ns)

-- To parse a list of comma-separated numbers with the whole list in brackets:
-- parse nats "  [1, 2, 3 ] "
-- [([1,2,3], "")]

nats :: Parser [Int]
nats = do
  _ <- symbol "["
  ns <- cslOfNats
  _ <- symbol "]"
  return ns

-- End parser functions.

-- First sort the list of numbers and put them in a vector, then walk indices from both the
-- beginning and end of the vector, looking for a pair that sums to 2020, until the indices are
-- equal. Return the product of the two if found, and Nothing if not. Note that this is an
-- O(n*log(n)) search, the expensive part being the sort. It is possible to do something with just
-- lists, but it is complicated by what to do about the case of the number 1010. If there is just
-- one, then we don't want to find a solution with it, but if there are duplicates of it, then we
-- do. That all happens naturally with the vector approach.

puzzle_01a :: IO Int
puzzle_01a = do
  inputNumbers <- readAllIntsFromFile "puzzle_01.inp"
  let sortedVec = UV.fromList (sort inputNumbers)
      resultM = findSumMatch 2020 sortedVec
      result | isNothing resultM = -1
             | otherwise = fromJust resultM
  return result
  where

    -- Search for the given sum among two elements of the sorted vector. Return the product of the
    -- two numbers if found, and Nothing if not.

    findSumMatch :: Int -> UV.Vector Int -> Maybe Int
    findSumMatch matchVal vec = fsm 0 (UV.length vec - 1)
      where
        fsm lowInd highInd
          | lowInd >= highInd = Nothing
          | currSum > matchVal = fsm lowInd (highInd - 1)
          | currSum < matchVal = fsm (lowInd + 1) highInd
          | otherwise = Just (lowVal * highVal)
          where
            currSum = lowVal + highVal
            lowVal  = vec UV.! lowInd
            highVal = vec UV.! highInd

puzzle_01b :: IO Int
puzzle_01b = do
  inputNumbers <- readAllIntsFromFile "puzzle_01.inp"
  let sortedVec = UV.fromList (sort inputNumbers)
      resultM = findSumMatch 2020 sortedVec
      result | isNothing resultM = -1
             | otherwise = fromJust resultM
  return result
  where

    -- Search for the given sum among three elements of the sorted vector. Return the product of the
    -- three numbers if found, and Nothing if not.

    findSumMatch :: Int -> UV.Vector Int -> Maybe Int
    findSumMatch matchVal vec = fsmLow 0
      where
        elementCount = UV.length vec
        lowLimit = elementCount - 2
        maxLowVal = matchVal `quot` 3
        fsmLow currInd

          -- If there are fewer than 3 elements left to work with, then we don't have anything to
          -- try, so we failed to find anything.

          | currInd >= lowLimit = Nothing

          -- If the current value is over a third of the target value, then we don't have to search
          -- further because each sum we tried would be larger than the goal value.

          | currVal > maxLowVal = Nothing

          -- If we found two other values to go with this one resulting in the right sum, then
          -- return the product of the three.

          | isJust foundValM = Just (fromJust foundValM * currVal)

          -- Move on to the next low index.

          | otherwise = fsmLow (currInd + 1)
          where
            currVal = vec UV.! currInd

            -- Search for the right sum in the remaining elements of the vector.

            foundValM = fsmLastTwo (currInd + 1) (elementCount - 1)

            -- The value to search for given the current low value.

            goalWithoutFirstVal = matchVal - currVal

            -- Search the remaining part of the vector for two elements that have the right
            -- sum. Since the vector is sorted, we can do the search in O(n) starting with an index
            -- at one end and the other and walking them back appropriately as one is too high or
            -- low.

            fsmLastTwo lowInd highInd
              | lowInd >= highInd = Nothing
              | currSum > goalWithoutFirstVal = fsmLastTwo lowInd (highInd - 1)
              | currSum < goalWithoutFirstVal = fsmLastTwo (lowInd + 1) highInd
              | otherwise = Just (lowVal * highVal)
              where
                currSum = lowVal + highVal
                lowVal  = vec UV.! lowInd
                highVal = vec UV.! highInd

data LetterFreqConstr = LetterFreqConstr { letter_d :: Char
                                         , fstVal_d :: Int
                                         , sndVal_d :: Int
                                         } deriving Show

passwordValidWithConstr1 :: LetterFreqConstr -> String -> Bool
passwordValidWithConstr1 (LetterFreqConstr ltr lowCount highCount) password
  | letterOccCount >= lowCount && letterOccCount <= highCount = True
  | otherwise = False
  where
    letterOccCount = (length . filter (== ltr)) password

passwordValidWithConstr2 :: LetterFreqConstr -> String -> Bool
passwordValidWithConstr2 (LetterFreqConstr ltr fstIndex sndIndex) password
  | matches == 1 = True
  | otherwise = False
  where
    matches = (length . filter (== ltr)) [firstLetter, secondLetter]
    firstLetter  = if sndIndex > pwLength then '\0' else password !! (fstIndex - 1)
    secondLetter = if fstIndex > pwLength then '\0' else password !! (sndIndex - 1)
    pwLength = length password

convToPairs :: String -> (LetterFreqConstr, String)
convToPairs singleLine = (constr, pwS)
  where
    constr = LetterFreqConstr (head chS) (read lowS) (read highS)
    [lowS, highS, chS, pwS] = (words . map (\c -> if c == ':' || c == '-' then ' ' else c))
                              singleLine
puzzle_02a :: IO Int
puzzle_02a = do
  constrPwPairs <- fmap (map convToPairs . lines) (readFile "puzzle_02.inp")
  let result = (length . filter id . map (uncurry passwordValidWithConstr1)) constrPwPairs
  return result

puzzle_02b :: IO Int
puzzle_02b = do
  constrPwPairs <- fmap (map convToPairs . lines) (readFile "puzzle_02.inp")
  let result = (length . filter id . map (uncurry passwordValidWithConstr2)) constrPwPairs
  return result

-- Generate the initialization values for the tree array for a particular row.

genInitsForRow :: (Int, String) -> [((Int, Int), Bool)]
genInitsForRow (currRowI, currRowData)
  = (zip indices . map (== '#')) currRowData
  where
    indices = zip [0..] (repeat currRowI)

-- Count the trees encountered with a given slope.

countTreesWithSlope :: UA.UArray (Int, Int) Bool -> (Int, Int) -> Int
countTreesWithSlope treeArray (colInc, rowInc) = treeCount
  where
    rawTobogganLocs = zip [0,colInc..] [0,rowInc..maxRow]
    tobogganLocs = map (\(c, r) -> (c `rem` cols, r)) rawTobogganLocs
    treeOrNot = map (\(c, r) -> treeArray UA.! (c, r)) tobogganLocs
    treeCount = (length . filter id) treeOrNot
    ((_, _), (maxCol, maxRow)) = UA.bounds treeArray
    cols = maxCol + 1

puzzle_03a :: IO Int
puzzle_03a = do
  inputLines <- fmap lines (readFile "puzzle_03.inp")
  let rows = length inputLines
      cols = if null inputLines then 0 else (length . head) inputLines
      arrayInitList = (concatMap genInitsForRow . zip [0..]) inputLines
      treeArr :: UA.UArray (Int, Int) Bool
      treeArr = UA.array ((0, 0), (cols - 1, rows - 1)) arrayInitList
  return (countTreesWithSlope treeArr (3, 1))

puzzle_03b :: IO Int
puzzle_03b = do
  inputLines <- fmap lines (readFile "puzzle_03.inp")
  let rows = length inputLines
      cols = if null inputLines then 0 else (length . head) inputLines
      arrayInitList = (concatMap genInitsForRow . zip [0..]) inputLines
      treeArr :: UA.UArray (Int, Int) Bool
      treeArr = UA.array ((0, 0), (cols - 1, rows - 1)) arrayInitList
      result = (product . map (countTreesWithSlope treeArr))
               [(1, 1), (3, 1), (5, 1), (7, 1), (1, 2)]
  return result

-- Split based on empy lines.

splitIntoRecordList :: [[String]] -> [[String]] ->[[String]]
splitIntoRecordList [] [] = []
splitIntoRecordList currAcc [] = [concat currAcc]
splitIntoRecordList currAcc (x : xs)
  | null x && null currAcc = splitIntoRecordList [] xs
  | null x = concat currAcc : splitIntoRecordList [] xs
  | otherwise = splitIntoRecordList (x : currAcc) xs

-- Convert a string representing an entry to a pair consisting of entry label and ata.

toPair :: String -> (String, String)
toPair xs = (firstStr, secondStr)
  where
    secondStr = if null secondChars then [] else tail secondChars
    (firstStr, secondChars) = span (/= ':') xs

-- Ideally, we would put the values in a record, but this works well for a small case.

puzzle_04a :: IO Int
puzzle_04a = do
  inputRecords <- fmap (map (sort . map toPair) . splitIntoRecordList [] . map words . lines)
                  (readFile "puzzle_04.inp")
  let validCount = (length . filter id . map isValidSet) inputRecords
      isValidSet :: [(String, String)] -> Bool
      isValidSet xs = onlyIDs `elem` validSets
        where
          onlyIDs = map fst xs
          validSets = [["byr", "cid", "ecl", "eyr", "hcl", "hgt", "iyr", "pid"],
                       ["byr", "ecl", "eyr", "hcl", "hgt", "iyr", "pid"]]
  return validCount

puzzle_04b :: IO Int
puzzle_04b = do
  inputRecords <- fmap (map (sort . map toPair) . splitIntoRecordList [] . map words . lines)
                  (readFile "puzzle_04.inp")
  let validCount = (length . filter id . map isValidSet) inputRecords
  return validCount
    where
      isValidSet :: [(String, String)] -> Bool
      isValidSet xs = elem onlyIDs validSets && all validData xs
        where
          onlyIDs = map fst xs
          validSets = [["byr", "cid", "ecl", "eyr", "hcl", "hgt", "iyr", "pid"],
                       ["byr", "ecl", "eyr", "hcl", "hgt", "iyr", "pid"]]
          validData :: (String, String) -> Bool
          validData (field, contents)
            | field == "byr" = contentsLength == 4 && value >= 1920 && value <= 2002
            | field == "cid" = True
            | field == "ecl" = contents `elem` ["amb", "blu", "brn", "gry", "grn", "hzl", "oth"]
            | field == "eyr" = contentsLength == 4 && value >= 2020 && value <= 2030
            | field == "hcl"
              = contentsLength == 7 && head contents == '#' && all isHexDigit (tail contents)
            | field == "hgt" = let (valueStr, unit) = span isDigit contents
                                   val = read valueStr :: Int
                               in case unit of
                                    "in" -> val >= 59  && val <= 76
                                    "cm" -> val >= 150 && val <= 193
                                    _ -> False
            | field == "iyr" = contentsLength == 4 && value >= 2010 && value <= 2020
            | field == "pid" = contentsLength == 9 && all isDigit contents
            | otherwise = False
            where
              contentsLength = length contents
              value = read contents :: Int

convToBits :: String -> Int
convToBits = foldl' shiftInBit 0
  where
    shiftInBit acc x = let shiftedAcc = shiftL acc 1
                       in if x == 'B' || x == 'R' then shiftedAcc + 1 else shiftedAcc

puzzle_05a :: IO Int
puzzle_05a = do
  inputCodes <- fmap (map convToBits . lines) (readFile "puzzle_05.inp")
  return (maximum inputCodes)

puzzle_05b :: IO Int
puzzle_05b = do
  inputCodesSorted <- fmap (sort . map convToBits . lines) (readFile "puzzle_05.inp")
  let result = searchForSingleMissing inputCodesSorted
  return result
  where
    searchForSingleMissing [] = 0
    searchForSingleMissing [_] = 0
    searchForSingleMissing (x : y : xs)
      | y == x + 2 = x + 1
      | otherwise = searchForSingleMissing (y : xs)

puzzle_06a :: IO Int
puzzle_06a = do
  fmap (sum . map (length . map head . group . sort . concat)
        . splitIntoRecordList [] . map words . lines) (readFile "puzzle_06.inp")

puzzle_06b :: IO Int
puzzle_06b = do
  fmap (sum . map (length . foldl1' intersect) . splitIntoRecordList []
        . map words . lines) (readFile "puzzle_06.inp")

data EdgeDirection = TowardContaining | TowardContained

genBagKindGraph :: EdgeDirection -> [(String, [(Int, String)])]
                   -> (GRPT.Gr String Int, M.Map String Int)
genBagKindGraph edgeDir bagRelationships = (bagKindGraph, bagKindNameMap)
  where
    bagKindGraph = GR.mkGraph grNodes grEdges
    bagKindNameMap = M.fromList $ map (\(x, y) -> (y, x)) grNodes
    grNodes = zip [1..] (map fst bagRelationships)
    grEdges = concatMap convToEdgeList bagRelationships

    convToEdgeList :: (String, [(Int, String)]) -> [GR.LEdge Int]
    convToEdgeList (topBagName, heldBags) = map genEdge heldBags
      where
        topBagInd = getBagInd bagKindNameMap topBagName
        genEdge (count, bagName) = let bagInd = getBagInd bagKindNameMap bagName
                                   in case edgeDir of
                                        TowardContaining -> (bagInd, topBagInd, count)
                                        TowardContained  -> (topBagInd, bagInd, count)
    
-- Get the index associated with a name in the graph. Assume the name exists.

getBagInd :: M.Map String Int -> String -> Int
getBagInd nameToIndMap x = fromJust $ M.lookup x nameToIndMap

-- Remove periods, add a space before commas.

commasAndPeriods :: Char -> String -> String
commasAndPeriods ch acc
  | ch == '.' = acc
  | ch == ',' = ' ' : ',' : acc
  | otherwise = ch : acc

-- Convert the word 'bags' to 'bag'.

bagsToBag :: String -> String
bagsToBag str = if str == "bags" then "bag" else str

-- Call createPair with initial parameter values.

createPairFn :: [String] -> (String, [(Int, String)])
createPairFn = createPair ("", []) 0 []

-- Work through the words in a single line collecting the data in a pair.

createPair :: (String, [(Int, String)]) -> Int -> [String] -> [String]
              -> (String, [(Int, String)])
createPair (accStr, accSubBags) currCount currStrs []
  = (accStr, (currCount, stringsToName currStrs) : accSubBags)
createPair acc@(accStr, accSubBags) currCount currStrs (x : xs)
  | x == "no" = acc
  | all isDigit x = createPair acc (read x) currStrs xs
  | x == "contain" = createPair (stringsToName currStrs, accSubBags) 0 [] xs
  | x == "," = createPair (accStr, (currCount, stringsToName currStrs) : accSubBags) 0 [] xs
  | otherwise = createPair acc currCount (x : currStrs) xs

-- Once we have the words making up a kind of bag, reverse them, add spaces, and concat.

stringsToName :: [String] -> String
stringsToName = unwords . reverse

-- Convert to bag data pairs.

convToBagDataPairs :: String -> [(String, [(Int, String)])]
convToBagDataPairs
  = map (createPairFn . map bagsToBag . words . foldr commasAndPeriods []) . lines

puzzle_07a :: IO Int
puzzle_07a = do
  inputData <- fmap convToBagDataPairs (readFile "puzzle_07.inp")
  let (bagKindGraph, bagNameMap) = genBagKindGraph TowardContaining inputData
      goldBagInd = getBagInd bagNameMap "shiny gold bag"

      -- Do a depth first search to find all of the containing bags. Ignore the shiny gold bag
      -- itself.

      containingBags = tail $ GRDFS.dfs [goldBagInd] bagKindGraph
  return (length containingBags)

puzzle_07b :: IO Int
puzzle_07b = do
  inputData <- fmap convToBagDataPairs (readFile "puzzle_07.inp")
  let (bagKindGraph, bagNameMap) = genBagKindGraph TowardContained inputData
      goldBagInd    = getBagInd bagNameMap "shiny gold bag"

      -- Count the total bags contained in this one and remove one for the initial bag.

      totalBagCount = genBagCount 1 goldBagInd - 1

      -- Recursively count the number of bags contained by the initial one.

      genBagCount :: Int -> GR.Node -> Int
      genBagCount currMultiple currInd = newAcc
        where
          newAcc = sum $ currMultiple : countsFromInnerBags
          countsFromInnerBags = map genCounts (GR.out bagKindGraph currInd)
          genCounts :: GR.LEdge Int -> Int
          genCounts (_, nextNode, count) = genBagCount (currMultiple * count) nextNode

  return totalBagCount

data OpCode = Acc | Jmp | Nop deriving (Eq, Enum, Show)
data MachineQuit = Loop | Halt deriving (Eq, Enum, Show)
data Instruction = Instruction { code_d :: OpCode
                               , value_d :: Int
                               } deriving Show
data MachineState = MachineState { accum_d :: Int
                                 , instrIndex_d :: Int
                                 } deriving Show

convToOpFromString :: String -> OpCode
convToOpFromString str = case str of
                           "acc" -> Acc
                           "jmp" -> Jmp
                           "nop" -> Nop
                           _ -> error ("Unknown opcode " ++ str)

convToInstructs :: [String] -> Instruction
convToInstructs strs
  | len == 2 = let [opName, arg] = strs
                   argVal = if head arg == '+' then read (tail arg) else read arg
                   op = convToOpFromString opName
               in Instruction op argVal
  | otherwise = error ("Bad length for machine instruction: " ++ show len)
  where
    len = length strs

initialMachineState :: MachineState
initialMachineState = MachineState 0 0

executeInstruction :: Instruction -> MachineState -> MachineState
executeInstruction (Instruction code value) (MachineState accum instrIndex) = resultMachState
  where
    resultMachState = case code of
                        Nop -> incedInstrIndex `seq` MachineState accum incedInstrIndex
                        Acc -> let newAccum = incedInstrIndex `seq` accum + value
                               in newAccum `seq` MachineState newAccum incedInstrIndex
                        Jmp -> let newInstrIndex = instrIndex + value
                               in newInstrIndex `seq` MachineState accum newInstrIndex
    incedInstrIndex = instrIndex + 1

-- Run the machine until we either encounter a loop or we move off the end of the instructions
-- indicating a halt.

runUntilLoopOrEnd :: V.Vector Instruction -> S.Set Int -> MachineState
                     -> (MachineState, MachineQuit)
runUntilLoopOrEnd instrVec visitedInstrs currMachineState
  | instrIndex == instrLength = (currMachineState, Halt)
  | instrIndex > instrLength || instrIndex < 0
    = error ("Instruction index out of range: " ++ show instrIndex)
  | S.member instrIndex visitedInstrs = (currMachineState, Loop)
  | otherwise = runUntilLoopOrEnd instrVec (S.insert instrIndex visitedInstrs) newMachineState
  where
    instrLength = V.length instrVec
    instrIndex = instrIndex_d currMachineState
    newMachineState = executeInstruction (instrVec V.! instrIndex) currMachineState

puzzle_08a :: IO Int
puzzle_08a = do
  instructionVec <- fmap (V.fromList . map (convToInstructs . words) . lines)
                         (readFile "puzzle_08.inp")

  -- Run the machine until we hit a loop, and return the accumulator.

  let (resultMachState, _) = runUntilLoopOrEnd instructionVec S.empty initialMachineState

  return (accum_d resultMachState)

puzzle_08b :: IO Int
puzzle_08b = do
  instructionVec <- fmap (V.fromList . map (convToInstructs . words) . lines)
                         (readFile "puzzle_08.inp")

  -- Run the machine until we hit a loop, and return the accumulator.

  let fixedAccumVal = tryFixesUntilGood instructionVec [0..(V.length instructionVec - 1)]

  return fixedAccumVal
  where
    tryFixesUntilGood :: V.Vector Instruction -> [Int] -> Int
    tryFixesUntilGood _ [] = 0
    tryFixesUntilGood origVec (index : indexes)
      | code == Jmp = let newVec = origVec V.// [(index, Instruction Nop value)]
                          (mState, reason) = runUntilLoopOrEnd newVec S.empty initialMachineState
                      in if reason == Halt then accum_d mState
                         else tryFixesUntilGood origVec indexes
      | code == Nop = let newVec = origVec V.// [(index, Instruction Jmp value)]
                          (mState, reason) = runUntilLoopOrEnd newVec S.empty initialMachineState
                      in if reason == Halt then accum_d mState
                         else tryFixesUntilGood origVec indexes
      | otherwise = tryFixesUntilGood origVec indexes
      where
        (Instruction code value) = origVec V.! index

-- Read a file of non-negative integers, and find the first number (after the 25th) that isn't the
-- sum of two of the prior 25 numbers. Return 0 if not found.

puzzle_09a :: IO Int64
puzzle_09a = do
  resultM <- fmap (searchForFirstInvalid 0 [] . map read . lines) (readFile "puzzle_09.inp")

  when (isNothing resultM) (ioError $ userError "Error: no solution found for 9a.")

  return (fromMaybe 0 resultM)

  where
    preambleLen = 25

    -- Do the search. Keep track of the prior 25 values along with a set holding all of the sums
    -- with that number and those in front of it.

    searchForFirstInvalid :: (Integral a) => Int -> [(a, S.Set a)] -> [a] -> Maybe a
    searchForFirstInvalid _ _ [] = Nothing
    searchForFirstInvalid priorLen priorGroup (currVal : nextVals)

      -- Until we have processed the first 25 numbers, just add each new one.

      | priorLen < preambleLen  = searchForFirstInvalid (priorLen + 1) nextPrior nextVals

      -- If we found the current number in one of the 25 sets of pair sums, continue on.

      | foundCurrValInPriorSums = searchForFirstInvalid priorLen nextPrior nextVals

      -- If we didn't find the current number, then we found our answer.

      | otherwise = Just currVal
      where

        -- Check for the current number in the list of sets holding pair sums.

        foundCurrValInPriorSums = (any (S.member currVal . snd) . take preambleLen) priorGroup

        -- Generate the new list of 25 pair sum sets for the next iteration.

        nextPrior = (currVal, S.empty) : (map addSumToSet . take (preambleLen - 1)) priorGroup
        addSumToSet (priorVal, set) = (priorVal, S.insert (priorVal + currVal) set)

-- For the goal number, which was the answer to 9a, search for a consecutive group of 2 or more
-- values whose sum is the goal number. Each of the numbers in the list is non-negative.

puzzle_09b :: IO Int64
puzzle_09b = do
  ansSequenceM <- fmap (searchForSequentialSum goal minimumElements . map read . lines)
                    (readFile "puzzle_09.inp")

  when (isNothing ansSequenceM) (ioError $ userError "Error: no solution found for 9b.")

  let ansSequence = fromJust ansSequenceM
      result = minimum ansSequence + maximum ansSequence

  return result

  where
    goal = 731031916
    minimumElements = 2

    -- Given a list of non-negative integers, a goal sum, and a minimum number of sequential
    -- elements of the list, search for the goal sum in the list, returning the sequence of items if
    -- found, and Nothing if not. Also, return Nothing if the list is empty, the goal value is less
    -- than 0, or the minimum number of elements is less than 2.
    
    searchForSequentialSum :: (Integral a) => a -> Int -> [a] -> Maybe [a]
    searchForSequentialSum goalVal minElements values
      | goalVal < 0 || minElements < 2 || null values = Nothing
      | otherwise = let (first, rest) = (fromJust . uncons) values
                    in go first 1 (SQ.singleton first) rest
      where
    
        -- Go through the list of values. At each entry, add the current value to the
        -- sum/count/sequence or remove the left-most element from the running sequence, depending
        -- on the current count and sum. Check this new value for a match, if we have enough values
        -- in the sequence, and return it if it is a match or move on to the next.
    
        go _ _ _ [] = Nothing
        go currSum currCount currSeq allVals@(currVal : nextVals)

          -- A matched sum only counts if we have at least the minimum number of elements needed.

          | newSum == goalVal && newCount >= minElements = Just (toList newSeq)

          -- Continue on with the search with the new sum, count, and sequence.

          | otherwise = go newSum newCount newSeq newVals
          where
            (newSum, newCount, newSeq, newVals)

              -- Add the current value to the sum and sequence if the sum is too small or we don't
              -- have sufficient elements.

              | currCount < minElements || currSum < goalVal
                = (currSum + currVal, currCount + 1, currSeq SQ.|> currVal, nextVals)

              -- Drop the oldest element in the sequence and subtract it from the sum.

              | otherwise = let (droppedVal SQ.:< remainingSeq) = SQ.viewl currSeq
                            in  (currSum - droppedVal, currCount - 1, remainingSeq, allVals)

puzzle_10a :: IO Int
puzzle_10a = do
  (inputs :: [Int]) <- fmap (map read . lines) (readFile "puzzle_10.inp")

  when (null inputs) (ioError $ userError "Error: empty input for 10a.")

  let deviceJoltage = maximum inputs + 3
      joltagesSorted = sort (0 : deviceJoltage : inputs)
      diffs = zipWith (-) (tail joltagesSorted) joltagesSorted
      oneDiffCount   = (length . filter (== 1)) diffs
      threeDiffCount = (length . filter (== 3)) diffs

  return (oneDiffCount * threeDiffCount)

puzzle_10b :: IO Int64
puzzle_10b = do
  (inputs :: [Int]) <- fmap (map read . lines) (readFile "puzzle_10.inp")

  when (null inputs) (ioError $ userError "Error: empty input for 10b.")

  let deviceJoltage = maximum inputs + 3
      joltagesRevSorted = sortBy (flip compare) (0 : deviceJoltage : inputs)
      pathCount = computePathCount [(head joltagesRevSorted, 1)] (tail joltagesRevSorted)

  return pathCount

  where
    computePathCount [] [] = 0
    computePathCount ((_, count) : _) [] = count
    computePathCount largerCounts (x : xs) = computePathCount ((x, countFromHere) : largerCounts) xs
      where
        countFromHere = (sum . map snd . takeWhile ((<= maxJump) . fst)) largerCounts
        maxJump = x + 3

-- Generate the initialization values for the tree array for a particular row.

genInitsForRow11 :: (Int, [a]) -> [((Int, Int), a)]
genInitsForRow11 (currRowI, currRowData) = zip (zip [0..] (repeat currRowI)) currRowData

-- Unboxed array that holds a whole floor.

type FloorOccArray = UA.UArray (Int, Int) Char

-- Create array from text input in problem 11.

createArrayFromTextInput11 :: [String] -> FloorOccArray
createArrayFromTextInput11 inputLines = floorArr
  where
    maxRow = length inputLines - 1
    maxCol = (length . head) inputLines - 1
    arrayInitList = (concatMap genInitsForRow11 . zip [0..]) inputLines
    floorArr = UA.array ((0, 0), (maxCol, maxRow)) arrayInitList

-- Take an array representing a floor state and step it by 1 to the new state.  A value is passed in
-- to indicate looking just one square away versus until seeing a seat, and the number of occupied
-- ones nearby to remove a person.

oneFloorStep :: Bool -> Int -> FloorOccArray -> FloorOccArray
oneFloorStep lookJustOneStepAway countToSeat currArray = UA.array currBounds initList
  where
    initList = [((c, r), newOcc (c, r)) | c <- [lowBC..highBC], r <- [lowBR..highBR]]
    currBounds@((lowBC, lowBR), (highBC, highBR)) = UA.bounds currArray
    newOcc currLoc
      | currContents == '.' = '.'
      | currContents == 'L' = if occCount == 0 then '#' else 'L'
      | otherwise = if occCount >= countToSeat then 'L' else '#'
      where
        currContents = currArray UA.! currLoc
        occCount = countOccDirs currLoc

        countOccDirs loc = (length . filter id . map (occThisDir loc)) oneSteps
          where
            oneSteps = [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]
        occThisDir loc (cInc, rInc) = analyzeLocs locsToTry
          where
            analyzeLocs [] = False
            analyzeLocs (whatIsHere : rest)
              | whatIsHere == '.' = analyzeLocs rest
              | whatIsHere == 'L'  = False
              | otherwise = True
            locsToTry = if lookJustOneStepAway then take 1 allLocsThisDir else allLocsThisDir
            allLocsThisDir = (map (currArray UA.!) . takeWhile inBounds . drop 1)
                             (iterate (\(c', r') -> (c' + cInc, r' + rInc)) loc)
            inBounds (c', r') = c' >= lowBC && c' <= highBC && r' >= lowBR && r' <= highBR

puzzle_11a :: IO Int
puzzle_11a = do
  inputLines <- fmap lines (readFile "puzzle_11.inp")

  when (null inputLines || (null . head) inputLines) (ioError $ userError "Empty input for 11a.")

  let floorArr = createArrayFromTextInput11 inputLines
      sequenceOfStates = iterate (oneFloorStep True 4) floorArr
      finalArr = (fst . head . dropWhile (uncurry (/=)))
                 (zip sequenceOfStates (tail sequenceOfStates))

  return ((length . filter (== '#') . UA.elems) finalArr)

puzzle_11b :: IO Int
puzzle_11b = do
  inputLines <- fmap lines (readFile "puzzle_11.inp")

  when (null inputLines || (null . head) inputLines) (ioError $ userError "Empty input for 11a.")

  let floorArr = createArrayFromTextInput11 inputLines
      sequenceOfStates = iterate (oneFloorStep False 5) floorArr
      finalArr = (fst . head . dropWhile (uncurry (/=)))
                 (zip sequenceOfStates (tail sequenceOfStates))

  return ((length . filter (== '#') . UA.elems) finalArr)

convToInstr12 :: String -> (Char, Int)
convToInstr12 [] = ('\0', 0)
convToInstr12 (x : xs) = (x, read xs)

puzzle_12a :: IO Int
puzzle_12a = do
  instructStream <- fmap (concatMap (map convToInstr12 . words) . lines) (readFile "puzzle_12.inp")
  let (finalX, finalY) = fst $ foldl' makeMove ((0, 0), 0) instructStream
  return (abs finalX + abs finalY)
  where
    makeMove :: ((Int, Int), Int) -> (Char, Int) -> ((Int, Int), Int)
    makeMove ((xLoc, yLoc), dir) (instrCode, instrVal)
      = case instrCode of
          'N' -> ((xLoc, yLoc + instrVal), dir)
          'S' -> ((xLoc, yLoc - instrVal), dir)
          'E' -> ((xLoc + instrVal, yLoc), dir)
          'W' -> ((xLoc - instrVal, yLoc), dir)
          'L' -> ((xLoc, yLoc), (dir + instrVal) `mod` 360)
          'R' -> ((xLoc, yLoc), (dir - instrVal) `mod` 360)
          'F' -> case dir of
                   0 -> ((xLoc + instrVal, yLoc), dir)
                   90 -> ((xLoc, yLoc + instrVal), dir)
                   180 -> ((xLoc - instrVal, yLoc), dir)
                   270 -> ((xLoc, yLoc - instrVal), dir)
                   _   -> error "Bad direction in makeMove."
          _ -> error "Bad instruction in makeMove."

puzzle_12b :: IO Int
puzzle_12b = do
  instrStream <- fmap (concatMap (map convToInstr12 . words) . lines) (readFile "puzzle_12.inp")
  let (finalX, finalY) = (fst . foldl' makeMove ((0, 0), (10, 1))) instrStream
  return (abs finalX + abs finalY)
  where
    makeMove :: ((Int, Int), (Int, Int)) -> (Char, Int) -> ((Int, Int), (Int, Int))
    makeMove (loc@(xLoc, yLoc), way@(xWay, yWay)) (instrCode, instrVal)
      = case instrCode of
          'N' -> (loc, (xWay, yWay + instrVal))
          'S' -> (loc, (xWay, yWay - instrVal))
          'E' -> (loc, (xWay + instrVal, yWay))
          'W' -> (loc, (xWay - instrVal, yWay))          
          'L' -> let newWay = foldl' rotLeft way [1..(instrVal `quot` 90)]
                 in (loc, newWay)
          'R' -> let newWay = foldl' rotRight way [1..(instrVal `quot` 90)]
                 in (loc, newWay)
          'F' -> ((xLoc + instrVal * xWay, yLoc + instrVal * yWay), way)
          _ -> error "Bad instruction in makeMove."
    rotLeft  (x, y) _ = (-y, x)
    rotRight (x, y) _ = (y, -x)

-- Compute the extended GCD of two integers, where the result is (t1, t2, gcd)
-- For example: extGCD 24 9 = (-1, 3, 3), so (gcd 24 9) == 3, and
--     -1 * 24 + 3 * 9 = 3

extGCD :: (Integral a) => a -> a -> (a, a, a)
extGCD a 0 = (1, 0, a)
extGCD a b = let (q, r) = a `divMod` b
                 (s, t1, g) = extGCD b r
                 t2 = s - q * t1
             in t2 `seq` (t1, t2, abs g)

-- Returns the modular multiplicative inverse given a value and a modulus. If there is not a single
-- valid one, then Nothing is returned. The idea here is that to use division while keeping the
-- result of a computation (mod m), it's easy using multiplications, addition, and subtraction and
-- then just do a (mod m) after, but for division, it is harder. If you can find the multiplicative
-- inverse of a divisor given the modulus, then you can multiply by that to get the result.
-- Always return a non-negative value, although extGCD will also return negative ones.

modularMultInverseM :: (Integral a) => a -> a -> Maybe a
modularMultInverseM modVal val
  | gcdVal == 1 = let nonNegT1 = if t1 < 0 then t1 + modVal else t1 in nonNegT1 `seq` Just nonNegT1
  | otherwise = Nothing
  where (t1, _, gcdVal) = extGCD val modVal

-- Given a set of modular congruences, solve for the smallest value satisfying them all.  This is
-- used to find the least answer for the Chinese Remainder Theorem. For example: x = 2 mod 3; x = 3
-- mod 5; and x = 2 mod 7, call this function with [2, 3, 2] [3, 5, 7], and it will return the
-- smallest x that is consistent with all these equations, which is 23 in this case. Note that the
-- residues need to all be smaller than the corresponding modVals, and the modVals need to all be
-- relatively prime. See page 68 of "Number Theory" by George Andrews for the technique.

solveMinLinCongruenceChineseRemainder :: (Integral a) => [a] -> [a] -> Maybe a
solveMinLinCongruenceChineseRemainder residues modVals
  | any isNothing nCompValsM = Nothing
  | otherwise = Just result
  where
    result = ((`mod` fullProduct) . sum) (zipWith3 (\a b c -> a * b * c) residues nVals nCompVals)
    nVals  = map (div fullProduct) modVals
    fullProduct = product modVals
    nCompValsM  = zipWith modularMultInverseM modVals nVals
    nCompVals   = map fromJust nCompValsM

-- This one is just finding the smallest of the goal time mod each of the bus cycle times, and
-- subtracting that from the bus cycle time itself.

puzzle_13a :: IO Int
puzzle_13a = do
  inputLines <- fmap lines (readFile "puzzle_13.inp")

  when (length inputLines /= 2) (ioError $ userError "There must be 2 input lines 13a.")

  let goalTime = (read . head) inputLines
      busCycleTimes = (map read . words . map removeCommasAndXs . head . tail) inputLines
      timesAfterGoal = map (\x -> (x, x - goalTime `rem` x)) busCycleTimes

  return ((uncurry (*) . minimumBy (compare `on` snd)) timesAfterGoal)
  where
    removeCommasAndXs ch = if ch == ',' || ch == 'x' then ' ' else ch

-- This part was more difficult and involves finding the expected mod value for each of the bus
-- cycle times, and using the extended Euclidian algorithm to find the result. It is related to the
-- Chinese Remainder Theorem.

puzzle_13b :: IO Integer
puzzle_13b = do
  inputLines <- fmap lines (readFile "puzzle_13.inp")

  when (length inputLines /= 2) (ioError $ userError "There must be 2 input lines 13b.")

  let cycleTimeLine = inputLines !! 1

      -- Separate the numbers and xs into words, index them from 0, then remove the ones with xs,
      -- and finally create pairs with the index, which is the arrival goal, and the bus cycle time.

      timeGoalsAndCycleTimes = (map (BF.second read) . filter ((/= "x") . snd)
                                . zip [0..] . words . map (\c -> if c == ',' then ' ' else c))
                               cycleTimeLine
      modGoalsAndCycleTimes = map calcModGoal timeGoalsAndCycleTimes
      (modVals, cycleVals) = unzip modGoalsAndCycleTimes
      resultM = solveMinLinCongruenceChineseRemainder modVals cycleVals

  when (isNothing resultM) (ioError $ userError "Problem 13b doesn't have a unique answer.")

  return (fromJust resultM)
    where

      -- Find the modular goal, which is value such that the bus arrives at the proper time based on
      -- the place in the list of inputs.

      calcModGoal :: (Integer, Integer) -> (Integer, Integer)
      calcModGoal (goalTime, busCycleTime) = (modGoal, busCycleTime)
        where
          modGoal  = if modGoal1 == busCycleTime then 0 else modGoal1
          modGoal1 = (busCycleTime - goalTime) `mod` busCycleTime

data MaskedMemInstr = MaskInstr Int64 Int64 [Int] | MemStore Int64 Int64 deriving (Show)
data MachState14 = MachState14 Int64 Int64 [Int] (M.Map Int64 Int64) deriving (Show)
data Puzzle14Part = Part1 | Part2 deriving (Show, Eq)

executeInstr14 :: Puzzle14Part -> MachState14 -> MaskedMemInstr -> MachState14
executeInstr14 _ (MachState14 _ _ _ currMem) (MaskInstr andMask orMask varBits)
  = MachState14 andMask orMask varBits currMem
executeInstr14 part (MachState14 currAndMask currOrMask currVarBits currMem) (MemStore addr value)
  | part == Part1
    = MachState14 currAndMask currOrMask currVarBits
                  (M.insert addr (value .&. currAndMask .|. currOrMask) currMem)
  | otherwise = let newMem = foldl' (\m adr -> M.insert adr value m) currMem allAddrs
                    baseAddr = addr .|. currOrMask
                    allAddrs = foldl' addBothBits [baseAddr] currVarBits
                    addBothBits currAddrs varBit = map (`clearBit` varBit) currAddrs
                                                   ++ map (`setBit` varBit) currAddrs
                in MachState14 currAndMask currOrMask currVarBits newMem

readMaskInstr :: Puzzle14Part -> [String] -> MaskedMemInstr
readMaskInstr _ [] = error "Error: Empty instruction in problem 14."
readMaskInstr part (instrStr : rest)
  | instrStr == "mask" && part == Part1
    = let andMask = foldl' (\acc ch -> shiftL acc 1 + (if ch == '0' then 0 else 1)) 0 (head rest)
          orMask  = foldl' (\acc ch -> shiftL acc 1 + (if ch == '1' then 1 else 0)) 0 (head rest)
      in MaskInstr andMask orMask []
  | instrStr == "mask" && part == Part2
    = let andMask = 0xFFFFFFFFF
          orMask  = foldl' (\acc ch -> shiftL acc 1 + (if ch == '1' then 1 else 0)) 0 (head rest)
          varBits = foldl' (\acc ch -> let newAcc = map (+ 1) acc
                                       in if ch /= 'X' then newAcc else 0 : newAcc) [] (head rest)
      in MaskInstr andMask orMask varBits
  | instrStr == "mem"  = let addr  = read (head rest)
                             value = read (rest !! 1)
                         in MemStore  addr value
  | otherwise = error "Error: bad instruction in problem 14."

-- Remove extra characters so 'words' does the right thing.

remChars :: Char -> Char
remChars ch = if ch == '[' || ch == ']' || ch == '=' then ' ' else ch

puzzle_14a :: IO Int64
puzzle_14a = do
  maskMemInstrs <- fmap (map (readMaskInstr Part1) . filter (not . null)
                          . map (words . map remChars) . lines) (readFile "puzzle_14.inp")
  let (MachState14 _ _ _ currMemMap)
        = foldl' (executeInstr14 Part1) (MachState14 0 0 [] M.empty) maskMemInstrs
      sumOfMemVals = M.foldl' (+) 0 currMemMap
  return sumOfMemVals

puzzle_14b :: IO Int64
puzzle_14b = do
  maskMemInstrs <- fmap (map (readMaskInstr Part2) . filter (not . null)
                          . map (words . map remChars) . lines) (readFile "puzzle_14.inp")
  let (MachState14 _ _ _ currMemMap)
        = foldl' (executeInstr14 Part2) (MachState14 0 0 [] M.empty) maskMemInstrs
      sumOfMemVals = M.foldl' (+) 0 currMemMap
  return sumOfMemVals

type Map15 = HMS.HashMap Int Int

calcNumberAfterIterations :: [Int] -> Int -> Int
calcNumberAfterIterations initNumbers limit = lastNumber
  where
    initMap = HMS.fromList (zip (init initNumbers) [1..])
    lenInit = length initNumbers
    (lastNumber, _) = foldl' nextStep (last initNumbers, initMap) [(lenInit + 1)..limit]

    nextStep :: (Int, Map15) -> Int -> (Int, Map15)
    nextStep (lastNum, currMap) currIndex
      | isNothing lastUseM = newMap `seq` (0, newMap)
      | otherwise = let lastUse = fromJust lastUseM
                        diffToLast = currIndex - 1 - lastUse
                    in diffToLast `seq` (diffToLast, newMap)
      where
        newMap   = HMS.insert lastNum (currIndex - 1) currMap
        lastUseM = HMS.lookup lastNum currMap

puzzle_15a :: IO Int
puzzle_15a = do
  initNumbers <- fmap (map read . words . map (\ch -> if ch == ',' then ' ' else ch) . head . lines)
                      (readFile "puzzle_15.inp")
  return (calcNumberAfterIterations initNumbers 2020)

-- In the first part of this one, using a hashmap for the prior values was fine and completed very
-- quickly. For the much larger number of iterations, a mutable vector was needed.

puzzle_15b :: IO Int
puzzle_15b = do
  initNumbers <- fmap (map read . words . map (\ch -> if ch == ',' then ' ' else ch) . head . lines)
                      (readFile "puzzle_15.inp")

  let limit = 30000000

  -- Create a vector of zeros, except for the initialization list. We use each value in that list as
  -- the index, and the turn it was used as the associated value.

  v <- UVM.new (limit + 1)
  mapM_ (uncurry (UVM.write v)) (zip [0..limit] (repeat (0 :: Int)) ++ zip initNumbers [1..])

  -- Walk through the remaining turns using and updating the mutable vector for values and
  -- turns. The result of this is returned.

  foldM (nextStep v) (last initNumbers) [(length initNumbers + 1)..limit]

  where

    -- Given the last number and current turn, compute the next number.

    nextStep v lastNum turn = do
      lastUse <- UVM.read v lastNum
      UVM.write v lastNum (turn - 1)
      return (if lastUse == 0 then 0 else turn - 1 - lastUse)

-- Problem 16 is the first of these that requires more full parsing of the input.

data FieldNameAndRanges = FieldNameAndRanges { name_d  :: String
                                             , ranges_d :: [(Int, Int)]
                                             } deriving Show
newtype MyTicket = MyTicket { numbers_d :: [Int] } deriving Show
newtype NearTickets = NearTickets { numbersList_d :: [[Int]] } deriving Show
data Prob16Data = Prob16Data { fieldNamesAndRanges_d :: [FieldNameAndRanges]
                             , myTicket_d :: MyTicket
                             , nearTickets_d :: NearTickets
                             } deriving Show

-- Parse the part of the input for my ticket.

myTicketP :: Parser MyTicket
myTicketP = do
  _ <- symbol "your ticket:"
  ns <- cslOfNats
  return (MyTicket ns)

-- Parse the input for nearby tickets.

nearTicketsP :: Parser NearTickets
nearTicketsP = do
  _ <- symbol "nearby tickets:"
  result <- some cslOfNats
  return (NearTickets result)

-- Parse a range in the first section of input.

rangeP :: Parser (Int, Int)
rangeP = do
  x <- nat
  _ <- symbol "-"
  y <- nat
  return (x, y)

-- Parse a field name and ranges associated, and return them in a record.

fieldAndRangeP :: Parser FieldNameAndRanges
fieldAndRangeP = do
  space
  name <- identWithSp
  _ <- symbol ":"
  x <- token rangeP
  xs <- many orAndRange
  return (FieldNameAndRanges name (x : xs))
  where
    orAndRange = do
      _ <- symbol "or"
      token rangeP

-- Parse one or more field name and ranges lines.

fieldsAndRangesP :: Parser [FieldNameAndRanges]
fieldsAndRangesP = do
  some fieldAndRangeP

-- Parse the whole input.

fieldNamesAndRanges :: Parser Prob16Data
fieldNamesAndRanges = do
  fieldsAndRanges <- fieldsAndRangesP
  space  -- This is not actually needed because spaces are consumed at the end of fieldsAndRangesP.
  myTicket <- myTicketP
  space  -- This is not actually needed because spaces are consumed at the end of myTicketP.
  nearTickets <- nearTicketsP
  return (Prob16Data fieldsAndRanges myTicket nearTickets)

-- Returns true if the value is not within any of the given ranges.

notInAnyRange16 :: [(Int, Int)] -> Int -> Bool
notInAnyRange16 allRanges value = all notInRange allRanges
  where
    notInRange :: (Int, Int) -> Bool
    notInRange (low, high) = not (value >= low && value <= high)

puzzle_16a :: IO Int
puzzle_16a = do
  parseRes <- fmap (parse fieldNamesAndRanges) (readFile "puzzle_16.inp")

  -- Make sure the input data was parsed correctly, unambigiously, and fully.

  when (null parseRes || (not . null) (tail parseRes) || (not . null . snd . head) parseRes)
       (ioError $ userError "Parse error in input for puzzle 16a.")

  let puzzleData = (fst . head) parseRes
      allRanges = (concatMap ranges_d . fieldNamesAndRanges_d) puzzleData
      allNearby = (concat . numbersList_d . nearTickets_d) puzzleData
      sumOfInvalid = (sum . filter (notInAnyRange16 allRanges)) allNearby
  return sumOfInvalid

puzzle_16b :: IO Int
puzzle_16b = do
  parseRes <- fmap (parse fieldNamesAndRanges) (readFile "puzzle_16.inp")

  -- Make sure the input data was parsed correctly, unambigiously, and fully.

  when (null parseRes || (not . null) (tail parseRes) || (not . null . snd . head) parseRes)
       (ioError $ userError "Parse error in input for puzzle 16b.")

  let puzzleData = (fst . head) parseRes
      fieldNamesAndRngs = fieldNamesAndRanges_d puzzleData
      rangeSetsAndInds = (zip [0..] . map ranges_d) fieldNamesAndRngs
      fieldNameVec = V.fromList (map (take 9 . name_d) fieldNamesAndRngs)
      allNearbyLists = (numbersList_d . nearTickets_d) puzzleData
      allNearbyRangeSets = map (map (fieldsValidFor rangeSetsAndInds)) allNearbyLists
      filtNearbyRangeSets = filter noneAreEmptySets allNearbyRangeSets
      combinedSets = (sortOnSize . zip [0..] . foldl1' (zipWith S.intersection)) filtNearbyRangeSets

      -- Here we have a mapping from position (zero-based) to index in the list of fields.

      mapPairs = (sortBy (compare `on` fst) . chooseOneToOne) combinedSets
      pairsMyTicketAndField = zipWith combine ((numbers_d . myTicket_d) puzzleData) mapPairs
        where
          combine :: Int -> (Int, Int) -> (Int, String)
          combine myTicketVal (_, fieldIndex) = (myTicketVal, fieldNameVec V.! fieldIndex)
      result = (product . map fst . filter ((== "departure") . snd)) pairsMyTicketAndField

  return result
  where
    chooseOneToOne :: [(Int, S.Set Int)] -> [(Int, Int)]
    chooseOneToOne [] = []
    chooseOneToOne ((ind, set) : xs)
      | S.size set == 1 = let [x] = S.toList set
                              newXs = map (BF.second (S.delete x)) xs
                              newXsSorted = sortOnSize newXs
                          in (ind, x) : chooseOneToOne newXsSorted
      | otherwise = error "Error: set size isn't 1 in chooseOneToOne."
    sortOnSize :: [(Int, S.Set Int)] -> [(Int, S.Set Int)]
    sortOnSize = sortBy (compare `on` (S.size . snd))
    fieldsValidFor :: [(Int, [(Int, Int)])] -> Int -> S.Set Int
    fieldsValidFor indexesAndRanges value = S.fromAscList fieldsValidIn
      where
        fieldsValidIn = (map fst . filter (\(_, xs) -> (not . notInAnyRange16 xs) value))
                        indexesAndRanges
    noneAreEmptySets :: [S.Set Int] -> Bool
    noneAreEmptySets xs = not $ any S.null xs

convToBool17 :: Char -> Bool
convToBool17 ch = case ch of
                    '.' -> False
                    '#' -> True
                    _   -> error "Bad input character for puzzle_17."

-- These two problems for 17 were fairly straightforward, but involved a lot of code. I used
-- tuples of size 3 and 4 to hold coordinates. It would be better to use lists of Ints as
-- coordinates (of length 3 and 4), but these aren't allowed as array indicies.

checkForError17 :: [[Bool]] -> IO ()
checkForError17 inputStrings = do

  -- Check that there was input, the first line has something in it, and all the lines are the same
  -- length.

  let firstLine    = head inputStrings
      lenFirstLine = length firstLine

  when (null inputStrings || null firstLine || any ((/= lenFirstLine) . length) inputStrings)
       (ioError $ userError "Empty input in 17.")

puzzle_17a :: IO Int
puzzle_17a = do
  parseRes <- fmap (map (map convToBool17) . lines) (readFile "puzzle_17.inp")

  checkForError17 parseRes

  let xWid = length (head parseRes)
      yWid = length parseRes
      (xArrHigh, yArrHigh) = (xWid - 1, yWid - 1)
      initialArr :: UA.UArray (Int, Int, Int) Bool
      initialArr = UA.array ((0, 0, 0), (xWid - 1, yWid - 1, 0)) (zip initIndList (concat parseRes))
      initIndList = [(x, y, 0) | y <- [0..yArrHigh], x <- [0..xArrHigh]]
      finalArr = foldl' nextCycle initialArr [1..6]
      totalActive = (length . filter id) (UA.elems finalArr)
      
  return totalActive
  where
    nextCycle :: UA.UArray (Int, Int, Int) Bool -> Int -> UA.UArray (Int, Int, Int) Bool
    nextCycle currArr _ = newArr
      where
        newArr = UA.array newBounds newArrInitList
        newBounds@((newLowX, newLowY, newLowZ), (newHighX, newHighY, newHighZ))
          = ((lowX - 1, lowY - 1, lowZ - 1), (highX + 1, highY + 1, highZ + 1))
        ((lowX, lowY, lowZ), (highX, highY, highZ)) = UA.bounds currArr
        newArrInitList = [(coords, compVal coords) | x <- [newLowX..newHighX],
                          y <- [newLowY..newHighY], z <- [newLowZ..newHighZ],
                          let coords = (x, y, z)]
        compVal :: (Int, Int, Int) -> Bool
        compVal currCoord@(x, y, z)
          | inCurrRange currCoord && currArr UA.! currCoord = nearbyActive == 2 || nearbyActive == 3
          | otherwise = nearbyActive == 3
          where
            nearbyActive = (length . filter id) nearbyLastContents
            nearbyLastContents = map (currArr UA.!) nearbyCoords
            nearbyCoords = [(x', y', z') |
                            xAdj <- [(-1)..1], let x' = x + xAdj, inRange x' lowX highX,
                            yAdj <- [(-1)..1], let y' = y + yAdj, inRange y' lowY highY,
                            zAdj <- [(-1)..1], let z' = z + zAdj, inRange z' lowZ highZ,
                            xAdj /= 0 || yAdj /= 0 || zAdj /= 0]
            inCurrRange (x', y', z')
              = inRange x' lowX highX && inRange y' lowY highY && inRange z' lowZ highZ
            inRange val lowLim highLim = val >= lowLim && val <= highLim

puzzle_17b :: IO Int
puzzle_17b = do
  parseRes <- fmap (map (map convToBool17) . lines) (readFile "puzzle_17.inp")

  checkForError17 parseRes

  let xWid = length (head parseRes)
      yWid = length parseRes
      (xArrHigh, yArrHigh) = (xWid - 1, yWid - 1)
      initialArr :: UA.UArray (Int, Int, Int, Int) Bool
      initialArr = UA.array ((0, 0, 0, 0), (xWid - 1, yWid - 1, 0, 0))
                   (zip initIndList (concat parseRes))
      initIndList = [(x, y, 0, 0) | y <- [0..yArrHigh], x <- [0..xArrHigh]]
      finalArr = foldl' nextCycle initialArr [1..6]
      totalActive = (length . filter id) (UA.elems finalArr)
      
  return totalActive
  where
    nextCycle :: UA.UArray (Int, Int, Int, Int) Bool -> Int
                 -> UA.UArray (Int, Int, Int, Int) Bool
    nextCycle currArr _ = newArr
      where
        newArr = UA.array newBounds newArrInitList
        newBounds@((newLowX, newLowY, newLowZ, newLowW), (newHighX, newHighY, newHighZ, newHighW))
          = ((lowX - 1, lowY - 1, lowZ - 1, lowW - 1), (highX + 1, highY + 1, highZ + 1, highW + 1))
        ((lowX, lowY, lowZ, lowW), (highX, highY, highZ, highW)) = UA.bounds currArr
        newArrInitList = [(coords, compVal coords) | x <- [newLowX..newHighX],
                          y <- [newLowY..newHighY], z <- [newLowZ..newHighZ],
                          w <- [newLowW..newHighW], let coords = (x, y, z, w)]
        compVal :: (Int, Int, Int, Int) -> Bool
        compVal currCoord@(x, y, z, w)
          | inCurrRange currCoord && currArr UA.! currCoord = nearbyActive == 2 || nearbyActive == 3
          | otherwise = nearbyActive == 3
          where
            nearbyActive = (length . filter id) nearbyLastContents
            nearbyLastContents = map (currArr UA.!) nearbyCoords
            nearbyCoords = [(x', y', z', w') |
                            xAdj <- [(-1)..1], let x' = x + xAdj, inRange x' lowX highX,
                            yAdj <- [(-1)..1], let y' = y + yAdj, inRange y' lowY highY,
                            zAdj <- [(-1)..1], let z' = z + zAdj, inRange z' lowZ highZ,
                            wAdj <- [(-1)..1], let w' = w + wAdj, inRange w' lowW highW,
                            xAdj /= 0 || yAdj /= 0 || zAdj /= 0 || wAdj /= 0]
            inCurrRange (x', y', z', w')
              = inRange x' lowX highX && inRange y' lowY highY && inRange z' lowZ highZ
                && inRange w' lowW highW
            inRange val lowLim highLim = val >= lowLim && val <= highLim

-- For problem 18a we create a parse tree so we can evaluate in the right order.

data ParseTree18a = OpPlus | OpMult | Parens [ParseTree18a] | Term Int deriving Show

expr18a :: Parser [ParseTree18a]
expr18a = do
            value1 <- parensOrNat18a
            do
                _ <- symbol "+"
                value2 <- expr18a
                return (value1 : OpPlus : value2)
              <|> do
                _ <- symbol "*"
                value2 <- expr18a
                return (value1 : OpMult : value2)
              <|>
                return [value1]

parensOrNat18a :: Parser ParseTree18a
parensOrNat18a = do
                   _ <- symbol "("
                   tree <- expr18a
                   _ <- symbol ")"
                   return (Parens tree)
                 <|> do
                   value <- natural
                   return (Term value)

parse18aLine :: Parser [ParseTree18a]
parse18aLine = expr18a

data ExprProcState = None | Op (Int -> Int -> Int)

computeExprList :: [ParseTree18a] -> Int
computeExprList exprList = result
  where
    (result, _) = foldl' combineNext (0, None) exprList
    combineNext :: (Int, ExprProcState) -> ParseTree18a -> (Int, ExprProcState)
    combineNext (_, None) (Parens tree) = (computeExprList tree, None)
    combineNext (accVal, Op fn) (Parens tree) = (fn accVal (computeExprList tree), None)
    combineNext (_, None) (Term val) = (val, None)
    combineNext (accVal, Op fn) (Term val) = (fn accVal val, None)
    combineNext (accVal, _) OpPlus = (accVal, Op (+))
    combineNext (accVal, _) OpMult = (accVal, Op (*))

-- Return true if all of the lines resulted in a single valid parse.

badParseOfInput :: [[(a, String)]]-> Bool
badParseOfInput xs = any null xs || (not . all (null . tail)) xs || (not . all (null . snd . head)) xs

puzzle_18a :: IO Int
puzzle_18a = do
  parseRes <- fmap (map (parse parse18aLine) . lines) (readFile "puzzle_18.inp")

  when (badParseOfInput parseRes)
       (ioError $ userError "Parse error in input for puzzle 18a.")

  let expressions = map (fst . head) parseRes
      values = map computeExprList expressions

  return (sum values)

expr18b :: Parser Int
expr18b = do
            t <- term18b
            do
                _ <- symbol "*"
                ex <- expr18b
                return (t * ex)
              <|>
                return t

term18b :: Parser Int
term18b = do
            f <- factor18b
            do
                _ <- symbol "+"
                t <- term18b
                return (f + t)
              <|>
                return f

factor18b :: Parser Int
factor18b = do
              _ <- symbol "("
              value <- expr18b
              _ <- symbol ")"
              return value
            <|>
              natural

parse18bLine :: Parser Int
parse18bLine = expr18b

puzzle_18b :: IO Int
puzzle_18b = do
  parseRes <- fmap (map (parse parse18bLine) . lines) (readFile "puzzle_18.inp")

  when (badParseOfInput parseRes)
       (ioError $ userError "Parse error in input for puzzle 18b.")

  let values = map (fst . head) parseRes

  return (sum values)

data Rules19 = RuleChar Char | RuleBuild [[Int]] | RuleString String deriving Show

barAndNatural :: Parser [Int]
barAndNatural = do
                  _ <- symbol "|"
                  some natural
--                  naturals <- some natural
--                  return naturals

parseRule19 :: Parser (Int, Rules19)
parseRule19 = do
                  ind <- natural
                  _ <- symbol ":"
                  do
                      _ <- symbol "\""
                      ch <- letter
                      _ <- symbol "\""
                      return (ind, RuleChar ch)
                    <|> do
                      firsts <- some natural
                      others <- many barAndNatural
                      return (ind, RuleBuild (firsts : others))
                <|> do
                  letters <- some letter
                  return (-1, RuleString letters)

-- This works with both 19a and 19b, and solves the problem of loops in rules by returning if the
-- input partial matches are empty.

matchStringWithRules :: [(String, String)] -> Int -> V.Vector Rules19 -> [(String, String)]
matchStringWithRules [] _ _ = []
matchStringWithRules currStates ruleIndex ruleVec = followRule (ruleVec V.! ruleIndex)
  where
    followRule (RuleChar ch) = foldr matchSingleChar [] currStates
      where
        matchSingleChar (_, []) acc = acc
        matchSingleChar (currMatched, x : xs) acc
          | x == ch = (x : currMatched, xs) : acc
          | otherwise = acc
    followRule (RuleBuild subRuleSets) = (filter (not . null) . concat) separateResultSets
      where
        separateResultSets = map matchSeqRules subRuleSets
        matchSeqRules :: [Int] -> [(String, String)]
        matchSeqRules = foldl' matchRule currStates
          where
            matchRule states rule = matchStringWithRules states rule ruleVec
    followRule (RuleString _) = []  -- This should never occurr.

divideRules :: ([(Int, Rules19)], [String]) -> [((Int, Rules19), String)]
               -> ([(Int, Rules19)], [String])
divideRules (accRules, accStrings) [((-1, RuleString str), _)] = (accRules, str : accStrings)
divideRules (accRules, accStrings) [((ind, rule), _)] = ((ind, rule) : accRules, accStrings)
divideRules acc _ = acc

isItMatched :: V.Vector Rules19 -> String -> Bool
isItMatched ruleVec str
  | null matchOptions = False
  | (isJust . find (null . snd)) matchOptions = True
  | otherwise = False
  where
    matchOptions = matchStringWithRules [([], str)] 0 ruleVec

puzzle_19a :: IO Int
puzzle_19a = do
  parseResults <- fmap (map (parse parseRule19) . filter (not . null) . lines) (readFile "puzzle_19.inp")

  when (badParseOfInput parseResults)
       (ioError $ userError "Parse error in input for puzzle 19a.")

  let (rules, strings) = foldl' divideRules ([], []) parseResults
      ruleVec = V.fromList ((map snd . sortBy (compare `on` fst)) rules)
      matchCount = (length . filter id . map (isItMatched ruleVec)) strings

  return matchCount

puzzle_19b :: IO Int
puzzle_19b = do
  parseResults <- fmap (map (parse parseRule19) . filter (not . null) . lines) (readFile "puzzle_19_a.inp")

  when (badParseOfInput parseResults)
       (ioError $ userError "Parse error in input for puzzle 19b.")

  let (rules, strings) = foldl' divideRules ([], []) parseResults
      ruleVec = V.fromList ((map snd . sortBy (compare `on` fst)) rules)
      matchCount = (length . filter id . map (isItMatched ruleVec)) strings

  return matchCount

-- Parser functions for Problem 20.

dotOrHash :: Parser Bool
dotOrHash = do
                _ <- sat (== '.')
                return False
              <|> do
                _ <- sat (== '#')
                return True
parseFile20 :: Parser TileInfoParse
parseFile20 = do
                  _ <- symbol "Tile "
                  ind <- natural
                  _ <- symbol ":"
                  return (TileHeading ind)
                <|> do
                  pixels <- many dotOrHash
                  return (TileRow pixels)

-- End parser functions.

-- Used for the initial parsing.

data TileInfoParse = TileHeading TileID | TileRow [Bool] deriving Show

-- Holds tile data and other type definitions for this problem.

type TileID = Int

-- Holds a side signature, where bits in the Integer correspond to on pixels on the edge of a tile.
-- Bits are left to right and top to bottom.

type TileSideSig = Integer

-- The side of a tile as it would appear from above.

data TileSide = TopS | RightS | BottomS | LeftS deriving (Eq, Ord, Show, Enum, Bounded)

-- Defining the Ix instance allows the TileSide enumeration to be used as an array index.

instance IX.Ix TileSide where
  range (m, n) = [m..n]
  index b i | IX.inRange b i = IX.unsafeIndex b i
            | otherwise = error "Out of range indexing with TileSide"
  inRange (low, high) i = fromEnum i >= fromEnum low && fromEnum i <= fromEnum high
  unsafeIndex (low, _) i = fromEnum i - fromEnum low

-- A list of all of the sides of a tile.

allSides :: [TileSide]
allSides = [(minBound :: TileSide)..(maxBound :: TileSide)]

-- All possible orientations, rotated, once, twice, and three times, and the samed for flipped
-- first, side-to-side.

data TileOrientation = RCW0 | RCW1 | RCW2 | RCW3 | FRCW0 | FRCW1 | FRCW2 | FRCW3
                       deriving (Eq, Ord, Show, Enum, Bounded)

-- We want to be able to index an array using tile orientations, so we define the Ix class.

instance IX.Ix TileOrientation where
  range (m, n) = [m..n]
  index b i | IX.inRange b i = IX.unsafeIndex b i
            | otherwise = error "Out of range indexing with TileOrientation"
  inRange (low, high) i = fromEnum i >= fromEnum low && fromEnum i <= fromEnum high
  unsafeIndex (low, _) i = fromEnum i - fromEnum low

-- A list of all orientations.

allOrients :: [TileOrientation]
allOrients = [(minBound :: TileOrientation)..(maxBound :: TileOrientation)]

-- The side opposite the given side. For two tiles next to each other, these would be the connecting
-- sides.

matchingTileSide :: TileSide -> TileSide
matchingTileSide TopS    = BottomS
matchingTileSide RightS  = LeftS
matchingTileSide BottomS = TopS
matchingTileSide LeftS   = RightS

-- Show the given number in binary, which is useful for debugging.

numberInBinary :: (Show a, Integral a) => a -> String
numberInBinary n = showIntAtBase 2 intToDigit n ""

type PixelArray = UA.UArray (Int, Int) Bool

-- This record holds the data for a tile, including the ID, the contents of the time, and an array
-- of signatures indexed by the orientation and side.

data TileData = TileData { tileID    :: TileID
                         , tileArr   :: PixelArray
                         , tileSigsByOrient :: A.Array (TileOrientation, TileSide) TileSideSig
                         }

-- Show instance for tile data that is friendlier than standard show.

instance Show TileData where
  show (TileData tID tArr tSigsByOrient)
    = mconcat ["ID: ", show tID, "\n", convertedArr, "\n", convertedSigs, "\n"]
    where
      convertedArr = let tilePixList = sortBy (compare `on` (snd . fst)) (UA.assocs tArr)
                         nextPixelFn ((_, currCol), currPix) fn lastCol
                           | currCol == lastCol = oneOrZeroAndContinue
                           | otherwise = '\n' : ' ' : ' ' : oneOrZeroAndContinue
                           where
                             oneOrZeroAndContinue = currOneOrZero : fn currCol
                             currOneOrZero = if currPix then '1' else '0'
                     in  ' ' : ' ' : foldr nextPixelFn (const []) tilePixList 0
      convertedSigs = (intercalate "\n" . map genStr) allOrients
      genStr orient = mconcat ["    ", show orient, ": ", (intercalate ", " . map valInBin)
                                                            allSides]
        where
          valInBin side = numberInBinary $ tSigsByOrient A.! (orient, side)

-- Some additional types used here.

type TileAndOrient = (TileID, TileOrientation)
type TileMap = M.Map TileID TileData
type AvailableTiles = [TileID]

-- Holds a grid location.

type GridCoord = (Int, Int)

-- Holds the grid of placed tiles in a map, along with the maximum and minimum bounds.

data GridMap = GridMap { gridMap_r :: M.Map GridCoord TileAndOrient
                       , minX_r    :: Int
                       , maxX_r    :: Int
                       , minY_r    :: Int
                       , maxY_r    :: Int } deriving Show

-- Take in the data parsed from the input stream, and return a list of tiles.

buildTileSetsFromParseResults :: [TileInfoParse] -> [TileData]
buildTileSetsFromParseResults = btsfpr [] Nothing
  where
    btsfpr :: [[Bool]] -> Maybe TileID -> [TileInfoParse] -> [TileData]

    btsfpr pixelLists indexM []

      -- Here we had an empty input list.

      | isNothing indexM = []

      -- If there was no pixel information at the end, then it's an error.

      | null pixelLists = error "No data for last tile."

      -- We have seen the index and pixel data for the last tile in the list. Create it and return
      -- it as a singleton list.

      | otherwise = [genTile (fromJust indexM) pixelLists]

    btsfpr pixelLists indexM ((TileHeading ind) : remainingStream)

      -- These first two cases shouldn't happen and are error conditions.

      | null pixelLists && isJust indexM = error ("Empty data for tile " ++ show (fromJust indexM))
      | (not . null) pixelLists && isNothing indexM = error "Rows before tile index."

      -- Here we have seen the initial tile index, so save it and move on.

      | null pixelLists && isNothing indexM = btsfpr [] (Just ind) remainingStream

      -- We are at a tile index declaration and have accumulated the data for the prior tile. Create
      -- that tile object and move on.

      | otherwise = genTile (fromJust indexM) pixelLists : btsfpr [] (Just ind) remainingStream

    btsfpr pixelLists indexM ((TileRow row) : remainingStream)

      -- If we see row data and haven't seen a tile index for it, it's an error.

      | isNothing indexM = error "Row data before tile index in input."

      -- Save the current row data with the rest for this tile and move on.

      | otherwise = btsfpr (row : pixelLists) indexM remainingStream

    -- This is called when we have read in the tile ID, and have all of the boolean data for the
    -- contents of the tile. Generate the corresponding tile data structure.

    genTile :: TileID -> [[Bool]] -> TileData
    genTile ind pixelLists = TileData ind pixelArr signatureArray
      where
        pixelArr = UA.array ((0, 0), (maxArrInd, maxArrInd)) initList

        signatureArray = UA.array ((RCW0, TopS), (FRCW3, LeftS))
          (concat [genInitList RCW0  [topSig, rightSig, botSig, leftSig],
                   genInitList RCW1  [leftSigR, topSig, rightSigR, botSig],
                   genInitList RCW2  [botSigR, leftSigR, topSigR, rightSigR],
                   genInitList RCW3  [rightSig, botSigR, leftSig, topSigR],
                   genInitList FRCW0 [topSigR, leftSig, botSigR, rightSig],
                   genInitList FRCW1 [rightSigR, topSigR, leftSigR, botSigR],
                   genInitList FRCW2 [botSig, rightSigR, topSig, leftSigR],
                   genInitList FRCW3 [leftSig, botSig, rightSig, topSig]])
          where
            genInitList :: TileOrientation -> [TileSideSig]
                           -> [((TileOrientation, TileSide), Integer)]
            genInitList rotFlip = zip (zip (repeat rotFlip) allSides)
        maxArrInd = sideSize - 1
        sideSize = length pixelLists
        initList = (zip [(x, y) | y <- [0..maxArrInd], x <- [0..maxArrInd]] . concat . reverse)
                   pixelLists
        [topSig, rightSig, botSig, leftSig] = map listSigToInt basicSigs
        [topSigR, rightSigR, botSigR, leftSigR] = map listSigToInt basicRevSigs
        basicSigs :: [[Bool]]
        basicSigs = [[pixel (x, 0) | x <- fullRange], [pixel (maxArrInd, y) | y <- fullRange],
                     [pixel (x, maxArrInd) | x <- fullRange], [pixel (0, y) | y <- fullRange]]
          where
            fullRange = [0..maxArrInd]
            pixel :: (Int, Int) -> Bool
            pixel pair = pixelArr UA.! pair
        basicRevSigs = map reverse basicSigs
        listSigToInt :: [Bool] -> TileSideSig
        listSigToInt = foldl' addBit 0
          where
            addBit acc bt = let shifted = shiftL acc 1 in if bt then shifted .|. 0x1 else shifted

buildFullSignatureMap :: [TileData] -> SignatureMap
buildFullSignatureMap = foldl' addTileData M.empty
  where
    addTileData :: SignatureMap -> TileData -> SignatureMap
    addTileData sigMap tile = foldl' addSigData sigMap sigs
      where
        tileIdent = tileID tile
        tileSigArr = tileSigsByOrient tile
        sigs :: [((TileOrientation, TileSide), TileSideSig)]
        sigs = UA.assocs tileSigArr
        addSigData :: SignatureMap -> ((TileOrientation, TileSide), TileSideSig) -> SignatureMap
        addSigData currMap ((tileOrient, tileSide), sideSig)
          = M.insertWith prependOne (sideSig, tileSide) [(tileIdent, tileOrient)] currMap
          where

            -- Prepends the single element in the first list to the second list. because of the
            -- call, we know there is a single element in xs.

            prependOne xs acc = let x = head xs
                                in x `seq` (x : acc)

-- For a particular grid location, generate the list of locations next to it and the side of the
-- tile at that location that touches the (x, y) location.

genAdjacentLocsAndSides :: GridCoord -> [(GridCoord, TileSide)]
genAdjacentLocsAndSides (x, y) = [((x, y - 1), TopS), ((x + 1, y), LeftS), ((x, y + 1), BottomS),
                                   ((x - 1, y), RightS)]
genAdjacentLocs :: GridCoord -> [GridCoord]
genAdjacentLocs coord = map fst $ genAdjacentLocsAndSides coord

-- This set holds the grid coordinates that we need to investigate because they were next to a tile
-- added and empty.

type GridLocsToInvestigate = S.Set GridCoord
isEmptyGL :: GridLocsToInvestigate -> Bool
isEmptyGL = S.null
removeMin :: GridLocsToInvestigate -> (GridCoord, GridLocsToInvestigate)
removeMin = S.deleteFindMin

emptyGridMap :: GridMap
emptyGridMap = GridMap M.empty maxBound minBound maxBound minBound

isEmptyGM :: GridMap -> Bool
isEmptyGM (GridMap gridMap _ _ _ _) = M.null gridMap

addTileToGrid :: TileAndOrient -> GridCoord -> GridMap -> GridMap
addTileToGrid tileAndOrient coords@(x, y) (GridMap gridMap minX maxX minY maxY)
  = GridMap (M.insert coords tileAndOrient gridMap) (min x minX) (max x maxX) (min y minY) (max y maxY)

isEmptyAvailTiles :: AvailableTiles -> Bool
isEmptyAvailTiles [] = True
isEmptyAvailTiles _  = False

chooseOne :: AvailableTiles -> (TileID, AvailableTiles)
chooseOne [] = error "Can't chooseTile from empty tile set."
chooseOne (x : xs) = (x, xs)

removeOne :: TileID -> AvailableTiles -> AvailableTiles
removeOne = delete

type SignatureMap = M.Map (TileSideSig, TileSide) [(TileID, TileOrientation)]
removeTile :: TileID -> SignatureMap -> SignatureMap
removeTile tID = M.filter (not . null) . M.map (filter ((/= tID) . fst))

nextTileForGrid :: TileMap -> GridMap -> AvailableTiles -> SignatureMap -> GridLocsToInvestigate
                   -> GridMap
nextTileForGrid tileMap gridMap availableTiles sigMap gridLocsToInvestigate

  -- If we don't have any more tiles to place, or we don't have any more locations to investigate,
  -- then we are done.
  
  | isEmptyAvailTiles availableTiles = gridMap

  -- If we haven't placed any tiles yet, add one to location (0, 0) and note that we need to
  -- investigate all of the horizontal and vertical locations next to it.

  | isEmptyGM gridMap
    = let (tID, newAvailTiles) = chooseOne availableTiles
          newGridLocsToInvestigate = foldr S.insert gridLocsToInvestigate (genAdjacentLocs (0, 0))
          newSigMap = removeTile tID sigMap
          newGridMap = addTileToGrid (tID, RCW0) (0, 0) gridMap
      in  nextTileForGrid tileMap newGridMap newAvailTiles newSigMap newGridLocsToInvestigate

  -- I don't think this should happen in a non-error case if there are still available tiles.

  | isEmptyGL gridLocsToInvestigate = gridMap

  | null sigsToMatch = error (mconcat ["No sigs to match for ", show locToInvestigate])

  -- In this case we have investigated a location that had no matches and had one neighbor
  -- tile. Given the constraints for this problem, it must be an edge piece, so just move on.
    
  | tileAndOrients == [[]] = 
    nextTileForGrid tileMap gridMap availableTiles sigMap restToInvestigate

  -- If any of the matching tiles have other than one on their list, then it is an error.

  | any ((/= 1) . length) tileAndOrients = error "Conflicting or ambigious match."

  -- If the matches aren't all the same, then we also have a conflict.

  | foldr (\pair acc -> (pair /= firstTO) || acc) False restTO = error "Conflicing match"

  | otherwise = let newAvailTiles = removeOne tile availableTiles
                    adjacentLocs  = genAdjacentLocs locToInvestigate
                    newGridLocsToInvestigate = foldr insertIfNotInGrid restToInvestigate adjacentLocs
                    newSigMap = removeTile tile sigMap
                in  nextTileForGrid tileMap (addTileToGrid (tile, orient) locToInvestigate gridMap)
                      newAvailTiles newSigMap newGridLocsToInvestigate
  where

    insertIfNotInGrid :: GridCoord -> GridLocsToInvestigate -> GridLocsToInvestigate
    insertIfNotInGrid coord coordSet
      | M.member coord (gridMap_r gridMap) = coordSet
      | otherwise = S.insert coord coordSet

    -- These are the signatures of existing tiles adjacent to the location to investigate. This
    -- should never be empty because we only add locations that are next to an existing tile. If
    -- there is one tile in this list, then we may not find a match because it is an edge tile. If
    -- there are more than one tile on this list, then we have to find a tile that matches all of
    -- the appropriate signatures.
    -- The side is relative to the 

    sigsToMatch :: [(TileAndOrient, TileSide)]
    sigsToMatch = (map removeMaybe . filter inGrid . map findEntry)
                  (genAdjacentLocsAndSides locToInvestigate)
      where
        removeMaybe (entryM, side) = (fromJust entryM, side)
        findEntry (coord, side) = (M.lookup coord gm, side)
        inGrid (entryM, _) = isJust entryM
        gm = gridMap_r gridMap

    -- From the sigs to match, search for the corresponding tile and orientation. If there is a
    -- single one to search for, we may not find a matching signature, which means it was an edge
    -- location. If there are more than one signature to search for, they must all be found and must
    -- all match. The clean version is only generated after insuring that each list has just one
    -- element.

    (firstTO@(tile, orient) : restTO) = cleanTilesAndOrients
    cleanTilesAndOrients = map head tileAndOrients
    tileAndOrients = map searchForTileAndOrients sigsToMatch
      where
        searchForTileAndOrients :: (TileAndOrient, TileSide) -> [(TileID, TileOrientation)]
        searchForTileAndOrients ((tID, tileOrientation), tileSideOfSearched)
          | isNothing entryM = []
          | otherwise = fromJust entryM
          where
            entryM = M.lookup (searchSig, tileSideToPlace) sigMap
            searchSig = getSig tileMap tID tileOrientation tileSideOfSearched
            tileSideToPlace = matchingTileSide tileSideOfSearched
            
    -- Take one of the locations from the locations to investigate set, which we will work with
    -- here..

    (locToInvestigate, restToInvestigate) = removeMin gridLocsToInvestigate

getSig :: TileMap -> TileID -> TileOrientation -> TileSide -> TileSideSig
getSig tileMap tID tileOrientation tileSide
  | isNothing tileDataM = error ("Tile lookup of " ++ show tID ++ " not found.")
  | otherwise = tileSigsArr A.! (tileOrientation, tileSide)
  where
    tileSigsArr = (tileSigsByOrient . fromJust) tileDataM
    tileDataM = M.lookup tID tileMap

getAndArrangeProb20Data :: String -> IO (TileMap, GridMap)
getAndArrangeProb20Data inputFile = do

  -- Read the input and put into a list of parsed objects, either tile headers or rows.

  parseResults <- fmap (map (parse parseFile20) . filter (not . null) . lines)
                       (readFile inputFile)

  when (badParseOfInput parseResults)
       (ioError $ userError "Parse error in input for puzzle 20.")

  -- Convert the parse results into a list of tiles, each of which holds a list of tiles in all
  -- orientations. Note that while we use head here, we are guaranteed to have one valid parse
  -- due to the badParseOfInput check above.

  let tiles = buildTileSetsFromParseResults (map (fst . head) parseResults)
      tileMap = foldl' (\acc x -> M.insert (tileID x) x acc) M.empty tiles
      sigMap = buildFullSignatureMap tiles
      availTiles = map tileID tiles
      gridMap = nextTileForGrid tileMap emptyGridMap availTiles sigMap S.empty

  return (tileMap, gridMap)

-- This was a long one! Nothing too challenging, but a lot of detail work that was easy to make
-- mistakes in.

puzzle_20a :: IO Integer
puzzle_20a = do

  -- Use common function to read in the tile data and build the correct grid.

  (_, gridMap) <- getAndArrangeProb20Data "puzzle_20.inp"

  let (GridMap gm minx maxx miny maxy) = gridMap
      foundCornersM = map (flip M.lookup gm)
                          [(minx, miny), (minx, maxy), (maxx, miny), (maxx, maxy)]
      cornerIDs = map (fromIntegral . fst . fromJust) foundCornersM

  when (any isNothing foundCornersM)
       (ioError $ userError "Not all four corners valid in puzzle 20a.")

  return (product cornerIDs)

-- Generate the list of indicies for the elements of a tile given the orientation and the maximum
-- bounds of the tile. These are generated from the upper left corner in rows down to the lower
-- right corner. Note that the upper left corner is actually (0, 0).

genTileIndicesForOrientation :: TileOrientation -> GridCoord -> [GridCoord]
genTileIndicesForOrientation orient (maxX, maxY) = listOfCoords
  where
    listOfCoords = case orient of
      RCW0  -> [(x, y) | y <- fwdYRange,  x <- fwdXRange]
      RCW1  -> [(x, y) | x <- fwdXRange,  y <- bkwdYRange]
      RCW2  -> [(x, y) | y <- bkwdYRange, x <- bkwdXRange]
      RCW3  -> [(x, y) | x <- bkwdXRange, y <- fwdYRange]

      FRCW0 -> [(x, y) | y <- fwdYRange,  x <- bkwdXRange]
      FRCW1 -> [(x, y) | x <- bkwdXRange, y <- bkwdYRange]
      FRCW2 -> [(x, y) | y <- bkwdYRange, x <- fwdXRange]
      FRCW3 -> [(x, y) | x <- fwdXRange,  y <- fwdYRange]

    (maxXm1, maxYm1) = (maxX - 1, maxY - 1)
    (maxXm2, maxYm2) = (maxXm1 - 1, maxYm1 - 1)
    fwdXRange  = [1..maxXm1]
    bkwdXRange = [maxXm1, maxXm2..1]
    fwdYRange  = [1..maxYm1]
    bkwdYRange = [maxYm1, maxYm2..1]

-- Assemble the tiles, given their orientation and location in a larger grid, into a single pixel
-- array, erasing one edge of the boundaries between tiles.

assembleTiles :: TileMap -> GridMap -> PixelArray
assembleTiles tileMap (GridMap gridMap minX maxX minY maxY) = resultArr
  where

    -- Create a new array large enough for all tiles.

    resultArr = UA.array ((0, 0), pixArrUpperBound) initElements

    -- Generate both source and destination indices for the pixels in each tile, based on its
    -- location in the broader grid and its orientation.

    initElements = M.foldrWithKey genTilesPixels [] gridMap

    -- Given the size of each tile, and the number of tiles horizontally and vertically, compute the
    -- maximum bound of the full pixel array. Note that we multiply by the max x and y indexes of a
    -- tile even though the indices begin at 0. This is because we are going to erase an edge of
    -- each tile because of the duplicate lines used to stitch together the tiles.

    pixArrUpperBound = ((maxX - minX + 1) * (trimmedTileMaxX + 1) - 1,
                        (maxY - minY + 1) * (trimmedTileMaxY + 1) - 1)

    -- Determine the maximum array index for a single tile, and assume that all tiles are the same size.

    tileMaxBound@(tileMaxX, tileMaxY) = (snd . UA.bounds . tileArr . snd . M.elemAt 0) tileMap

    -- Maximu bound of trimmed tiles.

    trimmedTileMaxBound@(trimmedTileMaxX, trimmedTileMaxY) = (tileMaxX - 2, tileMaxY - 2)

    -- Accumulate a list of the grid coordinates (for the full array) and corresponding boolean
    -- values.

    genTilesPixels :: GridCoord -> TileAndOrient -> [(GridCoord, Bool)] -> [(GridCoord, Bool)]
    genTilesPixels (tileX, tileY) (tID, tileOrient) acc = filtAndAdjTilePixels ++ acc
      where

        -- Need to flip and rotate tile first... Do this with allTilePixels.

        -- Before adding the elements of this tile to the list, we need to filter out the lines that
        -- would be included in another (the stitch lines), and adjust them to be at the right place
        -- in the larger pixel field.

        filtAndAdjTilePixels = map adjCoord allTilePixels

        -- Here is a list of all of the coordinates and associated values of the tile array.

        allTilePixels = UA.assocs tileDataFlipRot
        tileDataFlipRot = flipRotArr tileOrient ((tileArr . fromJust . M.lookup tID) tileMap)

        -- The adjustment value based on where the tile falls in the full pixel array.

        (adjX, adjY) = ((tileX - minX) * (trimmedTileMaxX + 1), (maxY - tileY) * (trimmedTileMaxY + 1))

        -- Adjust the coordinates from tile coordinates to full-pixel array coordinates.

        adjCoord ((x, y), val) = ((x + adjX, y + adjY), val)

        -- Given the current tile array as read in, flip and rotate it based on the tile orientation
        -- so that it is in that state.

        flipRotArr :: TileOrientation -> PixelArray -> PixelArray
        flipRotArr orient currArray = UA.array ((0, 0), trimmedTileMaxBound) newArrayInitList
          where
            newArrayInitList = zipWith (getElement currArray) newArrayIndexList fromArrayIndexList
            newArrayIndexList = [(x, y) | y <- [0..trimmedTileMaxX], x <- [0..trimmedTileMaxY]]

            -- This is the list of coordinates in the order needed, so that when placed in the
            -- normal order, they create the array in the right way given the orientation.

            fromArrayIndexList = genTileIndicesForOrientation orient tileMaxBound

            -- Get the element in the current array based on the second coordinate, and associate
            -- that data with the first coordinate.

            getElement :: PixelArray -> GridCoord -> GridCoord -> (GridCoord, Bool)
            getElement arr newCoord currCoord = (newCoord, arr UA.! currCoord)

-- The serpent pattern as given in the problem. It also needs to be rotated and flipped 7 other ways
-- to find all of them.  The first pair of pairs defines a box around the starting point that needs
-- to be in range to be able to search for the pattern at all. The list of pairs are increments from
-- the starting location to check. If all are true, then the serpent pattern has been found. The (0,
-- 0) at the beginning is to check for the starting location..

type SerpPat = [(Int, Int)]
type SerpPatInst = (((Int, Int), (Int, Int)), [(Int, Int)])

-- These are the jumps starting from the tail to visit all elements of the serpent pattern.

serpPat :: SerpPat
serpPat = [(1, 1), (3, 0), (1, -1), (1, 0), (1, 1), (3, 0), (1, -1), (1, 0), (1, 1), (3, 0),
           (1, -1), (1, -1), (0, 1), (1, 0)]

serpPatterns :: [SerpPatInst]
serpPatterns = map genSerpBoundary (fourLeftAndRight ++ map flipXY fourLeftAndRight)
  where
    twoPointedRight  = [serpPat, flipTB serpPat]
    fourLeftAndRight = twoPointedRight ++ map flipLR twoPointedRight

    flipTB :: SerpPat -> SerpPat
    flipTB = map flipY

    flipLR :: SerpPat -> SerpPat
    flipLR = map flipX

    flipXY :: SerpPat -> SerpPat
    flipXY = map switchXY

    flipY :: (Int, Int) -> (Int, Int)
    flipY (x, y) = (x, -y)

    flipX :: (Int, Int) -> (Int, Int)
    flipX (x, y) = (-x, y)

    switchXY :: (Int, Int) -> (Int, Int)
    switchXY (x, y) = (y, x)

-- Given the serpent pattern from a starting point, generate the boundary box for the pattern.

genSerpBoundary :: SerpPat -> SerpPatInst
genSerpBoundary pat = (((minX, minY), (maxX, maxY)), pat)
  where
    locations = genPatternLocs (0, 0) pat
    minX = (minimum . map fst) locations
    maxX = (maximum . map fst) locations
    minY = (minimum . map snd) locations
    maxY = (maximum . map snd) locations

-- Given a SerpPat and a location, translate the elements to be relative to the location.

genPatternLocs :: (Int, Int) -> SerpPat -> SerpPat
genPatternLocs = scanl addPair
  where
    addPair (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)
    
countNonSerpentPixels :: PixelArray -> Int
countNonSerpentPixels imageArr = (length . filter id . UA.elems) deSerpentedArray
  where

    -- Remove any pixels that are a part of a serpent.

    deSerpentedArray = imageArr UA.// zip serpLocs (repeat False)

    -- We take all of the indices that are part of a found serpent in the image, and we remove any
    -- duplicates because in the Haskell 2010 spec, resetting the same element more than once in an
    -- update is undefined (although the implementation uses the last one).

    serpLocs = (map head . group . sort . concatMap serpentOrigins . UA.indices) imageArr
    ((minX, minY), (maxX, maxY)) = UA.bounds imageArr

    -- Returns all pattern indices found from this base location.

    serpentOrigins :: (Int, Int) -> [(Int, Int)]
    serpentOrigins (x, y) = (concatMap snd . filter fst . map thisPatternHere) serpPatterns
      where
        thisPatternHere :: SerpPatInst -> (Bool, SerpPat)
        thisPatternHere (((x1, y1), (x2, y2)), zs) = (inRangeAndFound, sPat)
          where

            -- Determine if the pattern would fit in the bounds of the current image array, and if
            -- so, if all pattern points are True.

            inRangeAndFound = inArrRange (x + x1, y + y1) && inArrRange (x + x2, y + y2)
                              && all (imageArr UA.!) sPat

            -- The pattern indices based on the current (x, y) location.

            sPat = genPatternLocs (x, y) zs

        inArrRange (x1, y1) = x1 >= minX && x1 <= maxX && y1 >= minY && y1 <= maxY

puzzle_20b :: IO Int
puzzle_20b = do

  -- Use common function to read in the tile data and build the correct grid.

  (tileMap, gridMap) <- getAndArrangeProb20Data "puzzle_20.inp"

  when (M.null tileMap)
       (ioError $ userError "Empty tile map in puzzle 20b.")

  let entireImage         = assembleTiles tileMap gridMap
      nonSerpentOnPixels  = countNonSerpentPixels entireImage

  return nonSerpentOnPixels

-- Initially hold each recipe as a list of ingredients and a list of allergens.

type Recipe21 = ([String], [String])
type IngredientMap = M.Map String Int
type AllergenMap = M.Map String (S.Set String)

parse21Recipe :: Parser Recipe21
parse21Recipe = do
  ingredients <- some identifier
  _ <- symbol "("
  _ <- symbol "contains"
  allergens <- cslOfIdents
  _ <- symbol ")"
  return (ingredients, allergens)

genProcessedPuzzle21Data :: IO (IngredientMap, [(String, String)])
genProcessedPuzzle21Data = do

  parseResults <- fmap (map (parse parse21Recipe) . lines) (readFile "puzzle_21.inp")

  -- Check for ambigious parsing or errors in parsing.

  when (badParseOfInput parseResults)
       (ioError $ userError "Parse error in input for puzzle 21.")

  let recipes = map (fst . head) parseResults

      -- Here we have a map of all of the ingredients along with the number of times they occur in
      -- the recipes as a whole, and a map of allergens to the set of possible ingredients they
      -- could be in. These sets associated with the allergens have been already cut down
      -- significantly by taking the intersection of the associated ingredients each time an
      -- allergen is listed.

      (ingredientMap, allergenMap) = foldl' processRecipe (M.empty, M.empty) recipes

      -- Here we have the final set of (allergen, ingredient) pairs along with any remaining
      -- allergens and the set of possible ingredients they might be in (zero of these in these
      -- puzzles).

      (allergensAndIngredients, remainingAllergens)
        = (doneOrNoChange . tail . iterate findSingleAllergens) ([], 0, M.toList allergenMap)

  -- Check that we narrowed down all allergens to a single ingredient.

  unless (null remainingAllergens)
       (ioError $ userError "Either no answer or multiple to 21.")

  return(ingredientMap, allergensAndIngredients)

  where

    -- Keep walking down the list until the number of identified allergen/ingredient pairs
    -- identified in the last iteration is zero or until there are no more allergens left.

    doneOrNoChange :: [([(String, String)], Int, [(String, S.Set String)])] -> ([(String, String)], [(String, S.Set String)])
    doneOrNoChange [] = ([], [])
    doneOrNoChange ((ais, cnt, currAllergens) : rest)
      | cnt == 0 || null currAllergens = (ais, currAllergens)
      | otherwise = doneOrNoChange rest

    -- Move any allergens associated with just a single ingredient to the allergen/ingredient list,
    -- and remove that ingredient from any remaining allergen's ingredient sets.

    findSingleAllergens :: ([(String, String)], Int, [(String, S.Set String)])
                        -> ([(String, String)], Int, [(String, S.Set String)])
    findSingleAllergens (currFound, _, currAllSets)
      = (currFound ++ newSingles, length newSingles, newAllSets)
      where
        newAllSets = map removeNewIngredients stillSets
        (newSingles, stillSets) = foldr setOrSingle ([], []) currAllSets
        setOrSingle :: (String, S.Set String) -> ([(String, String)], [(String, S.Set String)])
                       -> ([(String, String)], [(String, S.Set String)])
        setOrSingle (allerg, ingrSet) (accSingle, accSet)
          | S.size ingrSet == 1 = ((allerg, S.elemAt 0 ingrSet) : accSingle, accSet)
          | otherwise = (accSingle, (allerg, ingrSet) : accSet)
        removeNewIngredients :: (String, S.Set String) -> (String, S.Set String)
        removeNewIngredients (allerg, ingrSet) = (allerg, foldr (S.delete . snd) ingrSet newSingles)

    -- Given a recipe, add the ingredients and associated allergens to the accumulating maps.

    processRecipe :: (IngredientMap, AllergenMap) -> Recipe21 -> (IngredientMap, AllergenMap)
    processRecipe (accIngrMap, accAllergMap) (ingredients, allergens)
      = newIngrMap `seq` newAllergMap `seq` (newIngrMap, newAllergMap)
      where
        newIngrMap   = M.unionWith (+) accIngrMap currIngrMap
        currIngrMap  = foldl' (\accMap ingr -> M.insertWith (+) ingr 1 accMap) M.empty ingredients
        currIngrSet  = S.fromList ((map fst . M.toList) currIngrMap)
        newAllergMap = foldl' intersectSets accAllergMap allergens
        intersectSets accSet allergen = M.insertWith S.intersection allergen currIngrSet accSet

puzzle_21a :: IO Int
puzzle_21a = do

  (ingredientMap, allergensAndIngredients) <- genProcessedPuzzle21Data

  let mapOfGoodIngredients = foldl' (flip M.delete) ingredientMap (map snd allergensAndIngredients)
      count = M.foldl' (+) 0 mapOfGoodIngredients

  return count

puzzle_21b :: IO String
puzzle_21b = do

  (_, allergensAndIngredients) <- genProcessedPuzzle21Data

  let result = (intercalate "," . map snd . sort) allergensAndIngredients

  return result

-- Convert the lists of strings to ints, and remove empty strings, and there will be one at the
-- start of the second deck.

p22ConvStrsToDecks :: ([String], [String]) -> ([Int], [Int])
p22ConvStrsToDecks (xs, ys) = (convAndRemNull xs, convAndRemNull ys)
  where
    convAndRemNull :: [String] -> [Int]
    convAndRemNull = map read . filter (/= [])

-- Given a final position, compute the score to return.

p22ComputeScore :: [Int] -> Int
p22ComputeScore = sum . zipWith (*) [1..] . reverse

puzzle_22a :: IO Int
puzzle_22a = do

--  initialDecks :: ([Int], [Int])
  initialDecks <- fmap (p22ConvStrsToDecks . span (/= []) . filter ((/= "Player") . take 6)
                        . lines) (readFile "puzzle_22.inp")

  let (finalP1Deck, finalP2Deck) = (head . dropWhile (\(xs, ys) -> not (null xs || null ys))
                                    . iterate playOneRound) initialDecks
      result = p22ComputeScore (if null finalP1Deck then finalP2Deck else finalP1Deck)

  return result

  where

    -- Play one round of the game.

    playOneRound :: ([Int], [Int]) -> ([Int], [Int])
    playOneRound ([], _) = ([], [])
    playOneRound (_, []) = ([], [])
    playOneRound (x : xs, y : ys)
      | x > y = (xs ++ [x, y], ys)
      | otherwise = (xs, ys ++ [y, x])

-- Holds the game state for 22b.

data P22GameState = P22GameState { deck1_r  :: [Int]
                                 , count1_r :: Int
                                 , deck2_r  :: [Int]
                                 , count2_r :: Int
                                 } deriving Show

p22GameStateFromDecks :: [Int] -> [Int] -> P22GameState
p22GameStateFromDecks deck1 deck2 = P22GameState deck1 (length deck1) deck2 (length deck2)

data P22Player = Player1 | Player2 deriving (Eq, Show)
                                                           
puzzle_22b :: IO Int
puzzle_22b = do

  (deck1, deck2) <- fmap (p22ConvStrsToDecks . span (/= []) . filter ((/= "Player") . take 6)
                          . lines) (readFile "puzzle_22.inp")

  let initialGameState = p22GameStateFromDecks deck1 deck2
      (_, score)  = playRecursiveCombat S.empty initialGameState

  return score

  where

    playRecursiveCombat :: S.Set ([Int], [Int]) -> P22GameState -> (P22Player, Int)
    playRecursiveCombat priorStates (P22GameState deck1 count1 deck2 count2)
      | S.member twoDecks priorStates = (Player1, p22ComputeScore deck1)
      | count1 == 0 = (Player2, p22ComputeScore deck2)
      | count2 == 0 = (Player1, p22ComputeScore deck1)
      | card1 >= count1 || card2 >= count2
        = continueWithWin (if card1 > card2 then Player1 else Player2)
      | otherwise = continueWithWin resultFromRecursiveCombat
      where
        (card1 : remainDeck1) = deck1
        (card2 : remainDeck2) = deck2
        twoDecks = (deck1, deck2)

        -- Continue playing after a win of this hand by the given player.

        continueWithWin :: P22Player -> (P22Player, Int)
        continueWithWin currWinner = playRecursiveCombat newPriorStates newGameState
          where
            newPriorStates = S.insert twoDecks priorStates
            newGameState
              | currWinner == Player1
                = P22GameState (remainDeck1 ++ [card1, card2]) (count1 + 1) remainDeck2 (count2 - 1)
              | otherwise
                = P22GameState remainDeck1 (count1 - 1) (remainDeck2 ++ [card2, card1]) (count2 + 1)

        -- The result from a recursive game. Here we don't care about the score, just who won.

        (resultFromRecursiveCombat, _) = playRecursiveCombat S.empty recursiveGameStart
          where
            recursiveGameStart = p22GameStateFromDecks rDeck1 rDeck2
            rDeck1 = take card1 remainDeck1
            rDeck2 = take card2 remainDeck2

puzzle_23a :: IO Int
puzzle_23a = do
  initStr <- readFile "puzzle_23.inp"

  let initialIntList = map digitToInt initStr
      listLen = length initialIntList
      maxVal = maximum initialIntList
      resultListA = iterate (makeOneMove maxVal) initialIntList !! steps
      adjResultListA = (take (listLen - 1) . drop 1 . dropWhile (/= 1))
                       (resultListA ++ resultListA)
      resultA = foldl' (\acc d -> acc * 10 + d) 0 adjResultListA
                        
  return resultA

  where

    steps :: Int
    steps = 100

    makeOneMove :: Int -> [Int] -> [Int]
    makeOneMove _ [] = []
    makeOneMove maxVal (x : xs) = upToDest ++ [y] ++ removedChunk ++ ys ++ [x]
      where
        (upToDest, y : ys) = span (/= destCup) remainingChunk
        destCup = (head . filter (not . flip elem removedChunk) . drop 1 . iterate nextTry) x
        (removedChunk, remainingChunk) = splitAt 3 xs
        nextTry z
          | z == 1 = maxVal
          | otherwise = z - 1

-- This is a rare instance where using monadic imperative code is necessary to have reasonable
-- performance. The best I could due with purlely functional. code was for it to run in about 50
-- seconds, and this runs in a half a second.
-- The idea is to use a mutable vector to model the circular list indicated in the problem. For each
-- index, the contents of that vector location represents the next cup number in the list.

puzzle_23b :: IO Int64
puzzle_23b = do
  initStr <- readFile "puzzle_23.inp"

  let
      -- The maximum value in the sequence.

      maxVal :: Int
      maxVal = 1000000

      -- The number of moves to make.

      steps :: Int
      steps = 10000000

      readIntList    = map digitToInt initStr
      first          = head readIntList
      firstAfter     = maximum readIntList + 1
      initialization = (maxVal, first) : zip readIntList (drop 1 readIntList ++ [firstAfter])

  (fstAft, sndAft) <- do

    -- Create a mutable vector and fill it up with the initial state. We are modeling a circular
    -- list where each element of the vector is the one following the index. For example, in a
    -- smaller case, only 3 long, if the digits are 3,1,2, then the vector will hold: [(0,?), (1,
    -- 2), (2, 3), (3, 1)].

    v <- UVM.new (maxVal + 1)

    -- We initialize the vector in two pieces. First, there is the section in the front with the
    -- read-in sequence along with the last element that points back at the first. Then initialize
    -- all the ones inbetween which start out with each number n followed by (n + 1).

    mapM_ (uncurry (UVM.write v))  initialization
    mapM_ (\g -> UVM.write v g (g + 1)) [firstAfter..(maxVal - 1)]
    
    let
      makeOneMove currCup _ = do

        -- Get the three cups that will move, which are the three directly after the currCup.

        firstInChunk  <- UVM.read v currCup
        secondInChunk <- UVM.read v firstInChunk
        thirdInChunk  <- UVM.read v secondInChunk

        -- The fourth after currCup will be what currCup points to after the move, and it will also
        -- be the next currCup to return as the accumulator.

        newCup      <- UVM.read v thirdInChunk

        -- Figure out the destination cup and the cup after it, between which we will splice in the
        -- three moving cups.

        let destCup = (head . filter filtFn . drop 1 . iterate nextTry) currCup
            nextTry z
              | z == 1 = maxVal
              | otherwise = z - 1
            filtFn z = z /= firstInChunk && z /= secondInChunk && z /= thirdInChunk
        afterDest <- UVM.read v destCup

        -- Now hook up the links needed to put everything back together with the three cups moved.

        UVM.write v currCup newCup
        UVM.write v destCup firstInChunk
        UVM.write v thirdInChunk afterDest

        return newCup

    -- Make all of the individual moves, mutating the vector for each one, and the current cup at
    -- each point is kept in the accumulator.

    foldM_  makeOneMove first [1..steps]

    m <- UVM.read v 1
    n <- UVM.read v m

    return (m, n)

  let result = fromIntegral fstAft * fromIntegral sndAft
  return result

data P24Direction = East | Southeast | Southwest | West | Northwest | Northeast deriving (Show, Eq, Ord, Enum, Bounded)
type P24HexCoord = (Int, Int)
type P24TileState = S.Set P24HexCoord
type P24NeighborCount = M.Map P24HexCoord Int

-- Define the Ix instance to allow the P24Direction enumeration to be used as an array index.

instance IX.Ix P24Direction where
  range (m, n) = [m..n]
  index b i | IX.inRange b i = IX.unsafeIndex b i
            | otherwise = error "Out of range indexing with P24Direction"
  inRange (low, high) i  = fromEnum i >= fromEnum low && fromEnum i <= fromEnum high
  unsafeIndex (low, _) i = fromEnum i - fromEnum low

parse24HexDirs :: Parser [P24Direction]
parse24HexDirs = do many direction
  where
    direction :: Parser P24Direction
    direction = do
        _ <- symbol "e"
        return East
      <|> do
        _ <- symbol "se"
        return Southeast
      <|> do
        _ <- symbol "sw"
        return Southwest
      <|> do
        _ <- symbol "w"
        return West
      <|> do
        _ <- symbol "nw"
        return Northwest
      <|> do
        _ <- symbol "ne"
        return Northeast

-- The change to make to the location in the two-dimensional array for each move direction.

p24DirIncArr :: A.Array P24Direction P24HexCoord
p24DirIncArr = A.array (minBound, maxBound) [(East, (2, 0)), (Southeast, (1, -1)), (Southwest, (-1, -1)),
                                             (West, (-2, 0)), (Northwest, (-1, 1)), (Northeast, (1, 1))]

-- Add in an increment pair to the given coord.

p24AddIncPair :: P24HexCoord -> P24HexCoord -> P24HexCoord
p24AddIncPair (x, y) (xInc, yInc) = let newX = x + xInc
                                        newY = newX `seq` y + yInc
                                    in newY `seq` (newX, newY)

-- Take one step in the path depending on the direction given.

p24StepPath :: P24HexCoord -> P24Direction -> P24HexCoord
p24StepPath coord dir = p24AddIncPair coord (p24DirIncArr A.! dir)

-- Insert or remove this coordinate from the set depending on whether it is there or not.

p24InsertOrRemove :: P24TileState -> P24HexCoord -> P24TileState
p24InsertOrRemove currSet coord
  | S.member coord currSet = S.delete coord currSet
  | otherwise = S.insert coord currSet

puzzle_24a :: IO Int
puzzle_24a = do
  parseResults <- fmap (map (parse parse24HexDirs) . lines) (readFile "puzzle_24.inp")

  -- Check for ambigious parsing or errors in parsing.

  when (badParseOfInput parseResults)
       (ioError $ userError "Parse error in input for puzzle 24a.")

  let paths = map (fst . head) parseResults
      blackHexes = (foldl' p24InsertOrRemove S.empty . map (foldl' p24StepPath (0, 0))) paths

  return (S.size blackHexes)

puzzle_24b :: IO Int
puzzle_24b = do
  parseResults <- fmap (map (parse parse24HexDirs) . lines) (readFile "puzzle_24.inp")

  -- Check for ambigious parsing or errors in parsing.

  when (badParseOfInput parseResults)
       (ioError $ userError "Parse error in input for puzzle 24b.")

  let paths = map (fst . head) parseResults
      blackHexes = (foldl' p24InsertOrRemove S.empty . map (foldl' p24StepPath (0, 0))) paths
      seriesOfStates = iterate stepTileFloorOneDay blackHexes

  return (S.size $ seriesOfStates !! 100)

  where

    stepTileFloorOneDay :: P24TileState -> P24TileState
    stepTileFloorOneDay currTileState = newTileState
      where
        newTileState = M.foldlWithKey addIfShouldBeBlackTile S.empty newTileCounts
        newTileCounts = S.foldl' noteNeighbors M.empty currTileState

        -- Increment a map counter for all hexes surrounding the given black one.

        noteNeighbors :: P24NeighborCount -> P24HexCoord -> P24NeighborCount
        noteNeighbors currMap coord = newMap
          where
            newMap = (foldl' (\accM pr -> M.insertWith (+) pr 1 accM) currMap
                      . map (p24AddIncPair coord)) (A.elems p24DirIncArr)

        -- Check the current tile with count of black tiles around it, and decide if it should be
        -- black in the next step.

        addIfShouldBeBlackTile :: P24TileState -> P24HexCoord -> Int -> P24TileState
        addIfShouldBeBlackTile accSet coord neighborCount
          | neighborCount > 2 = accSet
          | neighborCount == 2 = S.insert coord accSet
          | S.member coord currTileState = S.insert coord accSet
          | otherwise = accSet

puzzle_25a :: IO Int64
puzzle_25a = do
  [pubKey1, pubKey2] <- fmap (map (read :: (String -> Int64)) . words) (readFile "puzzle_25.inp")

  let loopSize2 = (fromJust . elemIndex pubKey2) (iterate (loopFn 7) 1)
      encrKey  = iterate (loopFn pubKey1) 1 !! loopSize2

  return encrKey

  where

    loopFn :: Int64 -> Int64 -> Int64
    loopFn subjNumber currVal = currVal * subjNumber `rem` 20201227


main :: IO ()
main = do

  startTime <- getTime Realtime

  -- Generate the results for each problem and check for the expected answer. The result will
  -- contain not only the result, but the time taken to compute it.

  computeCheckAndPrint  puzzle_01a " 1a" 997899
  computeCheckAndPrint  puzzle_01b " 1b" 131248694
  computeCheckAndPrint  puzzle_02a " 2a" 636
  computeCheckAndPrint  puzzle_02b " 2b" 588
  computeCheckAndPrint  puzzle_03a " 3a" 299
  computeCheckAndPrint  puzzle_03b " 3b" 3621285278
  computeCheckAndPrint  puzzle_04a " 4a" 242
  computeCheckAndPrint  puzzle_04b " 4b" 186
  computeCheckAndPrint  puzzle_05a " 5a" 861
  computeCheckAndPrint  puzzle_05b " 5b" 633
  computeCheckAndPrint  puzzle_06a " 6a" 6443
  computeCheckAndPrint  puzzle_06b " 6b" 3232
  computeCheckAndPrint  puzzle_07a " 7a" 238
  computeCheckAndPrint  puzzle_07b " 7b" 82930
  computeCheckAndPrint  puzzle_08a " 8a" 1262
  computeCheckAndPrint  puzzle_08b " 8b" 1643
  computeCheckAndPrint  puzzle_09a " 9a" 731031916
  computeCheckAndPrint  puzzle_09b " 9b" 93396727
  computeCheckAndPrint  puzzle_10a "10a" 2040
  computeCheckAndPrint  puzzle_10b "10b" 28346956187648
  computeCheckAndPrint  puzzle_11a "11a" 2254
  computeCheckAndPrint  puzzle_11b "11b" 2004
  computeCheckAndPrint  puzzle_12a "12a" 1589
  computeCheckAndPrint  puzzle_12b "12b" 23960
  computeCheckAndPrint  puzzle_13a "13a" 2045
  computeCheckAndPrint  puzzle_13b "13b" 402251700208309
  computeCheckAndPrint  puzzle_14a "14a" 16003257187056
  computeCheckAndPrint  puzzle_14b "14b" 3219837697833
  computeCheckAndPrint  puzzle_15a "15a" 706
  computeCheckAndPrint  puzzle_15b "15b" 19331
  computeCheckAndPrint  puzzle_16a "16a" 21996
  computeCheckAndPrint  puzzle_16b "16b" 650080463519
  computeCheckAndPrint  puzzle_17a "17a" 338
  computeCheckAndPrint  puzzle_17b "17b" 2440
  computeCheckAndPrint  puzzle_18a "18a" 7293529867931
  computeCheckAndPrint  puzzle_18b "18b" 60807587180737
  computeCheckAndPrint  puzzle_19a "19a" 173
  computeCheckAndPrint  puzzle_19b "19b" 367
  computeCheckAndPrint  puzzle_20a "20a" 11788777383197
  computeCheckAndPrint  puzzle_20b "20b" 2242
  computeCheckAndPrint  puzzle_21a "21a" 2493
  computeCheckAndPrintS puzzle_21b "21b" "kqv,jxx,zzt,dklgl,pmvfzk,tsnkknk,qdlpbt,tlgrhdh"
  computeCheckAndPrint  puzzle_22a "22a" 32472
  computeCheckAndPrint  puzzle_22b "22b" 36463
  computeCheckAndPrint  puzzle_23a "23a" 28946753
  computeCheckAndPrint  puzzle_23b "23b" 519044017360
  computeCheckAndPrint  puzzle_24a "24a" 469
  computeCheckAndPrint  puzzle_24b "24b" 4353
  computeCheckAndPrint  puzzle_25a "25a" 19414467

  -- Report on the time taken by all of the solutions together.

  endTime <- getTime Realtime
  let diff = computeElapsedTime startTime endTime
      diffStr = printf "%0.5f sec" diff

  putStrLn $ mconcat ["\nTotal time for all solutions: ", diffStr]
