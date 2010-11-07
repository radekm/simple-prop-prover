-- |
-- Module    : Main
-- Copyright : (c) Radek Micek 2010
-- License   : BSD3
-- Stability : experimental
--
-- Generates formulas representing pigeonhole principle.
import Control.Applicative ((<$>))
import Data.Maybe
import Data.List
import System.Environment

-- Total number of holes.
type HolesCnt = Int

type Clause = String

-- Returns variable name for proposition "pigeon p is in hole h".
pl :: Int -> Int -> String
pl p h = "p[" ++ show p ++ "," ++ show h ++ "]"

-- Generated clause assures that pigeon p is in some hole.
--
-- Call this for each pigeon.
pigeonIsInHole :: Int -> HolesCnt -> Clause
pigeonIsInHole p n = intercalate "+" [pl p hole | hole <- [1..n]]

-- Assures that hole h is inhabited by no more than one pigeon.
--
-- Call this for each hole.
atMostOnePigeonInHole :: Int -> HolesCnt -> [Clause]
atMostOnePigeonInHole h n =
    ['~':pl p h ++ "+" ++ '~':pl p' h | p <- [1..(n+1)], p' <- [(p+1)..(n+1)]]

-- Generates CNF formula for pigeonhole principle
php :: HolesCnt -> String
php n = concatMap (\cl -> '(':cl ++ ")") clauses
  where
      clauses = [pigeonIsInHole p n | p <- [1..(n+1)]] ++
                concat [atMostOnePigeonInHole h n | h <- [1..n]]

main :: IO ()
main = do
    nHolesArg <- listToMaybe <$> getArgs
    prog      <- getProgName

    case nHolesArg of
        Nothing     -> putStrLn $ usage prog
        Just nHoles -> putStrLn $ php $ read nHoles
  where
      usage p = intercalate "\n"
          [ "Usage: " ++ p ++ " NUM-OF-PIGEONHOLES"
          , "Returns CNF formula which represents pigeonhole principle."
          , "Variable p[i,j] in the formula represents proposition"
          , "that pigeon i is in pigeonhole j." ]

