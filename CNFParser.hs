-- |
-- Module    : CNFParser
-- Copyright : (c) Radek Micek 2010
-- License   : BSD3
-- Stability : experimental
--
-- Parser for formulas in CNF.
module CNFParser where

import Data.List (nub)
import Control.Applicative ((<$>), (<*>), (*>), (<*), pure)
import Text.Parsec hiding (State)

type VarName = String

-- Variable name and flag whether literal is positive.
type StrLit = (VarName, Bool)

newtype StrClause = StrClause { scLits :: [StrLit] }
    deriving (Eq, Show)

-- Parses CNF formula. Valid input is for example (a+b+~c)(~a+~b)()(c+a).
parseStrCNF :: String -> Either ParseError [StrClause]
parseStrCNF str = runParser cnf () "formula in CNF" str
  where
      cnf      = many clause <* eof
      clause   = StrClause <$> between (char '(') (char ')')
                                       (literal `sepBy` char '+')
      literal  = option posLit (char '~' *> pure negLit) <*> variable
      variable = (:) <$> letter <*> many (alphaNum <|> oneOf "[],")

      posLit n = (n, True)
      negLit n = (n, False)

-- Removes duplicate literals.
factor :: StrClause -> StrClause
factor = StrClause . nub . scLits

