{-# LANGUAGE ViewPatterns, CPP #-}

-- |
-- Module    : Main
-- Copyright : (c) Radek Micek 2010
-- License   : BSD3
-- Stability : experimental
--
-- Prover for propositional logic.
--
-- This prover uses conflict driven search. When the conflict is
-- generated we use resolution to derive asserting clause which directs
-- search to another assignment of variables.
--
-- If the conflict is generated at level 0 we can derive an empty clause
-- since all variables have antecendent.
--
-- Very good description of the main idea of this algorithm can be found
-- in the article Validating SAT Solvers Using an Independent Resolution-Based
-- Checker: Practical Implementations and Other Applications by Lintao Zhang
-- and Sharad Malik.
module Main where

import Control.Applicative ((<$>))
import Control.Arrow (second)
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import CNFParser
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import System.Environment (getArgs, getProgName)

-- Only positive integers.
type Var = Int

-- Positive integers for positive literals and negative integers for negative.
-- Absolute value of literal gives variable.
type Lit = Int

data Clause = Clause { cResolved :: Maybe (Clause, Clause)
                     , cId       :: !Int
                       -- Literals are sorted and each variable appears
                       -- at most once.
                     , cLits     :: [Lit] }
    deriving (Eq, Show)

type Eval = Lit -> Maybe Bool

data Deduced = Conflict | Unit Lit
    deriving Eq

-- Number of guesses.
type Level = Int

data DLLState = DS { -- Values for some variables.
                     dsAssignment   :: IM.IntMap Bool
                     -- In which level was variable assigned.
                   , dsWhenAssigned :: IM.IntMap Level
                     -- Antecendents for each level.
                   , dsAntecendents :: [IM.IntMap Clause]
                     -- Set of assigned variables for each level.
                   , dsAssigned     :: [IS.IntSet]
                     -- Set with all unasigned variables.
                   , dsUnassigned   :: IS.IntSet
                   , dsLevel        :: Level
                   , dsLastClauseId :: Int
                   , dsClauses      :: [Clause] }

-- Result of DLL algorithm.
data Result = EmptyClause Clause | Assignment (IM.IntMap Bool)
    deriving Show

-- Conflict driven search based on DLL.
--
-- Input clauses are renumbered.
dll :: [Clause] -> Result
dll clauses = fst $ runState bcp st
  where
      st = DS { dsAssignment   = IM.empty
              , dsWhenAssigned = IM.empty
              , dsAntecendents = [IM.empty]
              , dsAssigned     = [IS.empty]
              , dsUnassigned   = IS.fromList variables
              , dsLevel        = 0
              , dsLastClauseId = lastId
              , dsClauses      = clauses' }

      variables          = nub $ map abs $ concatMap cLits clauses
      (lastId, clauses') = let updateId i cl = (succ i, cl { cId = succ i })
                           in mapAccumL updateId 0 clauses

type DLL = State DLLState

-- Returns Just when the clause is unit or conflicting. In case of unit clause
-- unit literal is returned.
deduce :: Eval -> Clause -> Maybe Deduced
deduce eval (cLits -> lits) = case evaluated of
    []             -> Just $ Conflict
    [(l, Nothing)] -> Just $ Unit l
    _              -> Nothing
  where
      evaluated = filter ((/= Just False) . snd) $ zip lits $ map eval lits

-- Level is increased when no antecendent is given.
assignLit :: Bool -> Lit -> Maybe Clause -> DLL ()
assignLit val l antecendent = do
    case antecendent of
        Nothing -> incLevel
        Just a  -> addAntecendent a
        
    modify (\st -> st
        { dsAssignment   = IM.insert v value (dsAssignment st)
        , dsWhenAssigned = IM.insert v (dsLevel st) (dsWhenAssigned st)
        , dsAssigned     = modifyHead (IS.insert v) (dsAssigned st)
        , dsUnassigned   = IS.delete v (dsUnassigned st) })
  where
      (v, value) = if l < 0 then (-l, not val) else (l, val)

      incLevel = modify (\st -> st
          { dsAntecendents = IM.empty : dsAntecendents st
          , dsAssigned     = IS.empty : dsAssigned st
          , dsLevel        = succ $ dsLevel st })

      addAntecendent a = modify (\st -> st
          { dsAntecendents = modifyHead (IM.insert v a) (dsAntecendents st) })

      modifyHead f (x:xs) = f x : xs
      modifyHead _ _      = error "assignLit: empty list"

-- Continues by guess or by handleConflict.
bcp :: DLL Result
bcp = do
    st <- get

    let -- Evaluates literals.
        eval l  = if l < 0 then not <$> (IM.lookup (-l) $ dsAssignment st)
                           else          IM.lookup l    $ dsAssignment st
        clauses = dsClauses st
        deduced = filter ((/= Nothing) . snd)
                      $ zip clauses
                      $ map (deduce eval) clauses

    case deduced of
        []                      -> guess
        -- Try to assign more.
        (cl, Just (Unit l)) : _ -> assignLit True l (Just cl) >> bcp
        (cl, Just Conflict) : _ -> handleConflict cl
        _                       -> error "bcp: impossible case"

-- Continues by backtrack or returns empty clause.
--
-- We distinguish two cases: level > 0 and level = 0.
-- Latter case ends by returning empty clause.
handleConflict :: Clause -> DLL Result
handleConflict cl = do
    st <- get

    let assig  = head $ dsAssigned st
        ante   = head $ dsAntecendents st
        lastId = dsLastClauseId st

    if dsLevel st > 0
      then do
          let x@(assertCl, _) = assertingClause cl assig ante lastId

          put $ st { dsLastClauseId = cId assertCl
                   , dsClauses      = assertCl : dsClauses st }

          backtrack $ assertingLevel x (dsWhenAssigned st)
      else do
          let emptyCl = emptyClause cl ante lastId

          put $ st { dsLastClauseId = cId emptyCl
                   , dsClauses      = emptyCl : dsClauses st }

          return $ EmptyClause emptyCl

-- Makes guess and continues by bcp or returns assignment
-- if no guess is possible.
--
-- Always guesses False.
guess :: DLL Result
guess = do
    freeVars <- IS.toList . dsUnassigned <$> get

    case freeVars of
        []    -> Assignment . dsAssignment <$> get
        (v:_) -> assignLit False v Nothing >> bcp

-- Continues with by bcp.
backtrack :: Level -> DLL Result
backtrack level = do
    st <- get

    if dsLevel st == level
      then bcp
      else do
          -- Backtrack one level up.
          let vars            = IS.toList $ head $ dsAssigned st
              removeFromMap m = foldl (flip IM.delete) m vars
              insertToSet s   = foldl (flip IS.insert) s vars

          modify (\sta -> sta
              { dsAssignment   = removeFromMap (dsAssignment sta)
              , dsWhenAssigned = removeFromMap (dsWhenAssigned sta)
              , dsAntecendents = tail (dsAntecendents sta)
              , dsAssigned     = tail (dsAssigned sta)
              , dsUnassigned   = insertToSet (dsUnassigned sta)
              , dsLevel        = pred (dsLevel sta) })

          backtrack level

------------------------------------------------------------------------------
-- Asserting clause and empty clause

-- Current level > 0.
assertingClause
    :: Clause           -- Conflicting clause (all literals are false)
    -> IS.IntSet        -- Variables assigned in current level
    -> IM.IntMap Clause -- Antecendents of variables assigned in current level
    -> Int              -- Last id of clause
    -> (Clause, Var)    -- Asserting clause and single variable
                        -- assigned in current level
                        -- (returned clause has new last id).
assertingClause cl assigned antecendents lastId = case variables of
    []      -> error "assertingClause: no variable assigned at current level"
    [v]     -> (cl, v)
    (x:y:_) -> let anteX     = IM.lookup x antecendents
                   anteY     = IM.lookup y antecendents
                   -- One of the variables x, y must have antecendent.
                   -- Because there is only one variable assigned at this level
                   -- which has no antecendent.
                   --
                   -- For termination is not essential which variable we choose
                   -- to resolve on (antecendent contains only variables
                   -- which were assigned earlier).
                   (ante, v) = case (anteX, anteY) of
                       (Just a, _) -> (a, x)
                       (_, Just a) -> (a, y)
                       _           -> error "assertingClause: no antecendent"
                   newId     = succ lastId
                   newCl     = resolve cl ante v newId
               in assertingClause newCl assigned antecendents newId
  where
      variables = filter (flip IS.member assigned) $ map abs $ cLits cl

-- Current level > 0.
assertingLevel :: (Clause, Var) -> IM.IntMap Level -> Level
assertingLevel (cl, v) whenAssigned
    | null levels = 0
    | otherwise   = maximum levels
  where
      levels    = map (fromJust . flip IM.lookup whenAssigned) variables
      variables = filter (/= v) $ map abs $ cLits cl

-- Current level = 0.
--
-- At level 0 every variable has antecendent and we don't need to know
-- which variables were assigned in this level.
emptyClause
    :: Clause           -- Conflicting clause
    -> IM.IntMap Clause -- Antecendents of variables assigned in current level
    -> Int              -- Last id of clause
    -> Clause           -- Empty clause.
emptyClause cl antecendents lastId = case variables of
    []    -> cl
    (v:_) -> let -- Every variable has antecendent.
                 ante  = fromJust $ IM.lookup v antecendents
                 newId = succ lastId
                 newCl = resolve cl ante v newId
             in emptyClause newCl antecendents newId
  where
      variables = map abs $ cLits cl 

-- Resolves conflict clause with unit clause and returns conflict clause.
-- Input integer is id of new clause.
resolve :: Clause -> Clause -> Var -> Int -> Clause
#ifndef NOPROOF
resolve cl cl' v newId = Clause { cResolved = Just (cl, cl')
#else
resolve cl cl' v newId = Clause { cResolved = Nothing
#endif
                                , cId = newId
                                , cLits = mergeLits (literals cl) 
                                                    (literals cl') }
  where
      literals = filter ((/= v) . abs) . cLits

      mergeLits ls     []       = ls
      mergeLits []     ls'      = ls'
      mergeLits (l:ls) (l':ls') = case compare l l' of
          LT -> l  : mergeLits ls     (l':ls')
          GT -> l' : mergeLits (l:ls) ls'
          EQ -> l  : mergeLits ls     ls'

------------------------------------------------------------------------------
-- Input processing

-- Returns converted CNF and association list (variable name -> variable).
-- Returned clauses have ids set to zeto.
toCNF :: [StrClause] -> ([Clause], [(String, Var)])
toCNF clauses = runState (mapM convertClause clauses') []
  where
      -- Handle clauses which contain some variable more than once.
      clauses' = filter (not . isTaut) $ map factor clauses
      isTaut (StrClause lits) = any ((`elem` lits) . second not) lits

      convertClause (StrClause lits)
          = Clause Nothing 0 . sort <$> mapM convertLit lits

      convertLit (name, True)  = getVar name
      convertLit (name, False) = negate <$> getVar name

      getVar name = do
          allNames <- get
          case lookup name allNames of
              Nothing -> do
                  let newVar = length allNames + 1
                  put $ (name, newVar) : allNames
                  return newVar
              Just var -> return var

------------------------------------------------------------------------------
-- Printing

-- Converts association list (variable name -> variable)
-- to map (variable -> variable name).
translationTable :: [(String, Var)] -> IM.IntMap String
translationTable = let insertOne m (name, v) = IM.insert v name m
                   in foldl insertOne IM.empty

showClause :: (Var -> String) -> Clause -> String
showClause translate = intercalate "+" . map showLit . cLits
  where
      showLit l = if l < 0
                  then '~' : translate (abs l)
                  else       translate      l

showComment :: (Var -> String) -> Clause -> String
showComment translate cl = case cResolved cl of
    Nothing      -> "assumption"
    Just (r, r') -> let litsR  = cLits r
                        litsR' = cLits r'
                        lit    = head $ filter (\l -> -l `elem` litsR') litsR
                    in "resolution " ++ show (cId r) ++ ", "
                                     ++ show (cId r')
                                     ++ " on " ++ translate (abs lit)

-- Shows one step of the proof.
showStep :: (Var -> String) -> Clause -> String
showStep translate cl = show (cId cl) ++ " ("
                                      ++ showClause translate cl ++ ")  -- "
                                      ++ showComment translate cl

-- Used by showProof.
data ProofSt = ProofSt { psProvedClauses :: IS.IntSet
                         -- Difference list.
                       , psProof         :: [String] -> [String] }

showProof :: (Var -> String) -> Clause -> [String]
showProof tr clause = proofDiff []
  where
      proofDiff = psProof $ snd $ runState (showProof' clause) $ ProofSt
          { psProvedClauses = IS.empty
          , psProof         = id }

      showProof' cl = do
          unproved <- IS.notMember (cId cl) . psProvedClauses <$> get

          when unproved $ do
              case cResolved cl of
                  Nothing      -> return ()
                  Just (r, r') -> showProof' r >> showProof' r'

              modify (\st -> st
                  { psProvedClauses = IS.insert (cId cl) (psProvedClauses st)
                  , psProof         = (psProof st) . (showStep tr cl :) })

showAssignment :: (Var -> String) -> IM.IntMap Bool -> [String]
showAssignment tr = map showOne . IM.toList
  where
      showOne (v, True)  = tr v ++ "=1"
      showOne (v, False) = tr v ++ "=0"

showResult :: (Var -> String) -> Result -> [String]
showResult translate (EmptyClause cl)   = showProof translate cl
showResult translate (Assignment assig) = showAssignment translate assig

------------------------------------------------------------------------------
-- Main

main :: IO ()
main = do
    cnfArg <- listToMaybe <$> getArgs
    prog   <- getProgName

    case parseStrCNF <$> cnfArg of
        Just (Right strCNF) -> runProver strCNF
        Just (Left msg)     -> putStrLn $ show msg
        Nothing             -> putStrLn $ usage prog
  where
      usage p = intercalate "\n"
          [ "Usage: " ++ p ++ " CNF"
          , "Finds satisfying assignment for given CNF " ++
            "or derives empty clause."
          , ""
          , "CNF consists of parenthesized clauses where each clause consists"
          , "of literals separated by plus sign.  Tilde symbol means negation."
          , "Variable name starts with a letter which can be followed"
          , "by alphanumeric characters or square brackets or commas."
          , ""
          , "Example of valid CNF: (a+b+~c)()(~a+d)(c)"
          , ""
          , "Generated assignment may not contain some insignificant " ++
            "variables." ]

runProver :: [StrClause] -> IO ()
runProver strCNF = mapM_ putStrLn steps
  where
      (cnf, toVar) = toCNF strCNF
      fromVar      = fromJust . flip IM.lookup (translationTable toVar)
      steps        = showResult fromVar $ dll cnf

