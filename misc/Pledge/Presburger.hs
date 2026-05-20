{-# OPTIONS_GHC -i.. #-}
module Pledge.Presburger
    ( -- * Terms
      Term(..)
      -- * Events
    , Event(..)
    , subsumesEvent
      -- * Shared type aliases
    , Addr
    , Val
      -- * Presburger expressions
    , PExpr(..)
    , pNeg
      -- * Presburger predicates
    , PPred(..)
      -- * Normalization
    , normalizePExpr
    , normalizePPred
      -- * Solver result type
    , SolverResult(..)
    , checkPPred
    ) where

import Control.Exception (try, SomeException)
import Data.List (nub, intercalate)
import qualified Data.Map.Strict as Map
import Data.SBV hiding (Unsatisfiable)

-- ── Terms ─────────────────────────────────────────────────────────────────────

data Term = Str String | Num Int | List [Term]
    deriving (Eq)

instance Show Term where
    show (Str s) = "\"" ++ s ++ "\""
    show (Num n) = show n
    show (List ts) = "[" ++ intercalate ", " (map show ts) ++ "]"

-- ── Events ────────────────────────────────────────────────────────────────────

-- An Event is either a concrete named call or a wildcard pattern (Σ).
-- Wildcard is used only inside RE patterns (Single Wildcard ≡ Σ, any one step).
data Event = Atom String Term    -- e.g. send(x)
           | Wildcard            -- matches any single event
    deriving (Eq)

instance Show Event where
    show (Atom name arg) = name ++ "(" ++ show arg ++ ")"
    show Wildcard         = "_"

-- Does a concrete event occurrence match an event pattern in a Single?
subsumesEvent :: Event -> Event -> Bool
subsumesEvent _            Wildcard      = True   -- any occurrence matches wildcard pattern
subsumesEvent (Atom n1 a1) (Atom n2 a2) = n1 == n2 && a1 == a2
subsumesEvent Wildcard     (Atom _ _)   = False   -- wildcard occurrence ≠ specific pattern

-- ── Shared type aliases ───────────────────────────────────────────────────────
-- Addr and Val are used by both RE examples and the SL instance.

type Addr = Int
type Val  = Int

-- ── Presburger Arithmetic ─────────────────────────────────────────────────────
-- Linear arithmetic over heap values.  Variables are heap addresses; ValAt a
-- dereferences address a.  Only scalar multiplication (k * e) is allowed to
-- keep expressions linear.

data PExpr
    = Lit Int           -- integer literal
    | ValAt Addr        -- value stored at address: h[a]
    | Add PExpr PExpr   -- e1 + e2
    | Mul Int   PExpr   -- k * e  (scalar only, preserves linearity)
    deriving (Eq)

instance Show PExpr where
    show (Lit n)     = show n
    show (ValAt a)   = "h[" ++ show a ++ "]"
    show (Add e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
    show (Mul k e)   = show k ++ "*" ++ show e

-- Derived expression smart constructors
pNeg :: PExpr -> PExpr
pNeg = Mul (-1)

data PPred
    = PTrue
    | PFalse
    | PLt  PExpr PExpr  -- e1 < e2
    | PLe  PExpr PExpr  -- e1 ≤ e2
    | PEq  PExpr PExpr  -- e1 = e2
    | PGt  PExpr PExpr  -- e1 > e2
    | PGe  PExpr PExpr  -- e1 ≥ e2
    | PNot PPred
    | PAnd PPred PPred
    deriving (Eq)

instance Show PPred where
    show PTrue        = "true"
    show PFalse       = "false"
    show (PLt  e1 e2) = show e1 ++ " < "  ++ show e2
    show (PLe  e1 e2) = show e1 ++ " ≤ "  ++ show e2
    show (PEq  e1 e2) = show e1 ++ " = "  ++ show e2
    show (PGt  e1 e2) = show e1 ++ " > "  ++ show e2
    show (PGe  e1 e2) = show e1 ++ " ≥ "  ++ show e2
    show (PNot p)     = "¬(" ++ show p ++ ")"
    show (PAnd p q)   = "(" ++ show p ++ " ∧ " ++ show q ++ ")"


-- ── Normalization ─────────────────────────────────────────────────────────────

-- Simplify a PExpr using arithmetic identities.
normalizePExpr :: PExpr -> PExpr
normalizePExpr (Add e1 e2) = case (normalizePExpr e1, normalizePExpr e2) of
    (Lit 0, e')       -> e'
    (e',    Lit 0)    -> e'
    (Lit a, Lit b)    -> Lit (a + b)
    (e1',   e2')      -> Add e1' e2'
normalizePExpr (Mul k e) = case normalizePExpr e of
    _       | k == 0  -> Lit 0
    e'      | k == 1  -> e'
    Lit n             -> Lit (k * n)
    e'                -> Mul k e'
normalizePExpr e = e   -- Lit, ValAt: already normal

-- Simplify a PPred by:
--   • eliminating PTrue from PAnd (identity)
--   • short-circuiting on PNot PTrue (false absorbs everything)
--   • deduplicating conjuncts (idempotency)
--   • substituting equalities of the form h[a]=k into sibling conjuncts
--   • eliminating double negation
--   • evaluating comparisons between literals
normalizePPred :: PPred -> PPred
normalizePPred p =
    let conjuncts = flattenAnd (normStep p)
        deduped   = nub conjuncts
        eqs       = [ (a, k) | PEq (ValAt a) (Lit k) <- deduped ]
                 ++ [ (a, k) | PEq (Lit k) (ValAt a) <- deduped ]
        subbed    = map (normStep . substEqs eqs) deduped
    in if PFalse `elem` subbed
       then PFalse
       else rebuildAnd (nub (filter (/= PTrue) subbed))

-- One-level structural simplification (no flattening).
normStep :: PPred -> PPred
normStep (PAnd p q) = case (normStep p, normStep q) of
    (PFalse, _)          -> PFalse       -- false absorbs
    (_, PFalse)          -> PFalse
    (PTrue, q')          -> q'
    (p',    PTrue)       -> p'
    (p',    q') | p'==q' -> p'
    (p',    q')          -> PAnd p' q'
normStep (PNot p) = case normStep p of
    PTrue   -> PFalse                    -- ¬true  = false
    PFalse  -> PTrue                     -- ¬false = true
    PNot p' -> p'                        -- ¬¬p    = p
    p'      -> PNot p'
normStep (PLt  e1 e2) = evalCmp PLt  (<)  e1 e2
normStep (PLe  e1 e2) = evalCmp PLe  (<=) e1 e2
normStep (PEq  e1 e2) = evalCmp PEq  (==) e1 e2
normStep (PGt  e1 e2) = evalCmp PGt  (>)  e1 e2
normStep (PGe  e1 e2) = evalCmp PGe  (>=) e1 e2
normStep p            = p

-- Flatten a right/left-associated PAnd tree into a list of conjuncts.
-- PFalse is kept as-is so the caller can detect it and short-circuit.
flattenAnd :: PPred -> [PPred]
flattenAnd (PAnd p q) = flattenAnd p ++ flattenAnd q
flattenAnd PTrue      = []
flattenAnd p          = [p]

-- Rebuild a flat list of conjuncts back into a PAnd tree ([] → PTrue).
rebuildAnd :: [PPred] -> PPred
rebuildAnd []     = PTrue
rebuildAnd [p]    = p
rebuildAnd (p:ps) = PAnd p (rebuildAnd ps)

-- Substitute a list of (addr → literal) equalities into a PExpr.
substEqs :: [(Addr, Int)] -> PPred -> PPred
substEqs eqs = goP
  where
    goE (ValAt a)   = maybe (ValAt a) Lit (lookup a eqs)
    goE (Add e1 e2) = normalizePExpr (Add (goE e1) (goE e2))
    goE (Mul k e)   = normalizePExpr (Mul k (goE e))
    goE e           = e

    goP (PLt  e1 e2) = normStep (PLt  (goE e1) (goE e2))
    goP (PLe  e1 e2) = normStep (PLe  (goE e1) (goE e2))
    goP (PEq  e1 e2) = normStep (PEq  (goE e1) (goE e2))
    goP (PGt  e1 e2) = normStep (PGt  (goE e1) (goE e2))
    goP (PGe  e1 e2) = normStep (PGe  (goE e1) (goE e2))
    goP (PNot q)     = normStep (PNot (goP q))
    goP (PAnd p q)   = normStep (PAnd (goP p) (goP q))
    goP p            = p

-- Helper: normalize subexpressions and fold literal comparisons to PTrue/PFalse.
evalCmp :: (PExpr -> PExpr -> PPred) -> (Int -> Int -> Bool) -> PExpr -> PExpr -> PPred
evalCmp con op e1 e2 =
    case (normalizePExpr e1, normalizePExpr e2) of
        (Lit a, Lit b) -> if op a b then PTrue else PFalse
        (e1',  e2')    -> con e1' e2'

-- ── Result type ───────────────────────────────────────────────────────────────

-- A witness heap maps each address to its concrete integer value.
data SolverResult
    = Satisfied (Map.Map Addr Integer)  -- SAT: a concrete witness heap
    | Unsatisfiable                     -- UNSAT: no heap satisfies the constraints
    | SolverUnknown String              -- solver unavailable or timeout
    deriving (Eq)

instance Show SolverResult where
    show (Satisfied h)
        | Map.null h = "SAT  (no heap variables)"
        | otherwise  = "SAT  heap = { "
                    ++ intercalate ", " [ "h[" ++ show a ++ "] := " ++ show v
                                       | (a, v) <- Map.toList h ]
                    ++ " }"
    show Unsatisfiable       = "UNSAT"
    show (SolverUnknown msg) = "UNKNOWN (" ++ msg ++ ")"

-- ── Address collection ────────────────────────────────────────────────────────

addrsInPExpr :: PExpr -> [Addr]
addrsInPExpr (Lit _)     = []
addrsInPExpr (ValAt a)   = [a]
addrsInPExpr (Add e1 e2) = addrsInPExpr e1 ++ addrsInPExpr e2
addrsInPExpr (Mul _ e)   = addrsInPExpr e

addrsInPPred :: PPred -> [Addr]
addrsInPPred PTrue        = []
addrsInPPred PFalse       = []
addrsInPPred (PLt  e1 e2) = addrsInPExpr e1 ++ addrsInPExpr e2
addrsInPPred (PLe  e1 e2) = addrsInPExpr e1 ++ addrsInPExpr e2
addrsInPPred (PEq  e1 e2) = addrsInPExpr e1 ++ addrsInPExpr e2
addrsInPPred (PGt  e1 e2) = addrsInPExpr e1 ++ addrsInPExpr e2
addrsInPPred (PGe  e1 e2) = addrsInPExpr e1 ++ addrsInPExpr e2
addrsInPPred (PNot p)     = addrsInPPred p
addrsInPPred (PAnd p q)   = addrsInPPred p ++ addrsInPPred q

-- ── SBV translation ───────────────────────────────────────────────────────────

pexprToSBV :: Map.Map Addr SInteger -> PExpr -> SInteger
pexprToSBV _  (Lit n)     = fromIntegral n
pexprToSBV hv (ValAt a)   = hv Map.! a
pexprToSBV hv (Add e1 e2) = pexprToSBV hv e1 + pexprToSBV hv e2
pexprToSBV hv (Mul k e)   = fromIntegral k * pexprToSBV hv e

ppredToSBV :: Map.Map Addr SInteger -> PPred -> SBool
ppredToSBV _  PTrue        = sTrue
ppredToSBV _  PFalse       = sFalse
ppredToSBV hv (PLt  e1 e2) = pexprToSBV hv e1 .< pexprToSBV hv e2
ppredToSBV hv (PLe  e1 e2) = pexprToSBV hv e1 .<= pexprToSBV hv e2
ppredToSBV hv (PEq  e1 e2) = pexprToSBV hv e1 .== pexprToSBV hv e2
ppredToSBV hv (PGt  e1 e2) = pexprToSBV hv e1 .> pexprToSBV hv e2
ppredToSBV hv (PGe  e1 e2) = pexprToSBV hv e1 .>= pexprToSBV hv e2
ppredToSBV hv (PNot p)     = sNot (ppredToSBV hv p)
ppredToSBV hv (PAnd p q)   = ppredToSBV hv p .&& ppredToSBV hv q

-- ── Core PPred solver ─────────────────────────────────────────────────────────
-- All ValAt references become unbounded integer variables.

checkPPred :: PPred -> IO SolverResult
checkPPred p = do
    let addrs   = nub (addrsInPPred p)
        varFor a = "h" ++ show a
    eResult <- try $ sat $ do
        vars <- mapM (sInteger . varFor) addrs
        let hv = Map.fromList (zip addrs vars)
        return (ppredToSBV hv p)
    case eResult of
        Left  (e :: SomeException) -> return (SolverUnknown (show e))
        Right result ->
            if modelExists result
                then do
                    let vals = [ (a, v)
                               | a <- addrs
                               , Just v <- [getModelValue (varFor a) result] ]
                    return (Satisfied (Map.fromList vals))
                else return Unsatisfiable

