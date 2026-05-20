{-# OPTIONS_GHC -i.. #-}
module Pledge.GuardedRE
    ( -- * Type
      GuardedRE(..)
      -- * Construction
    , fromRE
    , fromPPred
      -- * Conjunction
    , conjoin
      -- * Derivatives
    , deriveGuarded
      -- * Membership
    , nullableGuarded
    , checkGuarded
    ) where

import qualified Data.Map.Strict as Map
import Pledge.Core
import Pledge.Presburger
import Pledge.RE

-- ── Type ──────────────────────────────────────────────────────────────────────
-- An GuardedRE is a conjunction of two independent constraints on a state:
--   • a Presburger predicate over the heap
--   • a regular expression over the event trace
--
-- A state (heap, trace) satisfies GuardedRE p r  iff
--     heap  |= p           (Presburger side)
--   ∧ trace ∈ L(r)         (trace side)

data GuardedRE = GuardedRE PPred RE
    deriving (Eq)

instance Show GuardedRE where
    show (GuardedRE PTrue r) = show r
    show (GuardedRE p     r) = "[" ++ show p ++ "] ∧ " ++ show r

-- ── Construction ──────────────────────────────────────────────────────────────

-- Lift a plain RE (no heap constraint).
fromRE :: RE -> GuardedRE
fromRE = GuardedRE PTrue

-- Lift a plain PPred (no trace constraint: accept any trace).
fromPPred :: PPred -> GuardedRE
fromPPred p = GuardedRE p top

-- ── Conjunction ───────────────────────────────────────────────────────────────
-- (p1, r1) ∧ (p2, r2)  =  (p1 ∧ p2, r1 ∩ r2)
-- Both the heap and the trace must satisfy both constraints.

conjoin :: GuardedRE -> GuardedRE -> GuardedRE
conjoin (GuardedRE p1 r1) (GuardedRE p2 r2) =
    GuardedRE (normalizePPred (PAnd p1 p2)) (normalize (And r1 r2))

-- ── Derivatives ───────────────────────────────────────────────────────────────
-- Consuming an event advances only the trace side; the heap predicate is
-- a static constraint and does not change with individual events.

deriveGuarded :: Event -> GuardedRE -> GuardedRE
deriveGuarded e (GuardedRE p r) = GuardedRE p (normalize (derivative e r))

-- ── Membership ────────────────────────────────────────────────────────────────

-- nullableGuarded checks whether (heap, ε) satisfies the GuardedRE:
--   • the RE must be nullable (ε ∈ L(r))
--   • the Presburger predicate must be satisfiable against the heap
--
-- The heap is a concrete assignment Map Addr Int; we instantiate the
-- predicate with those values and ask the solver.
nullableGuarded :: Map.Map Addr Int -> GuardedRE -> IO Bool
nullableGuarded heap (GuardedRE p r)
    | not (nullable r) = return False
    | otherwise        = do
        result <- checkPPred (instantiate heap p)
        return $ case result of
            Satisfied _ -> True
            _           -> False

-- Instantiate a PPred by substituting concrete heap values for ValAt.
-- Any address not present in the map is left as a free variable.
instantiate :: Map.Map Addr Int -> PPred -> PPred
instantiate heap = go
  where
    subst (Lit n)     = Lit n
    subst (ValAt a)   = maybe (ValAt a) Lit (Map.lookup a heap)
    subst (Add e1 e2) = Add (subst e1) (subst e2)
    subst (Mul k e)   = Mul k (subst e)

    go PTrue        = PTrue
    go (PLt  e1 e2) = PLt  (subst e1) (subst e2)
    go (PLe  e1 e2) = PLe  (subst e1) (subst e2)
    go (PEq  e1 e2) = PEq  (subst e1) (subst e2)
    go (PGt  e1 e2) = PGt  (subst e1) (subst e2)
    go (PGe  e1 e2) = PGe  (subst e1) (subst e2)
    go (PNot q)     = PNot (go q)
    go (PAnd q1 q2) = PAnd (go q1) (go q2)

-- checkGuarded heap trace ext: does (heap, trace) satisfy ext?
-- Folds deriveGuarded over the trace then checks nullability.
checkGuarded :: Map.Map Addr Int -> [Event] -> GuardedRE -> IO Bool
checkGuarded heap trace ext =
    nullableGuarded heap (foldl (flip deriveGuarded) ext trace)

-- ── Composable instance ───────────────────────────────────────────────────────
-- Lifts the RE algebra to GuardedRE, threading PPred as a conjunction.
--
-- subtraction: both heap predicates are conjoined in the residual, so the
-- full constraint from both sides is preserved; the RE side uses reSubtraction.

instance Composable GuardedRE where
    concatenation (GuardedRE p1 r1) (GuardedRE p2 r2) =
        GuardedRE (normalizePPred (PAnd p1 p2)) (normalize (Seq r1 r2))
    conjunction   = conjoin
    empty         = GuardedRE PTrue Epsilon
    universe      = GuardedRE PTrue top
    subtraction   (GuardedRE p1 r1) (GuardedRE p2 r2) =
        GuardedRE (normalizePPred (PAnd p1 p2)) (normalize (reSubtraction r1 r2))
