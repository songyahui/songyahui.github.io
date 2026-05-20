{-# OPTIONS_GHC -i.. #-}
module Pledge.SL
    ( -- * Heap type
      Heap
      -- * Separation logic predicates
    , SL(..)
    , normalizeSL
    ) where

import Prelude hiding ((<>))
import qualified Data.Map.Strict as Map
import Pledge.Core
import Pledge.Presburger

-- ── Separation Logic ──────────────────────────────────────────────────────────
-- Symbolic separation-logic predicates over integer-addressed heaps.
-- Parallels the RE instance: Star/Emp play the role of Seq/Epsilon,
-- Conj/Top play the role of And/(Not Bot), and Wand plays the role of
-- the Brzozowski quotient.

type Heap = Map.Map Addr Val

data SL
    = Emp              -- empty heap                  (identity for Sep)
    | Top              -- any heap (universe)         (identity for Conj)
    | Pure PPred       -- pure predicate over heap values
    | Cell Addr Val    -- singleton: address l holds value v
    | SepStar SL SL    -- P * Q   separating conjunction
    | Conj SL SL       -- P ∧ Q   ordinary conjunction
    | Wand SL SL       -- P -* Q  magic wand (residual)
    deriving (Eq, Show)

normalizeSL :: SL -> SL
normalizeSL s = case s of

    SepStar p q -> case (normalizeSL p, normalizeSL q) of
        (Emp, q')             -> q'           -- Emp * Q = Q
        (p',  Emp)            -> p'           -- P * Emp = P
        (p',  q')             -> SepStar p' q'

    Conj p q -> case (normalizeSL p, normalizeSL q) of
        (Top, q')             -> q'           -- ⊤ ∧ Q = Q
        (p',  Top)            -> p'           -- P ∧ ⊤ = P
        (p',  q') | p' == q' -> p'           -- P ∧ P = P  (idempotent)
        (p',  q')             -> Conj p' q'

    Wand p q -> case (normalizeSL p, normalizeSL q) of
        (Emp, q')             -> q'           -- Emp -* Q = Q
        (_,   Top)            -> Top          -- P -* ⊤ = ⊤
        (p',  q')             -> Wand p' q'

    _ -> s

-- ── Composable instance ───────────────────────────────────────────────────────

instance Composable SL where
    concatenation = SepStar
    conjunction   = Conj
    empty         = Emp
    universe      = Top

    -- emp -* Q = Q: providing nothing leaves the obligation unchanged.
    subtraction Emp q = q
    -- Contract convention: ⊤ precondition is trivially discharged.
    subtraction Top _ = Emp
    -- General case: symbolic magic wand.
    subtraction p   q = Wand p q
