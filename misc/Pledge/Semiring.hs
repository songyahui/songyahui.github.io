{-# OPTIONS_GHC -i.. #-}
module Pledge.Semiring
    ( -- * Class
      Semiring(..)
      -- * Instances
    , Prob(..)
    , Tropical(..)
    ) where

-- ── Class ─────────────────────────────────────────────────────────────────────
-- A semiring (w, ⊕, ⊗, 0, 1) generalises the Boolean lattice:
--   ⊕  = choice     (OR  / union  / min  / +)
--   ⊗  = sequence   (AND / concat / +    / ×)
--   0  = zero       (⊥   / ∅     / ∞    / 0)
--   1  = unit       (ε   / Σ*   / 0    / 1)
--
-- Laws: ⊗ distributes over ⊕; 0 absorbs ⊗; 1 is the identity for ⊗.

class (Eq w, Show w) => Semiring w where
    szero :: w          -- additive identity / absorbing for ⊗
    sone  :: w          -- multiplicative identity
    sadd  :: w -> w -> w
    smul  :: w -> w -> w

-- Boolean semiring — recovers the existing RE / Composable behaviour exactly.
instance Semiring Bool where
    szero = False
    sone  = True
    sadd  = (||)
    smul  = (&&)

-- ── Probability semiring ──────────────────────────────────────────────────────
-- Weights represent the probability that an obligation will be met.
-- sadd clamps to [0,1] so values remain valid probabilities after repeated use.
-- smul corresponds to independent sequential obligations.

newtype Prob = Prob { getProb :: Double }
    deriving (Eq, Ord)

instance Show Prob where
    show (Prob p) = show (round (p * 100) :: Int) ++ "%"

instance Semiring Prob where
    szero                      = Prob 0
    sone                       = Prob 1
    sadd (Prob a) (Prob b)     = Prob (min 1.0 (a + b))
    smul (Prob a) (Prob b)     = Prob (a * b)

-- ── Tropical (min-plus) semiring ──────────────────────────────────────────────
-- Weights represent minimum cost (e.g. expected steps) to discharge an obligation.
-- sadd = min  (choose the cheaper path)
-- smul = +    (costs accumulate along a path)
-- szero = ∞   (unreachable / no path)
-- sone  = 0   (zero cost / already discharged)

newtype Tropical = Tropical { getCost :: Double }
    deriving (Eq, Ord)

instance Show Tropical where
    show (Tropical c)
        | isInfinite c = "∞ steps"
        | otherwise    = show (round c :: Int) ++ " steps"

instance Semiring Tropical where
    szero                          = Tropical (1/0)
    sone                           = Tropical 0
    sadd (Tropical a) (Tropical b) = Tropical (min a b)
    smul (Tropical a) (Tropical b) = Tropical (a + b)
