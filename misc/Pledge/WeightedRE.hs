{-# OPTIONS_GHC -i.. #-}
{-# LANGUAGE FlexibleInstances #-}
module Pledge.WeightedRE
    ( -- * Weighted regular expressions
      WRE(..)
      -- * Semantics
    , wNullable
      -- * Alphabet
    , wAtoms
    , wFirstWith
    , wFirst
      -- * Derivatives
    , wDerivative
      -- * Normalization
    , wNormalize
      -- * Quotient
    , wSubtraction
      -- * Smart constructors
    , wTop
    , wFinally
    , wGlobally
    , wPreviously
    ) where

import Prelude hiding ((<>))
import Data.List (union, nub)
import Pledge.Core
import Pledge.Presburger (Event(..), subsumesEvent)
import Pledge.Semiring

-- ── Type ──────────────────────────────────────────────────────────────────────
-- WRE w is a regular expression whose transitions carry weights from semiring w.
--
-- The language of a WRE is a function  Σ* → w  (words to weights):
--   wNullable r       = weight of ε in L(r)
--   wDerivative e r   = WRE whose language is  w ↦ L(r)(e·w)
--
-- The Boolean special case  WRE Bool  recovers the existing RE exactly:
--   WBot        ↔  Bot
--   WEps True   ↔  Epsilon
--   WSingle True e  ↔  Single e
--   WSeq / WAdd / WAnd / WStar  ↔  Seq / Or / And / Star

data WRE w
    = WBot                       -- 0: empty language  (weight 0 everywhere)
    | WEps w                     -- ε accepted with weight w
    | WSingle w Event            -- single event accepted with weight w
    | WSeq  (WRE w) (WRE w)     -- sequential composition  (⊗ on languages)
    | WAdd  (WRE w) (WRE w)     -- weighted choice           (⊕ on languages)
    | WAnd  (WRE w) (WRE w)     -- weighted conjunction  (pointwise ⊗)
    | WStar (WRE w)              -- Kleene star
    deriving (Eq)

instance Semiring w => Show (WRE w) where
    show WBot                           = "∅"
    show (WEps w)     | w == sone       = "ε"
                      | otherwise       = "[" ++ show w ++ "]ε"
    show (WSingle w Wildcard)
                      | w == sone       = "Σ"
                      | otherwise       = "[" ++ show w ++ "]Σ"
    show (WSingle w e)| w == sone       = show e
                      | otherwise       = "[" ++ show w ++ "]" ++ show e
    -- recognise common patterns for nicer display
    show (WSeq (WStar (WSingle w1 Wildcard)) (WSingle w2 ev))
        | w1 == sone && w2 == sone      = "F(" ++ show ev ++ ")"
        | otherwise                     = "F[" ++ show w2 ++ "](" ++ show ev ++ ")"
    show (WStar (WSingle w ev))
        | w == sone                     = "G(" ++ show ev ++ ")"
    show r = go r
      where
        go (WSeq r1 r2) = show r1 ++ " · " ++ show r2
        go (WAdd r1 r2) = "(" ++ show r1 ++ ") ⊕ (" ++ show r2 ++ ")"
        go (WAnd r1 r2) = "(" ++ show r1 ++ ") ∧ (" ++ show r2 ++ ")"
        go (WStar r1)   = "(" ++ show r1 ++ ")*"
        go r1           = show r1

-- ── Semantics: weight of ε ────────────────────────────────────────────────────
-- wNullable r = the semiring weight assigned to the empty word ε.
-- In the Boolean case this equals nullable :: RE -> Bool.

wNullable :: Semiring w => WRE w -> w
wNullable WBot          = szero
wNullable (WEps w)      = w
wNullable (WSingle _ _) = szero
wNullable (WSeq r1 r2)  = smul (wNullable r1) (wNullable r2)
wNullable (WAdd r1 r2)  = sadd (wNullable r1) (wNullable r2)
wNullable (WAnd r1 r2)  = smul (wNullable r1) (wNullable r2)
wNullable (WStar _)     = sone   -- ε ∈ L(r*) with unit weight for every semiring

-- ── Alphabet ──────────────────────────────────────────────────────────────────

wAtoms :: WRE w -> [Event]
wAtoms WBot               = []
wAtoms (WEps _)           = []
wAtoms (WSingle _ Wildcard) = []
wAtoms (WSingle _ e)      = [e]
wAtoms (WSeq  r1 r2)      = wAtoms r1 `union` wAtoms r2
wAtoms (WAdd  r1 r2)      = wAtoms r1 `union` wAtoms r2
wAtoms (WAnd  r1 r2)      = wAtoms r1 `union` wAtoms r2
wAtoms (WStar r)          = wAtoms r

wFirstWith :: Semiring w => [Event] -> WRE w -> [Event]
wFirstWith _    WBot                    = []
wFirstWith _    (WEps _)               = []
wFirstWith alph (WSingle _ Wildcard)   = alph
wFirstWith _    (WSingle _ e)          = [e]
wFirstWith alph (WSeq r1 r2)
    | wNullable r1 /= szero            = wFirstWith alph r1 `union` wFirstWith alph r2
    | otherwise                        = wFirstWith alph r1
wFirstWith alph (WAdd r1 r2)           = wFirstWith alph r1 `union` wFirstWith alph r2
wFirstWith alph (WAnd r1 r2)           = [ e | e <- wFirstWith alph r1
                                             , e `elem` wFirstWith alph r2 ]
wFirstWith alph (WStar r)              = wFirstWith alph r

wFirst :: Semiring w => WRE w -> [Event]
wFirst r = wFirstWith (wAtoms r) r

-- ── Brzozowski derivative ─────────────────────────────────────────────────────
-- wDerivative e r: the WRE for all continuations after event e.
-- When r1 is nullable in WSeq, both branches contribute (weighted by wNullable r1).

wDerivative :: Semiring w => Event -> WRE w -> WRE w
wDerivative _ WBot             = WBot
wDerivative _ (WEps _)         = WBot
wDerivative e (WSingle w p)
    | subsumesEvent e p        = WEps w
    | otherwise                = WBot
wDerivative e (WSeq r1 r2)
    | wNullable r1 /= szero    =
        WAdd (WSeq (wDerivative e r1) r2)
             (WSeq (WEps (wNullable r1)) (wDerivative e r2))
    | otherwise                = WSeq (wDerivative e r1) r2
wDerivative e (WAdd r1 r2)     = WAdd (wDerivative e r1) (wDerivative e r2)
wDerivative e (WAnd r1 r2)     = WAnd (wDerivative e r1) (wDerivative e r2)
wDerivative e (WStar r)        = WSeq (wDerivative e r) (WStar r)

-- ── Normalization ─────────────────────────────────────────────────────────────
-- Structural simplifications that hold for every semiring.

wNormalize :: Semiring w => WRE w -> WRE w
wNormalize r = case r of
    WSeq r1 r2 -> case (wNormalize r1, wNormalize r2) of
        (WBot,    _)               -> WBot
        (_,       WBot)            -> WBot
        (WEps w1, WEps w2)         -> WEps (smul w1 w2)
        (WEps w,  r2') | w == sone -> r2'
        (r1', WEps w)  | w == sone -> r1'
        (r1', r2')                 -> WSeq r1' r2'

    WAdd r1 r2 -> case (wNormalize r1, wNormalize r2) of
        (WBot, r')    -> r'
        (r',   WBot)  -> r'
        (r1',  r2')   -> WAdd r1' r2'

    WAnd r1 r2 -> case (wNormalize r1, wNormalize r2) of
        (WBot,    _)      -> WBot
        (_,       WBot)   -> WBot
        (WEps w1, WEps w2)-> WEps (smul w1 w2)
        (r1',     r2')    -> WAnd r1' r2'

    WStar r1 -> case wNormalize r1 of
        WBot   -> WEps sone    -- ∅* = ε
        WEps _ -> WEps sone    -- ε* = ε
        r1'    -> WStar r1'

    _ -> r

-- ── Quotient (weighted left-quotient) ─────────────────────────────────────────
-- wSubtraction r1 r2: the weighted residual of r2 after consuming a prefix
-- from r1.  Parallels reSubtraction using Brzozowski derivatives.
-- Base case: WEps _ means the prefix is ε, so r2 is unchanged.

wSubtraction :: Semiring w => WRE w -> WRE w -> WRE w
wSubtraction (WEps _) r2 = r2
wSubtraction r1       r2 =
    let alph  = wAtoms r1 `union` wAtoms r2
        evts  = wFirstWith alph r1
        step e = wSubtraction (wNormalize (wDerivative e r1))
                               (wNormalize (wDerivative e r2))
    in foldr (WAdd . step) WBot evts

-- ── Smart constructors ────────────────────────────────────────────────────────

-- Σ* — universal language with unit weight on every transition.
wTop :: Semiring w => WRE w
wTop = WStar (WSingle sone Wildcard)

-- F[w](ev) — event ev must eventually occur, observed with weight w.
wFinally :: Semiring w => w -> Event -> WRE w
wFinally w ev = WSeq wTop (WSingle w ev)

-- G[w](ev) — every step must be ev, each observed with weight w.
wGlobally :: Semiring w => w -> Event -> WRE w
wGlobally w ev = WStar (WSingle w ev)

-- previously[w](ev) — ev occurred at some point in the past with weight w.
wPreviously :: Semiring w => w -> Event -> WRE w
wPreviously w ev = WSeq wTop (WSeq (WSingle w ev) wTop)

-- ── Composable instance ───────────────────────────────────────────────────────
-- WRE w lifts the Composable algebra to the weighted setting.
-- This makes Pledge (WRE Prob) and Pledge (WRE Tropical) work out of the box.

instance Semiring w => Composable (WRE w) where
    concatenation r1 r2 = wNormalize (WSeq r1 r2)
    conjunction   r1 r2 = wNormalize (WAnd r1 r2)
    empty               = WEps sone
    universe            = wTop
    subtraction         = wSubtraction
