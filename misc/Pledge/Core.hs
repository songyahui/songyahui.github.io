{-# OPTIONS_GHC -i.. #-}
module Pledge.Core
    ( -- * Composable class
      Composable(..)
    , (<>)
    , (/\)
    , (\\)
      -- * Pledge monad
    , Pledge(..)
    , evalFuture
    ) where

import Prelude hiding ((<>))

class Composable a where
    concatenation :: a -> a -> a
    conjunction   :: a -> a -> a
    empty         :: a
    universe      :: a
    subtraction   :: a -> a -> a

infixl 6 <>
(<>) :: Composable a => a -> a -> a
(<>) = concatenation

infixl 7 /\
(/\) :: Composable a => a -> a -> a
(/\) = conjunction

infixl 5 \\
(\\) :: Composable a => a -> a -> a
(\\) = subtraction

-- ── Pledge monad ─────────────────────────────────────────────────────────────

-- future is now indexed by the return value (direction 1: data-dependent
-- future conditions).  This lets an operation's temporal obligation refer
-- to whatever resource handle it returns, e.g.
--   mallocFresh addr = Effectful { ..., future = \a -> finally(free(a)) }
-- so that the exact address returned drives the obligation.

data Pledge eff a = Pledge
    { ret    :: a
    , pre    :: eff
    , post   :: eff
    , future :: a -> eff   -- indexed by the return value
    }

-- Convenience: evaluate the future condition at the computation's own
-- return value.  Use this wherever you previously wrote `future e`.
evalFuture :: Pledge eff a -> eff
evalFuture e = future e (ret e)

instance Functor (Pledge eff) where
    -- fmap changes the return type from a to b, so future must become
    -- b -> eff.  We evaluate it at the known original return value and
    -- ignore the new b argument (the obligation is already determined).
    fmap f e = e { ret = f (ret e), future = \_ -> future e (ret e) }

instance Composable eff => Applicative (Pledge eff) where
    pure x = Pledge
        { ret    = x
        , pre    = universe
        , post   = empty
        , future = const universe
        }
    ef <*> ex = Pledge
        { ret    = ret ef (ret ex)
        -- Traditional precondition: pre of ef, plus whatever of pre ex
        -- is not already discharged by post ef.
        , pre    = pre ef /\ (post ef \\ pre ex)
        , post   = post ef <> post ex
        -- future ef and future ex are each applied to their own return
        -- values before the obligation is propagated.
        , future = \_ -> (post ex \\ future ef (ret ef)) /\ future ex (ret ex)
        }

instance Composable eff => Monad (Pledge eff) where
    return = pure
    e >>= f = let fe = f (ret e) in Pledge
        { ret    = ret fe
        -- Traditional precondition: pre of e, plus the residual of pre fe
        -- not covered by post e.  Mirrors the Hoare rule:
        --   {P} e {Q},  Q ⊢ P'  ⊢  {P} e >>= f {R}
        , pre    = pre e /\ (post e \\ pre fe)
        , post   = post e <> post fe
        -- future e is evaluated at e's return value; future fe at fe's.
        , future = \_ -> (post fe \\ future e (ret e)) /\ future fe (ret fe)
        }
