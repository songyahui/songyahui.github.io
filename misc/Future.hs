{-# LANGUAGE FunctionalDependencies #-}

module Future where

import Prelude hiding ((<>))

-- ── Terms ─────────────────────────────────────────────────────────────────────

data Term = Var String | Str String | Num Int
    deriving (Eq)

instance Show Term where
    show (Var s) = s
    show (Str s) = "\"" ++ s ++ "\""
    show (Num n) = show n

-- ── Events ────────────────────────────────────────────────────────────────────

-- An Event is either a concrete named call or a wildcard pattern (Σ).
-- Wildcard is used only inside RE patterns (Single Wildcard ≡ Σ, any one step).
data Event = Atom String [Term]  -- e.g. send(x)
           | Wildcard            -- matches any single event
    deriving (Eq)

instance Show Event where
    show (Atom name args) = name ++ "(" ++ concatMap show args ++ ")"
    show Wildcard         = "_"

-- Does a concrete event occurrence match an event pattern in a Single?
matchEvent :: Event -> Event -> Bool
matchEvent _            Wildcard      = True   -- any occurrence matches wildcard pattern
matchEvent (Atom n1 a1) (Atom n2 a2) = n1 == n2 && a1 == a2
matchEvent Wildcard     (Atom _ _)   = False   -- wildcard occurrence ≠ specific pattern

-- ── Regular Expressions ───────────────────────────────────────────────────────

data RE
    = Bot          -- ∅         empty language
    | Epsilon      -- ε         empty word
    | Single Event -- a         single-event pattern
    | Seq RE RE    -- r₁ · r₂   concatenation
    | Or  RE RE    -- r₁ + r₂   union
    | And RE RE    -- r₁ ∩ r₂   intersection  (= ¬(¬r₁ + ¬r₂))
    | Star RE      -- r*        Kleene star
    | Not RE       -- ¬r        complement
    deriving (Eq)

instance Show RE where
    show Bot         = "∅"
    show Epsilon     = "ε"
    show (Single e)  = show e
    show (Seq r1 r2) = "(" ++ show r1 ++ ") · (" ++ show r2 ++ ")"
    show (Or  r1 r2) = "(" ++ show r1 ++ ") ∨ (" ++ show r2 ++ ")"
    show (And r1 r2) = "(" ++ show r1 ++ ") ∧ (" ++ show r2 ++ ")"
    show (Star r)    = "(" ++ show r ++ ")*"
    show (Not r)     = "¬(" ++ show r ++ ")"

-- Σ* — universal language, complement of the empty language
anything :: RE
anything = Not Bot

-- ── Nullability: ν(r) ─────────────────────────────────────────────────────────
-- ν(r) = True  iff  ε ∈ L(r)

nullable :: RE -> Bool
nullable Bot          = False
nullable Epsilon      = True
nullable (Single _)   = False
nullable (Seq r1 r2)  = nullable r1 && nullable r2
nullable (Or  r1 r2)  = nullable r1 || nullable r2
nullable (And r1 r2)  = nullable r1 && nullable r2
nullable (Star _)     = True
nullable (Not r)      = not (nullable r)   -- ν(¬r) = ¬ν(r)

-- ── Brzozowski Derivative: ∂_e(r) ────────────────────────────────────────────
-- Key law for complement: ∂_a(¬r) = ¬(∂_a(r))

derivative :: Event -> RE -> RE
derivative _ Bot          = Bot
derivative _ Epsilon      = Bot
derivative e (Single p)   = if matchEvent e p then Epsilon else Bot
derivative e (Seq r1 r2)
    | nullable r1           = Or (Seq (derivative e r1) r2) (derivative e r2)
    | otherwise             = Seq (derivative e r1) r2
derivative e (Or  r1 r2)  = Or  (derivative e r1) (derivative e r2)
derivative e (And r1 r2)  = And (derivative e r1) (derivative e r2)
derivative e (Star r)     = Seq (derivative e r) (Star r)
derivative e (Not r)      = Not (derivative e r)   -- ∂_a(¬r) = ¬(∂_a(r))

-- ── First Set ─────────────────────────────────────────────────────────────────
-- Events that can begin a word in L(r); drives the subtraction algorithm.

first :: RE -> [Event]
first Bot          = []
first Epsilon      = []
first (Single e)   = [e]
first (Seq r1 r2)  = if nullable r1 then first r1 ++ first r2 else first r1
first (Or  r1 r2)  = first r1 ++ first r2
first (And r1 r2)  = [e | e <- first r1, e `elem` first r2]
first (Star r)     = first r
first (Not r)      = first r   -- approximation: explore same alphabet as inner r

-- ── LTL ───────────────────────────────────────────────────────────────────────

data LTL
    = LTLTrue
    | LTLFalse
    | LTLAtom     Event
    | LTLNot      LTL
    | LTLAnd      LTL LTL
    | LTLOr       LTL LTL
    | LTLNext     LTL          -- X φ        (strong next)
    | LTLUntil    LTL LTL      -- φ U ψ
    | LTLFinally  LTL          -- F φ  ≜  ⊤ U φ   ≡  Σ* · ⟦φ⟧
    | LTLGlobally LTL          -- G φ  ≜  ¬F¬φ    ≡  ¬(Σ* · ¬⟦φ⟧)
    deriving (Eq, Show)

-- Algebraic translation LTLf → RE (no automaton construction needed).
-- Complement is handled by the Not constructor directly.
ltl_to_re :: LTL -> RE
ltl_to_re LTLTrue            = anything                              -- ¬∅  = Σ*
ltl_to_re LTLFalse           = Bot                                   -- ∅
ltl_to_re (LTLAtom e)        = Single e
ltl_to_re (LTLNot l)         = Not (ltl_to_re l)                    -- ¬⟦l⟧
ltl_to_re (LTLAnd l1 l2)     = And (ltl_to_re l1) (ltl_to_re l2)   -- ⟦l1⟧ ∩ ⟦l2⟧
ltl_to_re (LTLOr  l1 l2)     = Or  (ltl_to_re l1) (ltl_to_re l2)   -- ⟦l1⟧ ∪ ⟦l2⟧
ltl_to_re (LTLNext l)        = Seq (Single Wildcard) (ltl_to_re l)  -- Σ · ⟦l⟧
ltl_to_re (LTLUntil l1 l2)   = Seq (Star (ltl_to_re l1))           -- ⟦l1⟧* · ⟦l2⟧
                                    (ltl_to_re l2)
ltl_to_re (LTLFinally l)     = Seq anything (ltl_to_re l)           -- Σ* · ⟦l⟧
ltl_to_re (LTLGlobally l)    = Not (Seq anything                    -- ¬(Σ* · ¬⟦l⟧)
                                        (Not (ltl_to_re l)))

-- ── Shorthands ────────────────────────────────────────────────────────────────

-- G ev  — ev must occur at every step:  ev*
globally :: Event -> RE
globally ev = Star (Single ev)

-- F ev  — ev must occur at some step:  Σ* · ev · Σ*
finally :: Event -> RE
finally ev = Seq anything (Seq (Single ev) anything)

-- Σ* (alias, for use as a trivially-satisfied future condition)
reTrue :: RE
reTrue = anything

-- ── Composable class ──────────────────────────────────────────────────────────

type Trace      = RE
type FutureCond = RE

class Composable a where
    concatenation :: a -> a -> a
    conjunction   :: a -> a -> a
    empty         :: a
    universe      :: a
    subtraction   :: a -> a -> a
    normalize     :: a -> a

infixl 6 <>
(<>) :: Composable a => a -> a -> a
(<>) = concatenation

infixl 7 /\
(/\) :: Composable a => a -> a -> a
(/\) = conjunction

infixl 5 \\
(\\) :: Composable a => a -> a -> a
(\\) = subtraction

instance Composable RE where
    concatenation = Seq
    conjunction   = And
    empty         = Epsilon
    universe      = anything

    -- Quotient r1 \ r2: the residual future obligation in r2 after trace r1.
    -- Base: if r1 = ε (nothing consumed), r2 is unchanged.
    -- Σ* (Not Bot) trivially satisfies any precondition: residual is ε.
    subtraction Epsilon   r2 = r2
    subtraction (Not Bot) _  = Epsilon
    subtraction r1 r2 =
        let evts   = first r1
            step e = subtraction (normalize (derivative e r1))
                                 (normalize (derivative e r2))
        in foldr Or Bot (map step evts)

    -- Normalization: simplify using RE algebra + De Morgan laws for Not.
    normalize r = case r of

        Seq r1 r2 -> case (normalize r1, normalize r2) of
            (Bot, _)      -> Bot
            (_, Bot)      -> Bot
            (Epsilon, r') -> r'
            (r', Epsilon) -> r'
            (r1', r2')    -> Seq r1' r2'

        Or r1 r2 -> case (normalize r1, normalize r2) of
            (Bot, r')        -> r'
            (r', Bot)        -> r'
            (r1', r2')
                | r1' == r2'  -> r1'
                | isUniv r1'  -> anything
                | isUniv r2'  -> anything
            (r1', r2')       -> Or r1' r2'

        And r1 r2 -> case (normalize r1, normalize r2) of
            (Bot, _)         -> Bot
            (_, Bot)         -> Bot
            (r1', r2')
                | r1' == r2'  -> r1'
                | isUniv r1'  -> r2'
                | isUniv r2'  -> r1'
            (Epsilon, r')    -> if nullable r' then Epsilon else Bot
            (r', Epsilon)    -> if nullable r' then Epsilon else Bot
            (r1', r2')       -> And r1' r2'

        -- Complement: involution + De Morgan laws
        Not r1 -> case normalize r1 of
            Not r'       -> r'                                    -- ¬¬r = r
            Or  r1' r2'  -> normalize (And (Not r1') (Not r2'))  -- De Morgan
            And r1' r2'  -> normalize (Or  (Not r1') (Not r2'))  -- De Morgan
            Bot          -> anything                              -- ¬∅  = Σ*
            r' | isUniv r' -> Bot                                -- ¬Σ* = ∅
            r'             -> Not r'

        Star r1 -> case normalize r1 of
            Bot     -> Epsilon   -- ∅* = ε
            Epsilon -> Epsilon   -- ε* = ε
            r'      -> Star r'

        _ -> r
      where
        isUniv (Not Bot) = True
        isUniv _         = False

-- ── Effectful monad ───────────────────────────────────────────────────────────

data Effectful eff a = Effectful
    { ret    :: a
    , pre    :: eff
    , post   :: eff
    , future :: eff
    }

instance Functor (Effectful eff) where
    fmap f e = e { ret = f (ret e) }

instance Composable eff => Applicative (Effectful eff) where
    pure x = Effectful
        { ret    = x
        , pre    = universe
        , post   = empty
        , future = universe
        }
    ef <*> ex = Effectful
        { ret    = ret ef (ret ex)
        -- Traditional precondition: pre of ef, plus whatever of pre ex
        -- is not already discharged by post ef.
        -- If post ef ⊢ pre ex, the quotient is ε and nothing is added.
        , pre    = pre ef <> (pre ex \\ post ef)
        , post   = post ef <> post ex
        , future = (post ex \\ future ef) /\ future ex
        }

instance Composable eff => Monad (Effectful eff) where
    return = pure
    e >>= f = let fe = f (ret e) in Effectful
        { ret    = ret fe
        -- Traditional precondition: pre of e, plus the residual of pre fe
        -- not covered by post e.  Mirrors the Hoare rule:
        --   {P} e {Q},  Q ⊢ P'  ⊢  {P} e >>= f {R}
        -- When post e fully satisfies pre fe, pre fe \\ post e = ε.
        , pre    = pre e <> (pre fe \\ post e)
        , post   = post e <> post fe
        , future = (post fe \\ future e) /\ future fe
        }
