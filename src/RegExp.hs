{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# OPTIONS_GHC -Wall                  #-}

module RegExp (RegExp (..), one, zero, literal, (*), (+), star, (*.), (.*),
language, finite, infinite, nullable,
derivative, derivative', derivatives,
matches, constant, reversal,
normalize,
similar, dissimilar, equivalent,
fromSet, RegExp.fromList, RegExp.toSet, RegExp.toList,
fromWords, toLanguage,
partial, partial',
linear,
first, last,
awidth, height, RegExp.size,
heightAlgebra, sizeAlgebra, languageAlg,
convert,
RegExp.optional, atLeastOnce, dot,
isZero, KleeneAlgebra) where

import           Common
import           Finite
import qualified Language
import           Prelude hiding ((+), (*), last, map)
import           Control.Monad
import           Data.List as List hiding (last, map)
import           Data.Set as Set hiding ((\\))
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Ord.Unicode
import           Data.Foldable (toList)
import           Data.Functor.Foldable (Fix (..))
import           Data.Pointed
import           Numeric.Natural.Unicode
import           Numeric.Additive.Class (Additive, (+), Idempotent, Abelian)
import           Numeric.Order.Class
import           Numeric.Algebra.Class (Monoidal, Multiplicative, (*), zero, LeftModule, (.*), RightModule, (*.), Semiring, sumWith)
import           Numeric.Algebra.Unital (Unital, one, pow, productWith)
import           Numeric.Algebra.Involutive
import           Numeric.Semiring.ZeroProduct (ZeroProductSemiring)
import           Numeric.Decidable.Zero
import           Numeric.Dioid.Class
import           GHC.Generics

-- α, β ⩴ ∅ | ε | σ | α∣β | α·β | α★  where σ ∈ Σ
data RegExp s where
  Zero ∷                       RegExp s  -- The empty language         -- ℒ(Zero)  = ∅
  One  ∷                       RegExp s  -- The empty string, epsilon  -- ℒ(One)   = {ε}
  Lit  ∷                   s → RegExp s  -- Literal, single symbol     -- ℒ(σ)     = {σ}, for σ ∈ Σ
  (:|) ∷ RegExp s → RegExp s → RegExp s  -- Union, plus, or            -- ℒ(α ∣ β) = ℒ(α) ∪ ℒ(β)
  (:.) ∷ RegExp s → RegExp s → RegExp s  -- Concatenation              -- ℒ(α · β) = ℒ(α) · ℒ(β)
  Star ∷            RegExp s → RegExp s  -- Kleene star, repetition    -- ℒ(α★)    = ℒ(α)★
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic1)

-- TODO coinductive Kleene Algebra http://www.math.ucla.edu/~znorwood/290d.2.14s/papers/Rutten-v1.pdf
-- also A coalgebraic approach to Kleene algebra with tests
data RegExpF s a where
  ZeroF   ∷         RegExpF s a
  OneF    ∷         RegExpF s a
  LitF    ∷     s → RegExpF s a
  UnionF  ∷ a → a → RegExpF s a
  ConcatF ∷ a → a → RegExpF s a
  StarF   ∷     a → RegExpF s a
  deriving (Eq, Functor)

instance (Finite s) ⇒ Σ (RegExp s) s
instance (Finite s) ⇒ Σ (RegExpF s a) s

-- Added for consistency
literal ∷ s → RegExp s
literal = Lit

-- A multiplicative semigroup
instance Multiplicative (RegExp s) where
  (*) ∷ RegExp s → RegExp s → RegExp s
  -- Annihilation
  _        * Zero = Zero
  Zero     *    _ = Zero
  -- Identity
  α        *  One = α
  One      *    β = β
  -- Associativity
  -- Associate to the right in normal form, creating a list
  (α :. β) *    γ = α :. (β * γ)
  α        *    β = α :. β

-- A multiplicative monoid
instance Unital (RegExp s) where
  one = One

instance (Ord s) ⇒ InvolutiveMultiplication (RegExp s) where
  adjoint = reversal

-- An Additive semigroup
instance (Ord s) ⇒ Additive (RegExp s) where
  (+) ∷ RegExp s → RegExp s → RegExp s
  -- Identity
  α        +     Zero             = α
  Zero     +        β             = β
  -- Associativity
  -- Associate to the right in normal form, creating a list
  (α :| β) +        γ             = α + (β + γ)
  -- Sort the list to account for commutivity (and also make idempotence easy to process)
  α        + (β :| γ) | α == β    = β :| γ         -- Idempotence
                      | α <= β    = α :| (β :| γ)
                      | otherwise = β :| α + γ     -- Commutivity
  α        +        β | α == β    = α              -- Idempotence
                      | α <= β    = α :| β
                      | otherwise = β :| α         -- Commutivity

-- An additive semigroup with idempotent addition.
-- a + a = a
instance (Ord s) ⇒ Idempotent (RegExp s) where

-- A partial order (a, ≤)
-- TODO With respect to ≤, K is an upper semilattice with join given by + and minimum element 0.
instance (Ord s) ⇒ Order (RegExp s) where
  (<~) ∷ RegExp s → RegExp s → Bool
  (<~) α β = α + β == β

-- An additive Abelian semigroup
-- a + b = b + a
instance (Ord s) ⇒ Abelian (RegExp s) where

-- A pair of an additive abelian semigroup, and a multiplicative semigroup, with the distributive laws
instance (Ord s) ⇒ Semiring (RegExp s) where

instance (Ord s) ⇒ LeftModule  ℕ (RegExp s) where
  (.*) = flip pow
instance (Ord s) ⇒ RightModule ℕ (RegExp s) where
  (*.) = pow

-- An additive semigroup with an identity element
instance (Ord s) ⇒ Monoidal (RegExp s) where
  zero = Zero

instance (Ord s) ⇒ DecidableZero (RegExp s) where
  -- Given a Regular Expression, r, decide if it produces the empty language, i.e.
  -- ℒ(r) ≟ ∅
  isZero ∷ RegExp s → Bool
  isZero = isZero' . normalize
     where isZero' Zero     = True
           isZero' One      = False
           isZero' (Lit  _) = False
           isZero' (α :| β) = isZero' α ∧ isZero' β
           isZero' (α :. β) = isZero' α ∨ isZero' β
           isZero' (Star _) = False

-- A zero-product semiring has no zero divisors
-- a * b = 0 implies a == 0 || b == 0
-- For a Kleene Algebra the annihilator wrt multiplication is ∅
instance (Ord s) ⇒ ZeroProductSemiring (RegExp s) where

-- infixl 6 + (Numeric.Additive.Class)
-- infixl 7 * (Numeric.Algebra.Class)
infixr 8 `star`  -- Numeric.Exp?

-- A Kleene algebra is an algebraic structure K = (k, +, ∙, ★, 0, 1)
-- satisfying the following equations and equational implications:
--  (α + β) + γ = α + (β + γ)  -- (+) Associativity
--        α + β = β + α        -- (+) Commutivity
--        α + 0 = α            -- (+) Right identity
--        0 + α = α            -- (+) Left  identity
--        α + α = α            -- (+) Idempotent
--        (αβ)γ = α(βγ)        -- (∙) Associativity
--           1α = α            -- (∙) Left identity
--           α1 = α            -- (∙) Right identity
--     α(β + γ) = αβ + αγ      -- Left distributivity
--     (β + γ)α = βα + γα      -- Right distributivity
--           0α = 0            -- (∙) Left  annihilator
--           α0 = 0            -- (∙) Right annihilator
--      1 + αα★ ≤ α★           -- (★) Unfold
--      1 + α★α ≤ α★           -- (★) Unfold
--   β + αγ ≤ γ ⇒ α★β ≤ γ      -- (★) Induction
--   β + γα ≤ γ ⇒ βα★ ≤ γ      -- (★) Induction
-- where ≤ refers to the natural partial order on K:
--      (α ≤ β) ↔ (α + β) = β
-- A Completeness Theorem for Kleene Algebras and
-- the Algebra of Regular Events
-- Kozen
-- https://www.cs.cornell.edu/~kozen/Papers/ka.pdf

-- N.B. These functions (`star`, `(+)`, and `(*)`) assume they were passed already normalized regular expressions.
class (Dioid a, ZeroProductSemiring a, Order a) ⇒ KleeneAlgebra a where
  star ∷ a → a

instance (Ord s) ⇒ KleeneAlgebra (RegExp s) where
  -- Kleene star
  star ∷ RegExp s → RegExp s
  star Zero     = One
  star One      = One
  star (Star α) = Star α  -- Idempotence
  star α        = Star α

instance (Show s) ⇒ Show (RegExp s) where
  showsPrec ∷ Show s ⇒ Int → RegExp s → ShowS
  showsPrec _          Zero     = showChar '∅'
  showsPrec _          One      = showChar 'ε'
  showsPrec _          (Lit  σ) = shows σ
  showsPrec precedence (α :| β) = showParen (precedence ≥ 6) (showsPrec 6 α . showChar '∣' . showsPrec 6 β)
  showsPrec precedence (α :. β) = showParen (precedence ≥ 7) (showsPrec 7 α . showChar '·' . showsPrec 7 β)
  showsPrec precedence (Star α) = showParen (precedence ≥ 8) (showsPrec 8 α . showChar '★')

instance Pointed RegExp where
  point ∷ s → RegExp s
  point = Lit

instance Applicative RegExp where
  pure ∷ s → RegExp s
  pure = return

  (<*>) ∷ RegExp (a → b) → RegExp a → RegExp b
  (<*>) = ap

instance Monad RegExp where
  return ∷ s → RegExp s
  return = point

  (>>=) ∷ RegExp a → (a → RegExp b) → RegExp b
  (>>=) Zero     _ = Zero
  (>>=) One      _ = One
  (>>=) (Lit  s) f = f s
  (>>=) (α :| β) f = (α >>= f) :| (β >>= f)
  (>>=) (α :. β) f = (α >>= f) :. (β >>= f)
  (>>=) (Star α) f = Star (α >>= f)

-- "character class"
fromSet ∷ (Ord s) ⇒ Set s → RegExp s
fromSet = sumWith point

-- "character sequence"
-- Given a list of symbols (a word), turn it into a regular expression which matches the sequence of symbols in said list
fromList ∷ [s] → RegExp s
fromList = productWith point

fromWords ∷ (Ord s) ⇒ [[s]] → RegExp s
fromWords = sumWith RegExp.fromList

-- "occurences"
-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.56.3425&rep=rep1&type=pdf pg 46. def 4.57
toSet ∷ (Ord s) ⇒ RegExp s → Set s
toSet = foldMap singleton

-- Inorder traversal of the RegExp tree, putting all the literals into a list
toList ∷ RegExp s → [s]
toList = Data.Foldable.toList

-- typically written α? for some regular expression α
optional ∷ (Ord s) ⇒    RegExp s → RegExp s
optional α = α + One

-- The positive star of α, α⁺
atLeastOnce ∷ (Ord s) ⇒ RegExp s → RegExp s
atLeastOnce α = α * star α

-- "wildcard"
-- matches any literal of Σ exactly once
-- This is usually denoted by `.`, or `Σ`
dot ∷ (Finite s) ⇒ RegExp s
dot = fromSet asSet

-- alphabetic width is the total number (with multiplicitiy) of alphabetic symbols from Σ
awidth ∷ RegExp s → ℕ
awidth = genericLength . RegExp.toList

-- "star height"
height ∷ RegExp s → ℕ
height Zero     = 0
height One      = 0
height (Lit  _) = 0
height (α :| β) = max (height α) (height β)
height (α :. β) = max (height α) (height β)
height (Star α) = 1 + height α

heightAlgebra ∷ Algebra (RegExpF s) ℕ
heightAlgebra = Algebra φ
        where φ ∷ RegExpF s ℕ → ℕ
              φ ZeroF         = 0
              φ OneF          = 0
              φ (LitF  _)     = 0
              φ (UnionF  α β) = max α β
              φ (ConcatF α β) = max α β
              φ (StarF   α)   = 1 + α

-- https://arxiv.org/pdf/0802.2869.pdf
-- "We define the size of an extended regular expression r over Σ, denoted by |r|, as
-- the number of Σ-symbols and operators occurring in r disregarding parentheses. This is
-- equivalent to the length of its (parenthesis-free) reverse Polish form"
size ∷ RegExp s → ℕ
size Zero     = 1
size One      = 1
size (Lit  _) = 1
size (α :| β) = 1 + RegExp.size α + RegExp.size β
size (α :. β) = 1 + RegExp.size α + RegExp.size β
size (Star α) = 1 + RegExp.size α

sizeAlgebra ∷ Algebra (RegExpF s) ℕ
sizeAlgebra = Algebra φ
        where φ ∷ RegExpF s ℕ → ℕ
              φ ZeroF         = 1
              φ OneF          = 1
              φ (LitF _)      = 1
              φ (UnionF  α β) = 1 + α + β
              φ (ConcatF α β) = 1 + α + β
              φ (StarF   α)   = 1 + α

-- Associativity, commutativity and idempotency (ACI) properties normalized
-- Note:  ℒ(γ) ≡ ℒ(normalize γ)
normalize ∷ (Ord s) ⇒ RegExp s → RegExp s
normalize Zero     = zero
normalize One      = one
normalize (Lit  σ) = literal σ
normalize (α :| β) = normalize α + normalize β
normalize (α :. β) = normalize α * normalize β
normalize (Star α) = star (normalize α)

-- ACI-similar
similar ∷ (Eq s, Ord s) ⇒    RegExp s → RegExp s → Bool
similar a b = normalize a == normalize b

dissimilar ∷ (Eq s, Ord s) ⇒ RegExp s → RegExp s → Bool
dissimilar a b = not (similar a b)

equivalent ∷ ∀ s . (Finite s) ⇒ RegExp s → RegExp s → Bool
equivalent a b = and (unfoldr bisim seed)
      where seed = ([(normalize a, normalize b)], [])
            bisim ∷ (Finite s)
                  ⇒ ([(RegExp s, RegExp s)], [(RegExp s, RegExp s)])
                  → Maybe (Bool, ([(RegExp s, RegExp s)], [(RegExp s, RegExp s)]))
            bisim ([],            _      ) = Nothing
            bisim ((α, β) : todo, history) = Just (nullable α == nullable β, (todo', history'))
                                      where derivatives' = fmap (\σ → (derivative α σ, derivative β σ)) asList
                                            todo'        = (todo `mappend` derivatives') \\ history
                                            history'     = (α, β) : history

-- Return true iff every symbol σ ∈ Σ is seen as a literal at most once
-- TODO test property that for any RE, r, `linear (mark r)` should evaluate to `true`
linear ∷ (Ord s) ⇒ RegExp s → Bool
linear = snd . linear' (∅)
    where linear' ∷ (Ord s) ⇒ Set.Set s → RegExp s → (Set.Set s, Bool)
          linear' s Zero     = (s,              True)
          linear' s One      = (s,              True)
          linear' s (Lit  σ) = (Set.insert σ s, σ ∉ s)
          linear' s (α :| β) = (s'',            res' && res'')
                         where (s',             res')          = linear' s  α
                               (s'',            res'')         = linear' s' β
          linear' s (α :. β) = (s'',            res' && res'')
                         where (s',             res')          = linear' s  α
                               (s'',            res'')         = linear' s' β
          linear' s (Star α) = linear' s α

-- first(E) = { a | av ∈ ℒ(E) }
first ∷ (Ord s) ⇒ RegExp s → Set.Set s
first Zero                  = (∅)
first One                   = (∅)
first (Lit  σ)              = Set.singleton σ
first (α :| β)              = first α ∪ first β
first (α :. β) | nullable α = first α ∪ first β
               | otherwise  = first α
first (Star α)              = first α

-- last(E) = { a | va ∈ ℒ(E) }
last ∷ (Ord s) ⇒ RegExp s → Set.Set s
last Zero                  = (∅)
last One                   = (∅)
last (Lit  σ)              = Set.singleton σ
last (α :| β)              = last α ∪ last β
last (α :. β) | nullable β = last α ∪ last β
              | otherwise  = last β
last (Star α)              = last α

-- Lazily generate the entire language of the given Regular Expression.
-- Mathematically, this is defined as a Set,
-- however, Data.Set does not support lazy infinite sets.
language ∷ (Finite s) ⇒ RegExp s → [[s]]
language γ | RegExp.finite γ' = Set.toList (language' γ')
           | otherwise        = Prelude.filter (matches γ') (sigmaStar γ')
     where γ' = normalize γ
           language'  ∷ (Finite s) ⇒ RegExp s → Set [s]
           -- The empty language
           language' Zero     = (∅)
           -- The language consisting of the empty string,     {ε}
           language' One      = Set.singleton []
           -- The language consisting of a literal symbol,     {σ}, for σ ∈ Σ
           language' (Lit  σ) = Set.singleton [σ]
           -- ℒ(E ∣ F) = ℒ(E) ∪ ℒ(F)
           language' (α :| β) = language' α ∪ language' β
           -- ℒ(E · F) = ℒ(E) · ℒ(F) = { w₁ · w₂ | w₁ ∈ ℒ(E) ∧ w₂ ∈ ℒ(F) }
           language' (α :. β) = foldMap (\w₁ → Set.map (\w₂ → w₁ ++ w₂) (language' β)) (language' α)
           -- ℒ(E★)  = (ℒ(E))★  -- Providing this comment for completeness but this case is impossible
           language' (Star _) = impossible -- if the RegExp is normalized and finite then this case is impossible!

toLanguage ∷ (Finite s) ⇒ RegExp s → Language.ℒ s
toLanguage Zero     = Language.empty
toLanguage One      = Language.epsilon
toLanguage (Lit  σ) = Language.lit σ
toLanguage (α :| β) = Language.union       (toLanguage α) (toLanguage β)
toLanguage (α :. β) = Language.concatenate (toLanguage α) (toLanguage β)
toLanguage (Star α) = Language.star        (toLanguage α)

languageAlg ∷ (Eq s) ⇒ Algebra (RegExpF s) (Language.ℒ s)
languageAlg = Algebra φ
      where φ ∷ (Eq s) ⇒ RegExpF s (Language.ℒ s) → Language.ℒ s
            φ ZeroF         = Language.empty
            φ OneF          = Language.epsilon
            φ (LitF σ)      = Language.lit σ
            φ (UnionF  α β) = Language.union α β
            φ (ConcatF α β) = Language.concatenate α β
            φ (StarF α)     = Language.star α

convert ∷ (Ord s) ⇒ RegExp s → Fix (RegExpF s)
convert Zero     = Fix ZeroF
convert One      = Fix OneF
convert (Lit  σ) = Fix (LitF σ)
convert (α :| β) = Fix (UnionF  (convert α) (convert β))
convert (α :. β) = Fix (ConcatF (convert α) (convert β))
convert (Star α) = Fix (StarF   (convert α))

finite ∷ (Ord s) ⇒ RegExp s → Bool
finite = finite' . normalize
   where finite' Zero     = True
         finite' One      = True
         finite' (Lit  _) = True
         finite' (α :| β) = finite' α ∧ finite' β
         finite' (α :. β) = finite' α ∧ finite' β
         finite' (Star _) = False

infinite ∷ (Ord s) ⇒ RegExp s → Bool
infinite = not . finite

-- decide if the language defined by r contains ε, i.e.
-- nullable (r) ⇔ ε ∈ ℒ(r)
-- Also know as Salomaa's Empty Word Property (EWP)
nullable ∷ (Ord s) ⇒ RegExp s → Bool
nullable = nullable' . normalize
  where nullable' Zero     = False
        nullable' One      = True
        nullable' (Lit  _) = False
        nullable' (α :| β) = nullable' α ∨ nullable' β
        nullable' (α :. β) = nullable' α ∧ nullable' β
        nullable' (Star _) = True

-- https://people.mpi-sws.org/~turon/re-deriv.pdf
-- Theorem 3.1, helper function, "v(r)".
constant ∷ (Ord s) ⇒ RegExp s → RegExp s
constant α | nullable α = One
           | otherwise  = Zero

-- Brzozowski ∂ with respect to σ ∈ Σ
derivative ∷ (Ord s) ⇒ RegExp s → s → RegExp s
derivative Zero     _ = zero
derivative One      _ = zero
derivative (Lit σ') σ = if σ' == σ then one else zero
derivative (α :| β) σ =  derivative α σ + derivative β σ
derivative (α :. β) σ = (derivative α σ * β) + (constant α * derivative β σ)
derivative (Star α) σ =  derivative α σ * star α

-- Brzozowski ∂ extended to strings
-- "The derivative of a language ℒ ⊆ Σ★ with respect to a string w ∈ Σ★ is defined to be ∂w ℒ = { v | w · v ∈ ℒ }."
derivative' ∷ (Ord s) ⇒ RegExp s → [s] → RegExp s
derivative' = List.foldl derivative

derivatives ∷ (Finite s) ⇒ RegExp s → Set (RegExp s)
derivatives a = map (derivative a) asSet

-- "Antimirov [2] proposed the notion of partial derivative, which is a nondeterministic
-- version of the Brzozowski derivative. Instead of a deterministic finite automaton, the
-- partial derivative leads to a construction of a nondeterministic finite automaton"
-- -- http://www.dcc.fc.up.pt/~nam/web/resources/rafaelamsc.pdf 3.3 (pg. 20)
partial ∷ (Ord s) ⇒ RegExp s → s → Set (RegExp s)
partial Zero     _              = (∅)
partial One      _              = (∅)
partial (Lit σ') σ | σ' == σ    = singleton One
                   | otherwise  = (∅)
partial (α :| β) σ              =                 partial α σ  ∪ partial β σ
partial (α :. β) σ | nullable α = map (* β)      (partial α σ) ∪ partial β σ
                   | otherwise  = map (* β)      (partial α σ)
partial (Star α) σ              = map (* star α) (partial α σ)

-- FIXME need to test
-- http://www.dcc.fc.up.pt/~nam/web/resources/rafaelamsc.pdf pg 41
partial' ∷ (Ord s) ⇒ RegExp s → [s] → Set (RegExp s)
partial' = List.foldl (foldMap partial) . singleton

-- Given a Regular Expression α, and a string w, determine if w matches α, i.e.
-- w ∈ ℒ(α)
matches ∷ (Ord s) ⇒ RegExp s → [s] → Bool
matches Zero       _ = False
matches α         [] = constant α == One
matches α    (a : w) = matches (derivative α a) w

-- automorphism -- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.50.7458&rep=rep1&type=pdf
reversal ∷ RegExp s → RegExp s
reversal Zero     = Zero
reversal One      = One
reversal (Lit  σ) = Lit σ
reversal (α :| β) = reversal α :| reversal β
reversal (α :. β) = reversal β :. reversal α
reversal (Star α) = Star (reversal α)
