{-# LANGUAGE InstanceSigs, GADTs, PostfixOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-} -- For LeftModule and RightModule, and Sigma class instance
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE FlexibleContexts, DataKinds,
    RankNTypes, ScopedTypeVariables,
    -- StandaloneDeriving,
    UnicodeSyntax,
    UndecidableInstances #-}

-- {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module RE (RegExp (..), one, zero, literal, (*), (+), star, (*.), (.*),
language, finite, infinite, nullable,
derivative, derivative',
matches, constant, reversal,
normalize,
similar, dissimilar,
fromSet, RE.fromList, RE.toSet, RE.toList,
fromLang,
partial, partial',
linear,
first, last,
awidth, height, RE.size,
heightAlgebra, sizeAlgebra,
convert,
RE.optional, atLeastOnce, dot,
isZero, KleeneAlgebra) where

import           Common
import           Finite hiding (Zero, One)
import           Prelude hiding ((+), (*), last, map)
import           Data.List as List hiding (last, map)
import           Data.Set as Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Foldable (toList)
import           Data.Pointed
import           Numeric.Additive.Class (Additive, (+), Idempotent, Abelian)
-- import           Numeric.Order.Additive (AdditiveOrder)
import           Numeric.Order.Class
import           Numeric.Algebra.Class (Monoidal, Multiplicative, (*), zero, LeftModule, (.*), RightModule, (*.), Semiring, sumWith)
import           Numeric.Algebra.Unital (Unital, one, pow, productWith)
import           Numeric.Algebra.Involutive
import           Numeric.Semiring.ZeroProduct (ZeroProductSemiring)
import           Numeric.Decidable.Zero
import           Numeric.Dioid.Class

-- α, β ⩴ ∅ | ε | σ | α∣β | α·β | α★   where σ ∈ Σ
data RegExp s where
  Zero ∷                       RegExp s  -- The empty language         -- ℒ(Zero)  = ∅
  One  ∷                       RegExp s  -- The empty string, epsilon  -- ℒ(One)   = {ε}
  Lit  ∷                   s → RegExp s  -- Literal, single symbol     -- ℒ(σ)     = {σ}, for σ ∈ Σ
  (:|) ∷ RegExp s → RegExp s → RegExp s  -- Union, plus, or            -- ℒ(α ∣ β) = ℒ(α) ∪ ℒ(β)
  (:.) ∷ RegExp s → RegExp s → RegExp s  -- Concatenation              -- ℒ(α · β) = ℒ(α) · ℒ(β)
  Star ∷            RegExp s → RegExp s  -- Kleene star, repetition    -- ℒ(α★)    = ℒ(α)★
  deriving (Eq, Read, Ord)

-- TODO coinductive Kleene Algebra http://www.math.ucla.edu/~znorwood/290d.2.14s/papers/Rutten-v1.pdf
-- also A coalgebraic approach to Kleene algebra with tests
data RegExpF s a where
  ZeroF   ∷         RegExpF s a
  OneF    ∷         RegExpF s a
  LitF    ∷     s → RegExpF s a
  UnionF  ∷ a → a → RegExpF s a
  ConcatF ∷ a → a → RegExpF s a
  StarF   ∷     a → RegExpF s a
  deriving Eq -- (Eq, Functor)


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

instance (Ord s) ⇒ Order (RegExp s) where
  -- order = orderOrd
  -- http://www.inf.ed.ac.uk/teaching/courses/inf2a/slides/2014_inf2a_L05_slides.pdf
  -- "
  -- α ≤ β means L(α) ⊆ L(β) (or equivalently α + β = β).
  -- it follows that
  -- αγ + β ≤ γ ⇒ α∗β ≤ γ
  -- β + γα ≤ γ ⇒ βα∗ ≤ γ
  -- "
  -- TODO so does this mean I have language equality instead of structural equality to use now?
  (<~) ∷ RegExp s → RegExp s → Bool
  (<~) α β = α + β == β

-- z + x <= z + y   =   x <= y   =   x + z <= y + z
-- instance (Ord s) ⇒ AdditiveOrder (RegExp s)

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

-- A Kleene algebra is a dioid (idempotent semiring) with star and an annihilator for multiplication
--       ℒ + ℒ ≡ ℒ            -- (+) Idempotent
--       ℒ + ε ≡ ℒ            -- (+) Right identity
--       ε + ℒ ≡ ℒ            -- (+) Left  identity
--       ℒ₀+ℒ₁ ≡ ℒ₁+ℒ₀        -- (+) Commutivity
--  (ℒ₀+ℒ₁)+ℒ₂ ≡ ℒ₀+(ℒ₁+ℒ₂)   -- (+) Associativity
--    (ℒ₀ℒ₁)ℒ₂ ≡ ℒ₀(ℒ₁ℒ₂)     -- (*) Associativity
--          ℒ∅ ≡ ∅            -- (*) Right annihilator
--          ∅ℒ ≡ ∅            -- (*) Left  annihilator
--   ℒ₀(ℒ₁+ℒ₂) ≡ ℒ₀ℒ₁ + ℒ₀ℒ₂  -- Left distributivity
--   (ℒ₁+ℒ₂)ℒ₀ ≡ ℒ₁ℒ₀ + ℒ₂ℒ₀  -- Right distributivity
-- TODO replace these with axioms below
--          ∅★ ≡ ε
--          ε★ ≡ ε
--         ℒ★★ ≡ ℒ★           -- (★) IdempotentFun
-- TODO Arden’s rule: Given an equation of the form X = αX + β, its smallest solution is X = α∗β. What’s more, if  6∈ L(α), this is the only solution. http://www.inf.ed.ac.uk/teaching/courses/inf2a/slides/2014_inf2a_L05_slides.pdf
-- http://events.cs.bham.ac.uk/mgs2012/lectures/StruthSlides.pdf
-- http://hoefner-online.de/home/pdfs_tr/trCS-07-04-Shef.pdf
-- ε + ℒℒ★ ≤ ℒ★             -- star unfold axiom 1 + xx★ ≤ x★
-- ℒ₀+ℒ₁ℒ₂ ≤ ℒ₂ ⇒ ℒ₁ℒ₀ ≤ ℒ₂ -- star induction axiom y + xz ≤ z ⇒ x★y ≤ z
-- and their opposites 1 + x ★x ≤ x ★ y + zx ≤ z ⇒ yx★ ≤ z
-- FIXME: So I need to add the Order, right? Can I move the Definition down here then?
-- N.B. These functions (`star`, `(+)`, and `(*)`) assume they were passed a normalized regular expression.
class (Dioid a, ZeroProductSemiring a) ⇒ KleeneAlgebra a where
  star ∷ a → a

instance (Ord s) ⇒ KleeneAlgebra (RegExp s) where
  -- Kleene star
  star ∷ RegExp s → RegExp s
  star Zero     = One
  star One      = One
  star (Star α) = Star α  -- Idempotence
  star α        = Star α

instance (Show s) ⇒ Show (RegExp s) where
   show Zero     = "∅"
   show One      = "ε"
   show (Lit  σ) = show σ
   show (α :| β) = "(" ++ show α ++ "∣" ++ show β ++ ")"
   show (α :. β) = "(" ++ show α ++ "·" ++ show β ++ ")"
   show (Star α) = "(" ++ show α ++ ")★"

instance Pointed RegExp where
  point ∷ s → RegExp s
  point = Lit

instance Functor RegExp where
  fmap ∷ (s → g) → RegExp s → RegExp g
  fmap _ Zero     = Zero
  fmap _ One      = One
  fmap f (Lit  σ) = Lit (f σ)
  fmap f (α :| β) = fmap f α :| fmap f β
  fmap f (α :. β) = fmap f α :. fmap f β
  fmap f (Star α) = Star (fmap f α)

instance Functor (RegExpF s) where
  fmap ∷ (a → b) → RegExpF s a → RegExpF s b
  fmap _ ZeroF         = ZeroF
  fmap _ OneF          = OneF
  fmap _ (LitF σ)      = LitF σ
  fmap f (UnionF  a b) = UnionF  (f a) (f b)
  fmap f (ConcatF a b) = ConcatF (f a) (f b)
  fmap f (StarF   a)   = StarF   (f a)

instance Applicative RegExp where
  pure ∷ s → RegExp s
  pure = point

  (<*>) ∷ RegExp (a → b) → RegExp a → RegExp b
  (<*>) Zero     _ = Zero
  (<*>) One      _ = One
  (<*>) (Lit  f) γ = fmap f γ
  (<*>) (α :| β) γ = (α <*> γ) :| (β <*> γ)
  (<*>) (α :. β) γ = (α <*> γ) :. (β <*> γ)
  (<*>) (Star α) γ = Star (α <*> γ)

instance Monad RegExp where
  (>>=) ∷ RegExp a → (a → RegExp b) → RegExp b
  (>>=) Zero     _ = Zero
  (>>=) One      _ = One
  (>>=) (Lit  s) f = f s
  (>>=) (α :| β) f = (α >>= f) :| (β >>= f)
  (>>=) (α :. β) f = (α >>= f) :. (β >>= f)
  (>>=) (Star α) f = Star (α >>= f)

instance Foldable RegExp where
  foldMap ∷ (Monoid m) ⇒ (s → m) → RegExp s → m
  foldMap _ Zero     = mempty
  foldMap _ One      = mempty
  foldMap f (Lit  σ) = f σ
  foldMap f (α :| β) = foldMap f α `mappend` foldMap f β
  foldMap f (α :. β) = foldMap f α `mappend` foldMap f β
  foldMap f (Star α) = foldMap f α

instance Traversable RegExp where
  traverse ∷ (Applicative f) ⇒ (s → f g) → RegExp s → f (RegExp g)
  traverse _ Zero     = pure Zero
  traverse _ One      = pure One
  traverse f (Lit  σ) = Lit  <$> f σ
  traverse f (α :| β) = (:|) <$> traverse f α <*> traverse f β
  traverse f (α :. β) = (:.) <$> traverse f α <*> traverse f β
  traverse f (Star α) = Star <$> traverse f α

-- "character class"
fromSet ∷ (Ord s) ⇒ Set s → RegExp s
fromSet = sumWith point

-- "character sequence"
-- Given a list of symbols (a word), turn it into a regular expression which matches the sequence of symbols in said list
fromList ∷ [s] → RegExp s
fromList = productWith point

fromLang ∷ (Ord s) ⇒ [[s]] → RegExp s
fromLang = sumWith RE.fromList

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
awidth = genericLength . RE.toList

-- "star height"
height ∷ RegExp s → ℕ
height Zero     = 0
height One      = 0
height (Lit  _) = 0
height (α :| β) = max (height α) (height β)
height (α :. β) = max (height α) (height β)
height (Star α) = 1 + height α

heightAlgebra ∷ Algebra (RegExpF s) ℕ
heightAlgebra = Algebra heightf
        where heightf ∷ RegExpF s ℕ → ℕ
              heightf ZeroF         = 0
              heightf OneF          = 0
              heightf (LitF  _)     = 0
              heightf (UnionF  α β) = max α β
              heightf (ConcatF α β) = max α β
              heightf (StarF   α)   = 1 + α


-- https://arxiv.org/pdf/0802.2869.pdf
-- "We define the size of an extended regular expression r over Σ, denoted by |r|, as
-- the number of Σ-symbols and operators occurring in r disregarding parentheses. This is
-- equivalent to the length of its (parenthesis-free) reverse Polish form"
size ∷ RegExp s → ℕ
size Zero     = 1
size One      = 1
size (Lit  _) = 1
size (α :| β) = 1 + RE.size α + RE.size β
size (α :. β) = 1 + RE.size α + RE.size β
size (Star α) = 1 + RE.size α

-- TODO if this is unambiguous it can be written `φ` instead of `sizef`? https://wiki.haskell.org/Catamorphisms
sizeAlgebra ∷ Algebra (RegExpF s) ℕ
sizeAlgebra = Algebra sizef
        where sizef ∷ RegExpF s ℕ → ℕ
              sizef ZeroF         = 1
              sizef OneF          = 1
              sizef (LitF _)      = 1
              sizef (UnionF  α β) = 1 + α + β
              sizef (ConcatF α β) = 1 + α + β
              sizef (StarF   α)   = 1 + α

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
language γ | RE.finite γ' = Set.toList (language' γ')
           | otherwise    = Prelude.filter (matches γ') (sigmaStar γ')
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
           language' (α :. β) = foldMap (\w₁ → (Set.map (\w₂ → w₁ ++ w₂) (language' β))) (language' α)
           -- ℒ(E★)  = (ℒ(E))★  -- Providing this comment for completeness but this case is impossible
           language' (Star _) = impossible -- if the RegExp is normalized and finite then this case is impossible!

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

-- "Antimirov [2] proposed the notion of partial derivative, which is a nondeterministic
-- version of the Brzozowski derivative. Instead of a deterministic finite automaton, the
-- partial derivative leads to a construction of a nondeterministic finite automaton"
-- -- http://www.dcc.fc.up.pt/~nam/web/resources/rafaelamsc.pdf 3.3 (pg. 20)
partial ∷ (Eq s, Ord s) ⇒ RegExp s → s → Set (RegExp s)
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
reversal ∷ (Ord s) ⇒ RegExp s → RegExp s
reversal Zero     = zero
reversal One      = one
reversal (Lit  σ) = literal σ
reversal (α :| β) = reversal α + reversal β
reversal (α :. β) = reversal β * reversal α
reversal (Star α) = star (reversal α)
