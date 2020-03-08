{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExplicitForAll             #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}

module Finite where

import           Data.Set as Set
import           Data.Set.Unicode ((∅))
import           Data.Set.Ordered (OSet)
import qualified Data.Set.Ordered as OSet
import           Data.Foldable.Unicode ((∈), (∋))
import           Data.Eq.Unicode ((≠))
import           Data.Bool.Unicode ((∧), (∨))
import           Control.Monad
import           Control.Applicative
import           Data.Group (Group, invert)
import           Data.List as List
import           Data.List.NonEmpty (NonEmpty, NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import           Data.Maybe (fromJust)
import           Data.These (These, These(..), these)
import           Data.These.Combinators (catThese)
import           Data.Void (Void, absurd)
import qualified Data.Foldable as F
import           Data.Function (on)
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible (Decidable, Divisible, divide, conquer, choose, lose)
import           Common
import           GHC.Enum (boundedEnumFrom)
import           Data.Fin (Fin)
import qualified Data.Type.Nat as Nat
import           Prelude.Unicode (ℤ)
import           Numeric.Natural.Unicode (ℕ)
import           Data.Tagged (Tagged, unTagged, retag)
import qualified Data.Universe as U

-- An imperfect, somewhat practical, representation of a Finite type constraint
-- The poor Haskeller's version of a Finite type constraint without reaching for dependent types
-- Will probably delete most of this once Haskell has better dependent type support :)
class (Enum a, Bounded a, Ord a, U.Finite a) ⇒ Finite a where
  -- N.B. if overridding asList, make sure the list contains only distinct elements in ascending order.
  asList ∷ [a]
  asList = boundedEnumFrom minBound
  asSet ∷ Set a
  asSet = Set.fromDistinctAscList asList

class BoundedBelow a where
  minimumBound ∷ a

class BoundedAbove a where
  maximumBound ∷ a

-- TODO experimental, may want to create seperate file for these classes
-- A wrapper for some type `a` which is known to be not empty (the proof of
-- which is witnessed by `wit`).
class NotEmpty a where
  wit ∷ a
class (NotEmpty a, Finite a) ⇒ NEF a where
  asNE ∷ NonEmpty a
  -- asNE = wit :| _ -- TODO decide if default implemetation is at all useful

-- TODO
instance NotEmpty () where
  wit  ∷ ()
  wit  = ()
instance NotEmpty Bool where
  wit  ∷ Bool
  wit  = False
instance NotEmpty Ordering where
  wit  ∷ Ordering
  wit  = LT
instance NotEmpty Fin₁ where
  wit ∷ Fin₁
  wit = 0
instance NotEmpty Fin₂ where
  wit ∷ Fin₂
  wit = 0
instance NotEmpty Fin₃ where
  wit ∷ Fin₃
  wit = 0
instance NotEmpty Fin₄ where
  wit ∷ Fin₄
  wit = 0
instance NotEmpty Fin₅ where
  wit ∷ Fin₅
  wit = 0
instance NotEmpty Fin₆ where
  wit ∷ Fin₆
  wit = 0
instance NotEmpty Fin₇ where
  wit ∷ Fin₇
  wit = 0
instance NotEmpty Fin₈ where
  wit ∷ Fin₈
  wit = 0
instance NotEmpty Fin₉ where
  wit ∷ Fin₉
  wit = 0
instance NotEmpty Fin₁₀ where
  wit ∷ Fin₁₀
  wit = 0
instance NotEmpty Fin₁₁ where
  wit ∷ Fin₁₁
  wit = 0
instance NotEmpty Fin₁₂ where
  wit ∷ Fin₁₂
  wit = 0
instance NotEmpty Fin₁₃ where
  wit ∷ Fin₁₃
  wit = 0
instance NotEmpty Fin₁₄ where
  wit ∷ Fin₁₄
  wit = 0
instance NotEmpty Fin₁₅ where
  wit ∷ Fin₁₅
  wit = 0
instance NotEmpty ℕ where
  wit ∷ ℕ
  wit = 0
instance NotEmpty ℤ where
  wit ∷ ℤ
  wit = 0

instance NotEmpty Alpha where
  wit ∷ Alpha
  wit = A
instance NotEmpty DNA where
  wit ∷ DNA
  wit = Adenine
instance NotEmpty Suit where
  wit ∷ Suit
  wit = Spade
instance NotEmpty Rank where
  wit ∷ Rank
  wit = Two
instance NotEmpty Card where
  wit ∷ Card
  wit = Card wit wit
instance NotEmpty D₆ where
  wit ∷ D₆
  wit = Side₁
instance NotEmpty Month where
  wit ∷ Month
  wit = January

instance NotEmpty [a] where
  wit ∷ [a]
  wit = []
instance NotEmpty (Maybe a) where
  wit ∷ Maybe a
  wit = Nothing
instance NotEmpty (Set a) where
  wit ∷ Set a
  wit = (∅)
instance NotEmpty (OSet a) where
  wit ∷ OSet a
  wit = OSet.empty

instance NEF () where
  asNE ∷ NonEmpty ()
  asNE = () :| []
instance NEF Bool where
  asNE ∷ NonEmpty Bool
  asNE = False :| [True]
instance NEF Ordering where
  asNE ∷ NonEmpty Ordering
  asNE = LT :| [EQ, GT]

instance (Finite a) ⇒ NEF (Maybe a) where
  asNE ∷ NonEmpty (Maybe a)
  asNE = Nothing :| asList

class (Finite sigma) ⇒ Σ formalism sigma | formalism → sigma where
  -- Σ, The alphabet of the formalism
  sigma ∷ formalism → Set sigma
  sigma = const asSet

  -- Σ⋆, Given a formalism, use its alphabet to lazily generate all possible strings
  sigmaStar ∷ formalism → [[sigma]]
  sigmaStar = const (freeMonoid asList)

  -- Σ⁺ = Σ⋆ \ {ε}, the positive closure
  sigmaPlus ∷ formalism → [[sigma]]
  sigmaPlus = const (freeSemigroup asList)

  -- (Σ ∪ {ε})
  sigma_ε ∷ formalism → Set (Maybe sigma)
  sigma_ε = Set.insert Nothing . Set.mapMonotonic Just . sigma

-- Note well: some classes such as `MYT` and `GFA` need to account for extra states when declaring an instance of `Q`!
class (Finite q) ⇒ Q automaton q | automaton → q where
  -- Q, The states of the Automaton
  qs ∷ automaton → Set q
  qs = const asSet

class (Finite g) ⇒ Γ automaton g | automaton → g where
  -- Γ, the external alphabet of the automaton
  gamma ∷ automaton → Set g
  gamma = const asSet

instance Finite () where
  asList ∷ [()]
  asList = [()]
  asSet ∷ Set ()
  asSet  = Set.singleton ()
instance Finite Bool where
  asList ∷ [Bool]
  asList = [False, True]
instance Finite Ordering where
  asList ∷ [Ordering]
  asList = [LT, EQ, GT]
instance Finite Char

instance (Finite a)
       ⇒ Bounded (Set a) where
  minBound ∷ Set a
  minBound = (∅)
  -- I'd rather this were just `asSet` as in a Hasse diagram (even though there is a total order)
  -- but that would be inaccurate for the Data.Set implementation
  maxBound ∷ Set a
  maxBound = singleton maxBound
-- For `Set a` where `a` is enumerable, enumerate the set as the powerset.
instance (Finite a)
       ⇒ Enum (Set a) where
  toEnum   ∷ Int → Set a
  toEnum   = (asList !!)
  fromEnum ∷ Set a → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ Set a → [Set a]
  enumFrom = boundedEnumFrom
instance (Finite a)
       ⇒ Finite (Set a) where
  asList ∷ [Set a]
  asList = Set.toList (powerSet asSet)
  asSet ∷ Set (Set a)
  asSet  = powerSet asSet

instance (Finite a)
       ⇒ Enum (OSet a) where
  toEnum   ∷ Int → OSet a
  toEnum   = (asList !!)
  fromEnum ∷ OSet a → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ OSet a → [OSet a]
  enumFrom = boundedEnumFrom

instance (Finite a)
       ⇒ Bounded (OSet a) where
  minBound ∷ OSet a
  minBound = OSet.empty
  -- TODO test that `maxBound == OSet.fromList (comparisonToList maxBound)`
  maxBound ∷ OSet a
  maxBound = OSet.fromList (reverse (asList ∷ [a]))

instance (Finite a, U.Universe a)
       ⇒ U.Universe (OSet a) where
instance (Finite a)
       ⇒ U.Finite (OSet a) where
  -- http://oeis.org/A000522
  cardinality ∷ Tagged (OSet a) ℕ
  cardinality = fmap (\n → sum (fmap (\k → choose' (n, k) * factorial k) [0 .. n])) (retag (U.cardinality ∷ Tagged a ℕ))

-- Generate all subsets then do permutations of each subset
-- AKA "sequences without repetition" or "k-permutations of n"
instance (Finite a)
       ⇒ Finite (OSet a) where
  asList ∷ (Finite a) ⇒ [OSet a]
  -- FIXME, test that this ordering agrees with `Comparison` ordering
  asList = sort (fmap OSet.fromList (concatMap permutations (subsequences (asList ∷ [a]))))

-- If `a` is bounded, then just move the lower bound to `Nothing`, and wrap the upper bound in a `Just`
-- This is one arbitrary possible instance
instance (Bounded a)
       ⇒ Bounded (Maybe a) where
  minBound ∷ Maybe a
  minBound = Nothing
  maxBound ∷ Maybe a
  maxBound = Just maxBound
-- For `Maybe a` types where `a` is enumerable, enumerate as `Nothing : fmap Just [toEnum 0..]`.
instance (Finite a)
       ⇒ Enum (Maybe a) where
  toEnum   ∷ Int     → Maybe a
  toEnum 0 = Nothing
  toEnum n = Just (toEnum (n - 1))
  fromEnum ∷ Maybe a → Int
  fromEnum Nothing  = 0
  fromEnum (Just t) = fromEnum t + 1
  enumFrom ∷ Maybe a → [Maybe a]
  enumFrom Nothing  = asList
  enumFrom (Just t) = fmap Just (enumFrom t)
instance (Finite a)
       ⇒ Finite (Maybe a) where
  asList ∷ [Maybe a]
  asList = U.universeF
  asSet ∷ Set (Maybe a)
  asSet  = Set.insert Nothing (Set.mapMonotonic Just asSet)

instance (Bounded a, Bounded b)
       ⇒ Bounded (Either a b) where
  minBound ∷ Either a b
  minBound = Left  minBound
  maxBound ∷ Either a b
  maxBound = Right maxBound
-- For `(Either a b)` where types `a` and `b` are enumerable,
-- enumerate as the concatenation of the enumerations of `Left` then `Right` types.
instance (Finite a, Finite b)
       ⇒ Enum (Either a b) where
  toEnum   ∷ Int → Either a b
  toEnum   = (asList !!)
  fromEnum ∷ Either a b → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ Either a b → [Either a b]
  enumFrom = boundedEnumFrom
instance (Finite a, Finite b)
       ⇒ Finite (Either a b) where
  asList ∷ [Either a b]
  asList = toList asSet
  asSet ∷ Set (Either a b)
  asSet  = asSet ⊎ asSet

instance (Bounded a, Bounded b)
       ⇒ Bounded (These a b) where
  minBound ∷ These a b
  minBound = This  minBound
  maxBound ∷ These a b
  maxBound = These maxBound maxBound
instance (Finite a, Finite b)
       ⇒ Enum (These a b) where
  toEnum   ∷ Int → These a b
  toEnum   = (asList !!)
  fromEnum ∷ These a b → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ These a b → [These a b]
  enumFrom = boundedEnumFrom
instance (Finite a, Finite b)
       ⇒ U.Finite (These a b) where
  -- a + b + ab
  cardinality ∷ Tagged (These a b) ℕ
  cardinality = liftA2 (\a b → a + b + a * b) (retag (U.cardinality ∷ Tagged a ℕ)) (retag (U.cardinality ∷ Tagged b ℕ))

-- TODO wait why do I need Finite constraints here??
instance (Finite a, Finite b, U.Universe a, U.Universe b)
       ⇒ U.Universe (These a b)
instance (Finite a, Finite b)
       ⇒ Finite (These a b) where
  asList ∷ [These a b]
  asList = toList asSet
  asSet ∷ Set (These a b)
  asSet = Set.map toThese (products ⊎ sums)
    where
      products ∷ Set (a, b) 
      products = asSet
      sums ∷ Set (Either a b)
      sums = asSet -- asSet ⊎ asSet

-- For tuples where types `a` and `b` are enumerable, allow the tuple to be enumerated as `a` × `b`
instance (Finite a, Finite b)
       ⇒ Enum (a, b) where
  toEnum ∷ Int → (a, b)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ)
    where
      cardinality_a ∷ ℕ
      cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      (i₁, bᵢ) = i₀ `quotRem` fromIntegral cardinality_b
      (_,  aᵢ) = i₁ `quotRem` fromIntegral cardinality_a
  fromEnum ∷ (a, b) → Int
  fromEnum (a, b) = fromIntegral $ aᵢ * cardinality_b
                                 +                  bᵢ
    where
      (aᵢ, bᵢ) = (fromEnum' a, fromEnum' b) ∷ (ℕ, ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
  enumFrom ∷ (a, b) → [(a, b)]
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b)
       ⇒ Finite (a, b) where
  asSet ∷ Set (a, b)
  asSet  = asSet × asSet
  asList ∷ [(a, b)]
  asList = liftA2 (,) asList asList

-- For tuples where types `a`, `b`, and `c` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c`
instance (Finite a, Finite b, Finite c)
       ⇒ Enum (a, b, c) where
  toEnum ∷ Int → (a, b, c)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ)
    where
      cardinality_a ∷ ℕ
      cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      cardinality_c ∷ ℕ
      cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      (i₁, cᵢ) = i₀ `quotRem` fromIntegral cardinality_c
      (i₂, bᵢ) = i₁ `quotRem` fromIntegral cardinality_b
      (_,  aᵢ) = i₂ `quotRem` fromIntegral cardinality_a
  fromEnum ∷ (a, b, c) → Int
  fromEnum (a, b, c) = fromIntegral $ aᵢ * cardinality_b  * cardinality_c
                                    +                  bᵢ * cardinality_c
                                    +                                   cᵢ
    where
      (aᵢ, bᵢ, cᵢ) = (fromEnum' a, fromEnum' b, fromEnum' c) ∷ (ℕ, ℕ, ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      cardinality_c ∷ ℕ
      cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
  enumFrom ∷ (a, b, c) → [(a, b, c)]
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b, Finite c)
       ⇒ Finite (a, b, c) where
  asList ∷ [(a, b, c)]
  asList = liftA3 (,,) asList asList asList

-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Finite a, Finite b, Finite c, Finite d)
       ⇒ Enum (a, b, c, d) where
  toEnum ∷ Int → (a, b, c, d)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ, toEnum dᵢ)
    where
      cardinality_a ∷ ℕ
      cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      cardinality_c ∷ ℕ
      cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      cardinality_d ∷ ℕ
      cardinality_d = unTagged (U.cardinality ∷ Tagged d ℕ)
      (i₁, dᵢ) = i₀ `quotRem` fromIntegral cardinality_d ∷ (Int, Int)
      (i₂, cᵢ) = i₁ `quotRem` fromIntegral cardinality_c ∷ (Int, Int)
      (i₃, bᵢ) = i₂ `quotRem` fromIntegral cardinality_b ∷ (Int, Int)
      (_,  aᵢ) = i₃ `quotRem` fromIntegral cardinality_a ∷ (Int, Int)
  fromEnum ∷ (a, b, c, d) → Int
  fromEnum (a, b, c, d) = fromIntegral $ aᵢ * cardinality_b  * cardinality_c  * cardinality_d
                                       +                  bᵢ * cardinality_c  * cardinality_d
                                       +                                   cᵢ * cardinality_d
                                       +                                                    dᵢ
    where
      (aᵢ, bᵢ, cᵢ, dᵢ) = (fromEnum' a, fromEnum' b, fromEnum' c, fromEnum' d) ∷ (ℕ, ℕ, ℕ, ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      cardinality_c ∷ ℕ
      cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      cardinality_d ∷ ℕ
      cardinality_d = unTagged (U.cardinality ∷ Tagged d ℕ)
  enumFrom ∷ (a, b, c, d) → [(a, b, c, d)]
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b, Finite c, Finite d)
       ⇒ Finite (a, b, c, d) where
  asList ∷ [(a, b, c, d)]
  asList = liftM4 (,,,)  asList asList asList asList

-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Finite a, Finite b, Finite c, Finite d, Finite e)
       ⇒ Enum (a, b, c, d, e) where
  toEnum ∷ Int → (a, b, c, d, e)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ, toEnum dᵢ, toEnum eᵢ)
    where
      cardinality_a ∷ ℕ
      cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      cardinality_c ∷ ℕ
      cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      cardinality_d ∷ ℕ
      cardinality_d = unTagged (U.cardinality ∷ Tagged d ℕ)
      cardinality_e ∷ ℕ
      cardinality_e = unTagged (U.cardinality ∷ Tagged e ℕ)
      (i₁, eᵢ) = i₀ `quotRem` fromIntegral cardinality_e
      (i₂, dᵢ) = i₁ `quotRem` fromIntegral cardinality_d
      (i₃, cᵢ) = i₂ `quotRem` fromIntegral cardinality_c
      (i₄, bᵢ) = i₃ `quotRem` fromIntegral cardinality_b
      (_,  aᵢ) = i₄ `quotRem` fromIntegral cardinality_a
  fromEnum ∷ (a, b, c, d, e) → Int
  fromEnum (a, b, c, d, e) = fromIntegral $ aᵢ * cardinality_b  * cardinality_c  * cardinality_d  * cardinality_e
                                          +                  bᵢ * cardinality_c  * cardinality_d  * cardinality_e
                                          +                                   cᵢ * cardinality_d  * cardinality_e
                                          +                                                    dᵢ * cardinality_e
                                          +                                                                     eᵢ
    where
      (aᵢ, bᵢ, cᵢ, dᵢ, eᵢ) = (fromEnum' a, fromEnum' b, fromEnum' c, fromEnum' d, fromEnum' e)
      cardinality_b ∷ ℕ
      cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      cardinality_c ∷ ℕ
      cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      cardinality_d ∷ ℕ
      cardinality_d = unTagged (U.cardinality ∷ Tagged d ℕ)
      cardinality_e ∷ ℕ
      cardinality_e = unTagged (U.cardinality ∷ Tagged e ℕ)
  enumFrom ∷ (a, b, c, d, e) → [(a, b, c, d, e)]
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b, Finite c, Finite d, Finite e)
       ⇒ Finite (a, b, c, d, e)
   where
  asList ∷ [(a, b, c, d, e)]
  asList = liftM5 (,,,,) asList asList asList asList asList

-- Something like Fin₀
instance Enum Void where
  toEnum ∷ Int → Void
  toEnum = undefined
  fromEnum ∷ Void → Int
  fromEnum = absurd
-- Easier to do this than write "BoundedOrEmpty" class because Enum and Bounded are everywhere :)
instance Bounded Void where
  minBound ∷ Void
  minBound = undefined
  maxBound ∷ Void
  maxBound = undefined
instance Finite Void where
  asList ∷ [Void]
  asList = []
  asSet ∷ Set Void
  asSet  = (∅)

type Nat10  = 'Nat.S Nat.Nat9
type Nat11  = 'Nat.S Nat10
type Nat12  = 'Nat.S Nat11
type Nat13  = 'Nat.S Nat12
type Nat14  = 'Nat.S Nat13
type Nat15  = 'Nat.S Nat14

type Fin₀  = Fin Nat.Nat0
type Fin₁  = Fin Nat.Nat1
type Fin₂  = Fin Nat.Nat2
type Fin₃  = Fin Nat.Nat3
type Fin₄  = Fin Nat.Nat4
type Fin₅  = Fin Nat.Nat5
type Fin₆  = Fin Nat.Nat6
type Fin₇  = Fin Nat.Nat7
type Fin₈  = Fin Nat.Nat8
type Fin₉  = Fin Nat.Nat9
type Fin₁₀ = Fin Nat10
type Fin₁₁ = Fin Nat11
type Fin₁₂ = Fin Nat12
type Fin₁₃ = Fin Nat13
type Fin₁₄ = Fin Nat14
type Fin₁₅ = Fin Nat15

type Fin0  = Fin₀
type Fin1  = Fin₁
type Fin2  = Fin₂
type Fin3  = Fin₃
type Fin4  = Fin₄
type Fin5  = Fin₅
type Fin6  = Fin₆
type Fin7  = Fin₇
type Fin8  = Fin₈
type Fin9  = Fin₉
type Fin10 = Fin₁₀
type Fin11 = Fin₁₁
type Fin12 = Fin₁₂
type Fin13 = Fin₁₃
type Fin14 = Fin₁₄
type Fin15 = Fin₁₅

instance U.Universe Fin₁
instance U.Finite   Fin₁
instance Finite     Fin₁

instance U.Universe Fin₂
instance U.Finite   Fin₂
instance Finite     Fin₂

instance U.Universe Fin₃
instance U.Finite   Fin₃
instance Finite     Fin₃

instance U.Universe Fin₄
instance U.Finite   Fin₄
instance Finite     Fin₄

instance U.Universe Fin₅
instance U.Finite   Fin₅
instance Finite     Fin₅

instance U.Universe Fin₆
instance U.Finite   Fin₆
instance Finite     Fin₆

instance U.Universe Fin₇
instance U.Finite   Fin₇
instance Finite     Fin₇

instance U.Universe Fin₈
instance U.Finite   Fin₈
instance Finite     Fin₈

instance U.Universe Fin₉
instance U.Finite   Fin₉
instance Finite     Fin₉

instance U.Universe Fin₁₀
instance U.Finite   Fin₁₀
instance Finite     Fin₁₀

instance U.Universe Fin₁₁
instance U.Finite   Fin₁₁
instance Finite     Fin₁₁

instance U.Universe Fin₁₂
instance U.Finite   Fin₁₂
instance Finite     Fin₁₂

instance U.Universe Fin₁₃
instance U.Finite   Fin₁₃
instance Finite     Fin₁₃

instance U.Universe Fin₁₄
instance U.Finite   Fin₁₄
instance Finite     Fin₁₄

instance U.Universe Fin₁₅
instance U.Finite   Fin₁₅
instance Finite     Fin₁₅

-- TODO deleteme
instance (Show a, Finite a) ⇒ Show (Predicate a) where
  show ∷ Predicate a → String
  show = showpredset
    where
      -- show predicate as a bitstring
      showpredbits ∷ ∀ a . (Finite a) ⇒ Predicate a → String
      showpredbits (Predicate p) = fmap (toBit . p) (asList ∷ [a])
        where
          toBit ∷ Bool → Char
          toBit False = '0'
          toBit True  = '1'
      -- show predicate as a function
      showpredf ∷ ∀ a . (Show a, Finite a) ⇒ Predicate a → String
      showpredf (Predicate p) = unlines (fmap (\(a, b) → show a <> " ↦ " <> show b) graph)
        where
          domain ∷ [a]
          domain = asList
          image_ ∷ [Bool]
          image_  = fmap p domain
          graph ∷ [(a, Bool)]
          graph  = zip domain image_
      -- show predicate as a set
      showpredset ∷ ∀ a . (Show a, Finite a) ⇒ Predicate a → String
      showpredset (Predicate p) = show (Set' (Set.filter p asSet))

instance (Finite a)
       ⇒ Eq (Predicate a) where
  (==) ∷ Predicate a → Predicate a → Bool
  (Predicate p₁) == (Predicate p₂) = all (\a → p₁ a == p₂ a) asList
instance Bounded (Predicate a) where
  minBound ∷ Predicate a
  minBound = Predicate (const False)
  maxBound ∷ Predicate a
  maxBound = Predicate (const True)
instance (Finite a)
       ⇒ Ord (Predicate a) where
  compare ∷ Predicate a → Predicate a → Ordering
  compare (Predicate p₁) (Predicate p₂) = foldMap (\a → p₁ a `compare` p₂ a) asList
instance (Finite a)
       ⇒ Enum (Predicate a) where
  toEnum   ∷ Int         → Predicate a
  toEnum   = (asList !!)
  fromEnum ∷ Predicate a → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ Predicate a → [Predicate a]
  enumFrom = boundedEnumFrom
instance (Finite a)
       ⇒ Finite (Predicate a) where
  asList ∷ [Predicate a]
  asList = fmap (Predicate . toFunction . zip as) bits
    where
      as ∷ [a]
      as = asList
      bs ∷ [Bool]
      bs = asList
      bits ∷ [[Bool]]
      bits = replicateM (length as) bs
      toFunction ∷ [(a, Bool)] → a → Bool
      -- toFunction list = \a → fromJust (lookup a list) -- TODO I like this better but need to get rid of hlint warning -- {-# ANN asList "HLint: warn Redundant lambda" #-}
      toFunction list a = fromJust (lookup a list)

-- TODO may want to move this code (if keeping it) to testing folder when done implementing `Finite` instance for `Equivalence`.

-- Restricted Growth String type, where `a` is the
-- underlying `Finite` type.
-- TODO this might be better as `NonEmpty ℕ → RGS a`?
--
-- TODO Pg. 163 "RGS serves as the /digits/ of a number system, while the edge weights serve as the /coefficients/."
data RGS a where
  RGS ∷ (Finite a) ⇒ [ℕ] → RGS a

instance Show (RGS a) where
  show ∷ RGS a → String
  show (RGS rgs) = show rgs

instance (Finite a)
       ⇒ Bounded (RGS a) where
  minBound ∷ RGS a
  minBound = RGS (genericReplicate cardinality 0)
    where
      cardinality ∷ ℕ
      cardinality = unTagged (U.cardinality ∷ Tagged a ℕ)
  maxBound ∷ RGS a
  maxBound = RGS (genericTake cardinality [0 ..])
    where
      cardinality ∷ ℕ
      cardinality = unTagged (U.cardinality ∷ Tagged a ℕ)

instance (Finite a)
       ⇒ Eq (RGS a) where
  (==) ∷ RGS a → RGS a → Bool
  (==) (RGS rgs₁) (RGS rgs₂) = rgs₁ == rgs₂

instance (Finite a) ⇒ Ord (RGS a) where
  -- TODO this is correct but I will have to think if there is more efficient way to do this directly
  compare ∷ RGS a → RGS a → Ordering
  compare = compare `on` fromRGS

instance (Finite a)
       ⇒ Enum (RGS a) where
  toEnum   ∷ Int   → RGS a
  toEnum   = (asList !!)
  fromEnum ∷ RGS a → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ RGS a → [RGS a]
  enumFrom = boundedEnumFrom

instance (Finite a) ⇒ U.Universe (RGS a)
instance (Finite a) ⇒ U.Finite (RGS a)
instance (Finite a)
       ⇒ Finite (RGS a) where
  asList ∷ [RGS a]
  asList = fmap toRGS (asList ∷ [Equivalence a])

toRGS ∷ (Finite a) ⇒ Equivalence a → RGS a
toRGS (≡) = RGS (fmap (fromEnumBy' (≡) . representative (≡)) asList)

fromRGS ∷ (Finite a) ⇒ RGS a → Equivalence a
fromRGS (RGS rgs) = equating' (genericIndex rgs . fromEnum')

-- TODO https://proofwiki.org/wiki/Definition:Cycle_Decomposition
cycles ∷ (Finite a) ⇒ Comparison a → Equivalence a
cycles c = Equivalence (\a → (a ∈) . orbit c)

-- " the orbit of an element is all its possible destinations under the group action."
-- https://proofwiki.org/wiki/Definition:Orbit_(Group_Theory)
orbit ∷ (Finite a) ⇒ Comparison a → a → NonEmpty a
orbit c a = a :| takeWhile (≠ a) (iterate (representativeC c) (representativeC c a))

-- FIXME
-- ~the least number of times the permutation has to be composed with itself
-- such that it would "become" the identity function.
--
-- https://en.wikipedia.org/wiki/Permutation#Permutation_order
-- "It is the least common multiple of its cycles lengths. For example, the order of (1 3 2)(4 5) is 2 * 3 = 6."
order ∷ (Finite a) ⇒ Comparison a → ℕ
order = F.foldl lcm 1 . fmap length' . fromEquivalence . cycles

byOrder ∷ (Finite a) ⇒ Equivalence (Comparison a)
byOrder = equating' order

-- Count the parts of an equivalence
count ∷ (Finite a) ⇒ Equivalence a → ℕ
count = genericLength . fromEquivalence

byCount ∷ (Finite a) ⇒ Equivalence (Equivalence a)
byCount = equating' count

byLength ∷ (Foldable t) ⇒ Equivalence (t a)
byLength = equating' length

-- group "pieces of pie" (equivalence classes) which are the same size (length)
byEqClassLength ∷ (Finite a) ⇒ Equivalence a → Equivalence a
byEqClassLength = (>$$<) (byLength ∷ Equivalence (NonEmpty a)) . equivalenceClass

shape ∷ (Finite a) ⇒ Equivalence a → [ℕ]
shape = sort . fmap length' . fromEquivalence

byShape ∷ (Finite a) ⇒ Equivalence (Equivalence a)
byShape = equating' shape

byThese ∷ Equivalence (These a b)
byThese = Equivalence (≡)
  where
    (≡) ∷ These a b → These a b → Bool
    (≡) (This  _  ) (This  _  ) = True
    (≡) (That    _) (That    _) = True
    (≡) (These _ _) (These _ _) = True
    (≡) _           _           = False

byEither ∷ Equivalence (Either a b)
byEither = Equivalence (≡)
  where
    (≡) ∷ Either a b → Either a b → Bool
    (≡) (Left  _) (Left  _) = True
    (≡) (Right _) (Right _) = True
    (≡) _         _         = False

byLefts ∷ (Foldable t, Eq a) ⇒ Equivalence (t (Either a b))
byLefts = equating' lefts'

byRights ∷ (Foldable t, Eq b) ⇒ Equivalence (t (Either a b))
byRights = equating' rights'

-- Reflexivity
refl ∷ (Finite a) ⇒ Predicate (Equivalence a)
refl = Predicate (\(Equivalence (≡)) → all (\a → a ≡ a) asSet)

-- Symmetric
sym ∷ (Finite a) ⇒  Predicate (Equivalence a)
sym = Predicate (\(Equivalence (≡)) → all (\(a₁, a₂) → (a₁ ≡ a₂) == (a₂ ≡ a₁)) asSet)

-- Transitivity
trans ∷ (Finite a) ⇒ Predicate (Equivalence a)
trans = Predicate (\(Equivalence (≡)) → all (\(a₁, a₂, a₃) → ((a₁ ≡ a₂) ∧ (a₂ ≡ a₃)) `implies` (a₁ ≡ a₃)) asSet) -- TODO may be some redundant checks here I can eliminate

-- Check that the equivalence relation is lawful
lawful ∷ (Finite a) ⇒ Predicate (Equivalence a)
lawful = refl
      <> sym
      <> trans

-- TODO clean this up, factor for modularity
-- test if the Comparison is actually a total ordering
lawfulComparison ∷ (Finite a) ⇒ Predicate (Comparison a)
lawfulComparison = connexityC
                <> antisymC
                <> transC

tolteq ∷ Comparison a → a → a → Bool
tolteq (Comparison c) a₁ a₂ = a₁ `c` a₂ == LT
                            ∨ a₁ `c` a₂ == EQ

-- TODO move to seperate module (and remove "C" from the name) or just think of better name?
-- "The connex property also implies reflexivity, i.e., a ≤ a."
connexityC ∷ ∀ a . (Finite a) ⇒ Predicate (Comparison a)
connexityC = Predicate p
  where
    p ∷ Comparison a → Bool
    p c = all (\(a₁, a₂) → a₁ ≤ a₂ ∨ a₂ ≤ a₁) asSet
      where
        (≤) ∷ a → a → Bool
        (≤) = tolteq c

-- TODO move to seperate module (and remove "C" from the name) or just think of better name?
antisymC ∷ ∀ a . (Finite a) ⇒ Predicate (Comparison a)
antisymC  = Predicate p
  where
    p ∷ Comparison a → Bool
    p c = all (\(a₁, a₂) → ((a₁ ≤ a₂) ∧ (a₂ ≤ a₁)) `implies` (a₁ == a₂)) asSet
      where
        (≤) ∷ a → a → Bool
        (≤) = tolteq c

-- TODO move to seperate module (and remove "C" from the name) or just think of better name?
transC ∷ ∀ a . (Finite a) ⇒ Predicate (Comparison a)
transC = Predicate p
  where
    p ∷ Comparison a → Bool
    p c = all (\(a₁, a₂, a₃) → ((a₁ ≤ a₂) ∧ (a₂ ≤ a₃)) `implies` (a₁ ≤ a₃)) asSet
      where
        (≤) ∷ a → a → Bool
        (≤) = tolteq c

comparisonToList ∷ (Finite a) ⇒ Comparison a → [a]
comparisonToList (Comparison c) = sortBy c asList

-- Reverse a total order
reverseC ∷ Comparison a → Comparison a
reverseC (Comparison c) = Comparison (flip c)

-- TODO this works for now but think if it is possible to do this but without throwing away information every time, by which I mean an implementation
-- TODO which could search a smaller list after each find (i.e. delete the elements from the list as we find results for them)
listToComparison ∷ (Finite a, Foldable t) ⇒ t a → Comparison a
listToComparison = comparing' . elemIndexTotal  -- FIXME will have to think about Void case

-- FIXME may want to `newtype` this list to guarantee by type it is actually a total permutation
-- FIXME (so perhaps something like "PermutationList" with `Finite` constraint?)
-- N.B. the `fromJust` here is justified in that, if `permutation` is genuinely
-- total for type `a` then any given `a` will be found in the list!
-- TODO better name?
-- TODO To be more accurate, this should probably use `NonEmpty`/`Foldable1`/`Finite1`?
elemIndexTotal ∷ (Finite a, Foldable t) ⇒ t a → a → ℕ
elemIndexTotal permutation a = fromJust (elemIndex' a (F.toList permutation))

-- TODO add test that `fromEnumBy defaultComparison` is same as `fromEnum`
fromEnumBy ∷ (Finite a) ⇒ Comparison a → a → ℕ
fromEnumBy = elemIndexTotal . comparisonToList

-- TODO add test that `toEnumBy defaultComparison` is same as `toEnum`
toEnumBy ∷ (Finite a) ⇒ Comparison a → ℕ → a
toEnumBy = genericIndex . comparisonToList

-- TODO better name
fromEnumBy' ∷ (Finite a) ⇒ Equivalence a → a → ℕ
fromEnumBy' = elemIndexTotal . representatives

-- TODO better name
-- FIXME also decide on how to handle partial results (for `toEnumBy` too)
-- FIXME if this is to be used outside of RGS code (or make it private to RGS context)
toEnumBy' ∷ (Finite a) ⇒ Equivalence a → ℕ → a
toEnumBy' = genericIndex . representatives

representativeC ∷ (Finite a) ⇒ Comparison a → a → a
representativeC c = genericIndex (comparisonToList c) . fromEnum'

-- I mean technically you could :P lol
equivalenceClassC ∷ (Finite a) ⇒ Comparison a → a → NonEmpty a
equivalenceClassC = pure ‥ representativeC

-- TODO
composeC ∷ ∀ a . (Finite a) ⇒ Comparison a → Comparison a → Comparison a
composeC c₁ c₂ = listToComparison (fmap (representativeC c₁ . representativeC c₂) asList)

-- Counts the number of possible total orders over a finite set
cardinalityC ∷ ∀ a . (Finite a) ⇒ Comparison a → ℕ
cardinalityC _ = unTagged (U.cardinality ∷ Tagged (Comparison a) ℕ)

instance (Show a, Finite a)
       ⇒ Show (Comparison a) where
  show ∷ Comparison a → String
  show = showl
    where
      -- show Comparison as a sorted list
      showl ∷ ∀ a . (Show a, Finite a) ⇒ Comparison a → String
      showl = show . comparisonToList
      -- show Comparison as a permutation (in two line notation)
      -- 1 ↦ 3
      -- 2 ↦ 2
      -- 3 ↦ 1
      -- ⦍ 1 2 3 ⦐
      -- ⦏ 3 2 1 ⦎
      -- TODO add cycle notation
      showp ∷ ∀ a. (Show a, Finite a) ⇒ Comparison a → String
      showp comparison = topline
                      <> "\n"
                      <> botline
        where
          top ∷ [a]
          top = asList
          bot ∷ [a]
          bot = comparisonToList comparison
          topline = "⦍" <> (top >>= show) <> "⦐"
          botline = "⦏" <> (bot >>= show) <> "⦎"
      -- show Comparison as a function
      showf ∷ ∀ a. (Show a, Finite a) ⇒ Comparison a → String
      showf (Comparison cmp) = unlines (fmap show' graph)
        where
          domain ∷ [(a, a)]
          domain = asList
          graph  ∷ [(a, a, Ordering)]
          graph  = fmap (\(a₁, a₂) → (a₁, a₂, a₁ `cmp` a₂)) domain
          show' (a₁, a₂, o) = show a₁ ++ ", " ++ show a₂ ++ " ↦ " ++ show o

instance (Finite a)
       ⇒ Group (Comparison a) where
  invert ∷ Comparison a → Comparison a
  invert = comparing' . representativeC

instance (Finite a)
       ⇒ Eq (Comparison a) where
  (==) ∷ Comparison a → Comparison a → Bool
  (==) = (==) `on` comparisonToList

instance (Finite a)
       ⇒ Enum (Comparison a) where
  toEnum   ∷ Int → Comparison a
  toEnum   = (asList !!)
  fromEnum ∷ Comparison a → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ Comparison a → [Comparison a]
  enumFrom = boundedEnumFrom

instance (Finite a)
       ⇒ Ord (Comparison a) where
  compare ∷ Comparison a → Comparison a → Ordering
  compare = compare `on` comparisonToList

instance (Finite a)
       ⇒ Bounded (Comparison a) where
  minBound ∷ Comparison a
  minBound = defaultComparison
  maxBound ∷ Comparison a
  maxBound = reverseC minBound

instance (Finite a, U.Universe a)
       ⇒ U.Universe (Comparison a) where
instance (Finite a)
       ⇒ U.Finite (Comparison a) where
  -- Counts the number of possible total orders over a finite set
  cardinality ∷ Tagged (Comparison a) ℕ
  cardinality = fmap factorial (retag (U.cardinality ∷ Tagged a ℕ))
instance (Finite a)
       ⇒ Finite (Comparison a) where
  asList ∷ [Comparison a]
  asList = sort (fmap listToComparison (permutations (asList ∷ [a])))

-- r₁ is "finer" r₂ iff r₁ ⊆ r₂   i.e. r₁ is a refinement of r₂
-- if r₁ is a refinement of r₂ then each equivalence class of r₂ is
-- a union of some of the equivalence classes of r₁.
-- The finer-than relation reflexive, transitive, and antisymmetric (a partial order)
finer ∷ (Finite a) ⇒ Equivalence a → Equivalence a → Bool
finer (Equivalence (⮀)) (Equivalence (⮂)) = all (\(x, y) → (x ⮀ y) `implies` (x ⮂ y)) asList

coarser ∷ (Finite a) ⇒ Equivalence a → Equivalence a → Bool
coarser = flip finer

-- TODO meant to be used with the `partitions'` fn and an index
-- TODO move (to a `where` clause?) and possibly rename?
-- partitions' {0..2} = [ [[0,1,2]]
--                      , [[1,2],[0]]
--                      , [[0,2],[1]]
--                      , [[2],[0,1]]
--                      , [[2],[1],[0]]
--                      ]
-- for each list (which represents an equivalence class), check if both a₁ and a₂ are in it
-- if they are in the same list return true, otherwise false
toEquivalence ∷ (Finite a, Foldable t) ⇒ t (NonEmpty a) → Equivalence a
toEquivalence parts = Equivalence (\a₁ a₂ → any (\part → (a₁ ∈ part) ∧ (a₂ ∈ part)) parts)

fromEquivalence ∷ ∀ a . (Finite a) ⇒ Equivalence a → [NonEmpty a]
fromEquivalence (Equivalence (≡)) = unfoldr c asList
  where
    c ∷ [a] → Maybe (NonEmpty a, [a])
    c []       = Nothing
    c (a : as) = Just (a :| p, np)
      where
        (p, np) = List.partition (≡ a) as

toPredicate ∷ (Foldable t, Eq a) ⇒ t a → Predicate a
toPredicate = Predicate . (∋)

singletonP ∷ (Eq a) ⇒ a → Predicate a
singletonP = Predicate . (==)

singletonPBy ∷ Equivalence a → a → Predicate a
singletonPBy (Equivalence (≡)) = Predicate . (≡)

disjointP ∷ (Finite a) ⇒ Predicate a → Predicate a → Bool
disjointP = Set.disjoint `on` predicateToSet

intersectingP ∷ (Finite a) ⇒ Predicate a → Predicate a → Bool
intersectingP = not ‥ disjointP

predicateToList ∷ (Finite a) ⇒ Predicate a → [a]
predicateToList (Predicate p) = List.filter p asList

predicateToSet  ∷ (Finite a) ⇒ Predicate a → Set a
predicateToSet (Predicate p) = Set.filter p asSet

-- TODO better name?
-- fromPredicate (Predicate (> 2) ∷ Predicate Fin₁₀) == [[0,1,2],[3,4,5,6,7,8,9]]
-- N.B. information is lost here, we can't distinguish `p` from `(not . p)` anymore
fromPredicate ∷ Predicate a → Equivalence a
fromPredicate (Predicate p) = equating' p

-- There is a way to do this safely by generating the NonEmpty list for the equivalence class
-- and then using comonadic extract to guarantee the representative will always be there
-- and thus avoiding the unsafe `head` but that seems like too much overhead for right now
-- The correct type for this should actually be:
-- representative ∷ (Finite a) ⇒ Equivalence a → Maybe (a → a)
-- Because the null relation is (vacuously) a lawful equivalence relation
-- https://proofwiki.org/wiki/Relation_on_Empty_Set_is_Equivalence
representative ∷ (Finite a) ⇒ Equivalence a → a → a
representative (Equivalence (≡)) a = head (List.filter (≡ a) asList)

representatives ∷ (Finite a) ⇒ Equivalence a → [a]
representatives (Equivalence (≡)) = nubBy (≡) asList

-- TODO explore other options to do this?
equivalenceClass ∷ ∀ a . (Finite a) ⇒ Equivalence a → a → NonEmpty a
equivalenceClass (Equivalence (≡)) a₁ = NE.insert a₁ (fmap snd (catThese (partitionedBy (Equivalence (≡)) a₁)))
  where
    -- TODO describe in terms of irreflexive kernel / anti-reflexive kernel?
    partitionedBy ∷ ∀ a . (Finite a) ⇒ Equivalence a → a → [These a a]
    partitionedBy (Equivalence (≡)) a₁ = fmap f (asList ∷ [a])
      where
        f ∷ a → These a a
        f a₂ | a₁ == a₂ = This  a₁    -- equal by `==`
        f a₂ | a₁ ≡ a₂  = These a₁ a₂ -- equal by `≡` but not `==`
        f a₂            = That     a₂ -- not equal

-- TODO deleteme
instance (Show a, Finite a) ⇒ Show (Equivalence a) where
  show ∷ Equivalence a → String
  show = showl
    where
      -- show an Equivalence as a list of disjoint lists of elements
      showl ∷ ∀ a. (Show a, Finite a) ⇒ Equivalence a → String
      showl = show . fmap NE.toList . fromEquivalence
      -- show an Equivalence as a function
      showf ∷ ∀ a. (Show a, Finite a) ⇒ Equivalence a → String
      showf (Equivalence (≡)) = unlines (fmap show' graph)
        where
          domain ∷ [(a, a)]
          domain = asList
          graph  ∷ [(a, a, Bool)]
          graph  = fmap (\(a₁, a₂) → (a₁, a₂, a₁ ≡ a₂)) domain
          show' (a₁, a₂, b) = show a₁ ++ ", " ++ show a₂ ++ " ↦ " ++ show b
      -- show an Equivalence relation as a Ferrer's diagram -- TODO can improve this later, but this works
      showferrers ∷ ∀ a. (Show a, Finite a) ⇒ Equivalence a → String
      showferrers e = unlines (reverse (sortOn genericLength (fmap (fmap (const '*')) parts)))
        where
          parts ∷ [[a]]
          parts = fmap NE.toList (fromEquivalence e)

-- TODO probably going to be lots of room for optimization in these instance defs, but for now I want to focus on correctness
instance (Finite a)
       ⇒ Eq (Equivalence a) where
  (==) ∷ Equivalence a → Equivalence a → Bool
  (Equivalence (⮀)) == (Equivalence (⮂)) = all (\(a₁, a₂) → (a₁ ⮀ a₂) == (a₁ ⮂ a₂)) (asSet × asSet)
-- N.B. this is just one possible implementation
instance (Eq a)
       ⇒ Bounded (Equivalence a) where
  -- One big equivalence class (the coarsest, i.e. the universal relation: {(x, y) | x, y ∈ U})
  minBound ∷ Equivalence a
  minBound = conquer -- Equivalence (const (const True))
  -- Each element is it's own equivalence class (the finest, i.e. the identity relation: {(x, x) | x ∈ U})
  -- N.B. `Equivalence (const (const False))` would violate reflexivity (unless in the vacuous case, where it is technically allowed)
  maxBound ∷ Equivalence a
  maxBound = defaultEquivalence
instance (Finite a)
       ⇒ Ord (Equivalence a) where
  -- N.B. that `⮀` and `⮂` swap order of appearence so that `compare minBound maxBound` is `LT` (for types of cardinality `> 1` [: )
  compare ∷ Equivalence a → Equivalence a → Ordering
  compare (Equivalence (⮀)) (Equivalence (⮂)) = foldMap (\(a₁, a₂) → (a₁ ⮂ a₂) `compare` (a₁ ⮀ a₂)) asList
instance (Finite a)
       ⇒ Enum (Equivalence a) where
  toEnum   ∷ Int → Equivalence a
  toEnum   = (asList !!)
  fromEnum ∷ Equivalence a → Int
  fromEnum = fromJust . flip elemIndex asList
  enumFrom ∷ Equivalence a → [Equivalence a]
  enumFrom = boundedEnumFrom

instance (Finite a)
       ⇒ U.Universe (Equivalence a)
instance (Finite a)
       ⇒ U.Finite (Equivalence a)
instance (Finite a)
       ⇒ Finite (Equivalence a) where
  asList ∷ [Equivalence a]
  asList = fmap toEquivalence (partitions' asList)

data Alpha = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z deriving (Eq, Ord, Enum, Bounded, Show, Read)
instance U.Universe Alpha
instance U.Finite   Alpha
instance Finite Alpha

data DNA = Adenine | Cytosine | Guanine | Thymine deriving (Eq, Ord, Bounded, Enum)
instance Show DNA where
  show ∷ DNA → String
  show Adenine  = "A"
  show Cytosine = "C"
  show Guanine  = "G"
  show Thymine  = "T"
instance U.Universe DNA
instance U.Finite   DNA
instance Finite DNA


newtype Init = Init () deriving (Eq, Ord, Bounded, Enum)
instance U.Universe Init
instance U.Finite   Init
instance Finite Init where
  asList ∷ [Init]
  asList = [Init ()]
  asSet ∷ Set Init
  asSet  = Set.singleton (Init ())
instance Show Init where
  show ∷ Init → String
  show (Init ()) = "qᵢ"
newtype Final = Final () deriving (Eq, Ord, Bounded, Enum)
instance U.Universe Final
instance U.Finite   Final
instance Finite Final where
  asList ∷ [Final]
  asList = [Final ()]
  asSet ∷ Set Final
  asSet  = Set.singleton (Final ())
instance Show Final where
  show ∷ Final → String
  show (Final ()) = "qᶠ"

-- A six-sided die -- TODO -- 🎲  U+1F3B2
data D₆ where
  Side₁ ∷ D₆
  Side₂ ∷ D₆
  Side₃ ∷ D₆
  Side₄ ∷ D₆
  Side₅ ∷ D₆
  Side₆ ∷ D₆
  deriving (Eq, Enum, Ord, Bounded)

-- non unicode aliases for convenience
type D6 = D₆
side1 = Side₁ ∷ D₆
side2 = Side₂ ∷ D₆
side3 = Side₃ ∷ D₆
side4 = Side₄ ∷ D₆
side5 = Side₅ ∷ D₆
side6 = Side₆ ∷ D₆

instance Show D₆ where
  show ∷ D₆ → String
  show = show'

instance U.Universe D₆
instance U.Finite   D₆
instance Finite     D₆

instance Fancy D₆ where
  unicode  ∷ D₆ → Char
  unicode Side₁ = '⚀'
  unicode Side₂ = '⚁'
  unicode Side₃ = '⚂'
  unicode Side₄ = '⚃'
  unicode Side₅ = '⚄'
  unicode Side₆ = '⚅'
  plain ∷ D₆ → String
  plain Side₁ = "Side₁"
  plain Side₂ = "Side₂"
  plain Side₃ = "Side₃"
  plain Side₄ = "Side₄"
  plain Side₅ = "Side₅"
  plain Side₆ = "Side₆"
  show' ∷ D₆ → String
  show' d = charToString (unicode d) `toColor` colorOf' d
    where
      -- TODO almost have the six colors of Rubik's cube, maybe try to update?
      colorOf' ∷ D₆ → DisplayColor
      colorOf' Side₁ = Red'    -- "⚀"
      colorOf' Side₂ = Magenta -- "⚁" -- Orange
      colorOf' Side₃ = Yellow  -- "⚂"
      colorOf' Side₄ = Green   -- "⚃"
      colorOf' Side₅ = Blue    -- "⚄"
      colorOf' Side₆ = White   -- "⚅"

(⚀) ∷ D₆
(⚀) = Side₁

(⚁) ∷ D₆
(⚁) = Side₂

(⚂) ∷ D₆
(⚂) = Side₃

(⚃) ∷ D₆
(⚃) = Side₄

(⚄) ∷ D₆
(⚄) = Side₅

(⚅) ∷ D₆
(⚅) = Side₆

data Month where
  January   ∷ Month
  February  ∷ Month
  March     ∷ Month
  April     ∷ Month
  May       ∷ Month
  June      ∷ Month
  July      ∷ Month
  August    ∷ Month
  September ∷ Month
  October   ∷ Month
  November  ∷ Month
  December  ∷ Month
  deriving (Eq, Enum, Ord, Bounded)

instance U.Universe Month
instance U.Finite   Month
instance Finite     Month

data Suit where
  Spade   ∷ Suit
  Heart   ∷ Suit
  Diamond ∷ Suit
  Club    ∷ Suit
  deriving (Eq, Enum, Ord, Bounded)

instance U.Universe Suit
instance U.Finite   Suit
instance Finite     Suit

instance Fancy Suit where
  unicode  ∷ Suit → Char
  unicode  Spade   = '♠'
  unicode  Heart   = '♥'
  unicode  Diamond = '♦'
  unicode  Club    = '♣'
  unicode' ∷ Suit → Char
  unicode' Spade   = '♤'
  unicode' Heart   = '♡'
  unicode' Diamond = '♢'
  unicode' Club    = '♧'
  plain ∷ Suit → String
  plain Spade   = "Spade"
  plain Heart   = "Heart"
  plain Diamond = "Diamond"
  plain Club    = "Club"
  show' ∷ Suit → String
  show' s = charToString (unicode s) `toColor` colorOf s

instance Show Suit where
  show ∷ Suit → String
  show = show'

data Rank where
  Two   ∷ Rank
  Three ∷ Rank
  Four  ∷ Rank
  Five  ∷ Rank
  Six   ∷ Rank
  Seven ∷ Rank
  Eight ∷ Rank
  Nine  ∷ Rank
  Ten   ∷ Rank
  Jack  ∷ Rank 
  Queen ∷ Rank
  King  ∷ Rank
  Ace   ∷ Rank
  deriving (Eq, Enum, Ord, Bounded)

instance Fancy Rank where
  unicode ∷ Rank → Char
  unicode Two   = '⑵'
  unicode Three = '⑶'
  unicode Four  = '⑷'
  unicode Five  = '⑸'
  unicode Six   = '⑹'
  unicode Seven = '⑺'
  unicode Eight = '⑻'
  unicode Nine  = '⑼'
  unicode Ten   = '⑽'
  unicode Jack  = '⑾'
  unicode Queen = '⑿'
  unicode King  = '⒀'
  unicode Ace   = '⒁'
  plain ∷ Rank → String
  plain Two   = "Two"
  plain Three = "Three"
  plain Four  = "Four"
  plain Five  = "Five"
  plain Six   = "Six"
  plain Seven = "Seven"
  plain Eight = "Eight"
  plain Nine  = "Nine"
  plain Ten   = "Ten"
  plain Jack  = "Jack"
  plain Queen = "Queen"
  plain King  = "King"
  plain Ace   = "Ace"

instance Show Rank where
  show ∷ Rank → String
  show = show'

instance U.Universe Rank
instance U.Finite   Rank
instance Finite     Rank

data Card where
  Card ∷ { rank ∷ Rank, suit ∷ Suit } → Card
  deriving (Ord, Eq, Bounded)

instance Enum Card where
  toEnum ∷ Int → Card
  toEnum = uncurry Card . (asList !!)
  fromEnum ∷ Card → Int
  fromEnum (Card r s) = fromJust (List.elemIndex (r, s) asList)
  enumFrom ∷ Card → [Card]
  enumFrom = boundedEnumFrom

instance U.Universe Card
instance U.Finite   Card
instance Finite     Card

instance Fancy Card where
  unicode ∷ Card → Char
  unicode (Card Ace   Spade  ) = '🂡'
  unicode (Card Ace   Heart  ) = '🂱'
  unicode (Card Ace   Diamond) = '🃁'
  unicode (Card Ace   Club   ) = '🃑'
  unicode (Card King  Spade  ) = '🂮'
  unicode (Card King  Heart  ) = '🂾'
  unicode (Card King  Diamond) = '🃎'
  unicode (Card King  Club   ) = '🃞'
  unicode (Card Queen Spade  ) = '🂭'
  unicode (Card Queen Heart  ) = '🂽'
  unicode (Card Queen Diamond) = '🃍'
  unicode (Card Queen Club   ) = '🃝'
  unicode (Card Jack  Spade  ) = '🂫'
  unicode (Card Jack  Heart  ) = '🂻'
  unicode (Card Jack  Diamond) = '🃋'
  unicode (Card Jack  Club   ) = '🃛'
  unicode (Card Ten   Spade  ) = '🂪'
  unicode (Card Ten   Heart  ) = '🂺'
  unicode (Card Ten   Diamond) = '🃊'
  unicode (Card Ten   Club   ) = '🃚'
  unicode (Card Nine  Spade  ) = '🂩'
  unicode (Card Nine  Heart  ) = '🂹'
  unicode (Card Nine  Diamond) = '🃉'
  unicode (Card Nine  Club   ) = '🃙'
  unicode (Card Eight Spade  ) = '🂨'
  unicode (Card Eight Heart  ) = '🂸'
  unicode (Card Eight Diamond) = '🃈'
  unicode (Card Eight Club   ) = '🃘'
  unicode (Card Seven Spade  ) = '🂧'
  unicode (Card Seven Heart  ) = '🂷'
  unicode (Card Seven Diamond) = '🃇'
  unicode (Card Seven Club   ) = '🃗'
  unicode (Card Six   Spade  ) = '🂦'
  unicode (Card Six   Heart  ) = '🂶'
  unicode (Card Six   Diamond) = '🃆'
  unicode (Card Six   Club   ) = '🃖'
  unicode (Card Five  Spade  ) = '🂥'
  unicode (Card Five  Heart  ) = '🂵'
  unicode (Card Five  Diamond) = '🃅'
  unicode (Card Five  Club   ) = '🃕'
  unicode (Card Four  Spade  ) = '🂤'
  unicode (Card Four  Heart  ) = '🂴'
  unicode (Card Four  Diamond) = '🃄'
  unicode (Card Four  Club   ) = '🃔'
  unicode (Card Three Spade  ) = '🂣'
  unicode (Card Three Heart  ) = '🂳'
  unicode (Card Three Diamond) = '🃃'
  unicode (Card Three Club   ) = '🃓'
  unicode (Card Two   Spade  ) = '🂢'
  unicode (Card Two   Heart  ) = '🂲'
  unicode (Card Two   Diamond) = '🃂'
  unicode (Card Two   Club   ) = '🃒'
  plain ∷ Card → String
  plain (Card rank suit) = plain rank ++ " of " ++ plain suit ++ "s"

instance Show Card where
  show ∷ Card → String
  show c = show' c `toColor` color c

(🂡) ∷ Card
(🂡) = Card Ace Spade
(🂱) ∷ Card
(🂱) = Card Ace Heart
(🃑) ∷ Card
(🃑) = Card Ace Club
(🃁) ∷ Card
(🃁) = Card Ace Diamond

(🂮) ∷ Card
(🂮) = Card King  Spade
(🂾) ∷ Card
(🂾) = Card King  Heart
(🃎) ∷ Card
(🃎) = Card King  Diamond
(🃞) ∷ Card
(🃞) = Card King  Club

(🂭) ∷ Card
(🂭) = Card Queen Spade
(🂽) ∷ Card
(🂽) = Card Queen Heart
(🃍) ∷ Card
(🃍) = Card Queen Diamond
(🃝) ∷ Card
(🃝) = Card Queen Club

(🂫) ∷ Card
(🂫) = Card Jack  Spade
(🂻) ∷ Card
(🂻) = Card Jack  Heart
(🃋) ∷ Card
(🃋) = Card Jack  Diamond
(🃛) ∷ Card
(🃛) = Card Jack  Club

(🂪) ∷ Card
(🂪) = Card Ten   Spade
(🂺) ∷ Card
(🂺) = Card Ten   Heart
(🃊) ∷ Card
(🃊) = Card Ten   Diamond
(🃚) ∷ Card
(🃚) = Card Ten   Club

(🂩) ∷ Card
(🂩) = Card Nine  Spade
(🂹) ∷ Card
(🂹) = Card Nine  Heart
(🃉) ∷ Card
(🃉) = Card Nine  Diamond
(🃙) ∷ Card
(🃙) = Card Nine  Club

(🂨) ∷ Card
(🂨) = Card Eight Spade
(🂸) ∷ Card
(🂸) = Card Eight Heart
(🃈) ∷ Card
(🃈) = Card Eight Diamond
(🃘) ∷ Card
(🃘) = Card Eight Club

(🂧) ∷ Card
(🂧) = Card Seven Spade
(🂷) ∷ Card
(🂷) = Card Seven Heart
(🃇) ∷ Card
(🃇) = Card Seven Diamond
(🃗) ∷ Card
(🃗) = Card Seven Club

(🂦) ∷ Card
(🂦) = Card Six   Spade
(🂶) ∷ Card
(🂶) = Card Six   Heart
(🃆) ∷ Card
(🃆) = Card Six   Diamond
(🃖) ∷ Card
(🃖) = Card Six   Club

(🂥) ∷ Card
(🂥) = Card Five  Spade
(🂵) ∷ Card
(🂵) = Card Five  Heart
(🃅) ∷ Card
(🃅) = Card Five  Diamond
(🃕) ∷ Card
(🃕) = Card Five  Club

(🂤) ∷ Card
(🂤) = Card Four  Spade
(🂴) ∷ Card
(🂴) = Card Four  Heart
(🃄) ∷ Card
(🃄) = Card Four  Diamond
(🃔) ∷ Card
(🃔) = Card Four  Club

(🂣) ∷ Card
(🂣) = Card Three Spade
(🂳) ∷ Card
(🂳) = Card Three Heart
(🃃) ∷ Card
(🃃) = Card Three Diamond
(🃓) ∷ Card
(🃓) = Card Three Club

(🂢) ∷ Card
(🂢) = Card Two   Spade
(🂲) ∷ Card
(🂲) = Card Two   Heart
(🃂) ∷ Card
(🃂) = Card Two   Diamond
(🃒) ∷ Card
(🃒) = Card Two   Club

colorOf ∷ Suit → DisplayColor
colorOf Spade   = Black'
colorOf Heart   = Red'
colorOf Diamond = Red'
colorOf Club    = Black'

color ∷ Card → DisplayColor
color = colorOf . suit

cardsBySuit ∷ Equivalence Card
cardsBySuit = equating' suit

cardsByRank ∷ Equivalence Card
cardsByRank = equating' rank

cardsByColor ∷ Equivalence Card
cardsByColor = equating' color

suitsByColor ∷ Equivalence Suit
suitsByColor = equating' colorOf

