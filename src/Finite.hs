{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ExplicitForAll             #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators              #-}

module Finite where

import           Control.Applicative (Applicative (..), Const (..), liftA3)
import           Control.Monad (void)
import           Data.Bool (bool)
import           Data.Can (Can, can)
import qualified Data.Can as C
import           Data.Char (toLower)
import           Data.Set as Set (Set, disjoint, filter, fromDistinctAscList, insert, map, mapMonotonic, powerSet, singleton)
import           Data.Set.Unicode ((∅))
import           Data.Set.Ordered (OSet)
import qualified Data.Set.Ordered as OSet
import           Data.Bool.Unicode ((∧), (∨))
import           Data.Eq.Unicode ((≠))
import           Data.Fin (Fin)
import qualified Data.Fin as Fin (absurd, toNatural)
import           Data.Foldable (Foldable (..))
import           Data.Foldable.Unicode ((∈), (∋))
import           Data.Function (on)
import           Data.Functor ((<&>))
import           Data.Functor.Contravariant (Contravariant (..), Op (..), Comparison(..), Equivalence (..), Predicate (..), comparisonEquivalence, defaultComparison, defaultEquivalence)
import           Data.Functor.Contravariant.Divisible (Divisible (..))
import           Data.Functor.Identity (Identity (..))
import           Data.Group (Group, invert)
import           Data.List as List (elemIndex, filter, genericDrop, genericIndex, genericLength, genericReplicate, genericTake, intercalate, nubBy, partition, permutations, sort, sortBy, sortOn, subsequences, unfoldr)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import           Data.Maybe (fromJust, maybe)
import           Data.Ord.Unicode ((≤))
import           Data.Ord (Down (..))
import           Data.Smash (Smash (..), smash, toSmash, fromSmash)
import           Data.Tagged (Tagged (..), retag)
import           Data.These (These (..), these)
import           Data.These.Combinators (catThese)
import qualified Data.Type.Nat as Nat
import qualified Data.Universe as U
import           Data.Void (Void, absurd)
import           Data.Wedge (Wedge (..), wedge, toWedge, fromWedge)
import           GHC.Enum (boundedEnumFrom)
import           Numeric.Natural.Unicode (ℕ)
import           Prelude.Unicode (ℤ)
import           Common (DisplayColor (..), HasDisplayColor (..), Fancy (..), Set' (..), bell, charToString, choose', comparing', elemIndex', equating', factorial, filter', freeMonoid, freeSemigroup, fromCan, fromEnum', fromThese, indexed, implies, impossible, liftA4, liftA5, lefts', length', partitions', quoteWith, replicateM', rights', toColor, toCan, toEnum', toThese, (×), (‥), (⊎), (⋄), (>&<))


-- An imperfect, somewhat practical, representation of a Finite type constraint
-- The poor Haskeller's version of a Finite type constraint without reaching for dependent types
-- Will probably delete most of this once Haskell has better dependent type support :)
class (Enum a, Bounded a, Ord a, U.Finite a) ⇒ Finite a where
  -- N.B. if overridding asList, make sure the list contains only distinct elements in ascending order.
  asList ∷ [a]
  asList = boundedEnumFrom minBound
  asSet ∷ Set a
  asSet = Set.fromDistinctAscList asList

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

  -- FIXME this works for now...
  -- Σ⁺ = Σ⋆ \ {ε}, the positive closure (using a `NonEmpty` type for each word)
  sigmaPlusNE ∷ formalism → [NonEmpty sigma]
  sigmaPlusNE = const (fmap NE.fromList (freeSemigroup asList))

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
  asSet  ∷ Set ()
  asSet  = Set.singleton ()
instance Finite Bool where
  asList ∷ [Bool]
  asList = [False, True]
instance Finite Ordering where
  asList ∷ [Ordering]
  asList = [LT, EQ, GT]
instance Finite Char

instance (Finite a) ⇒ Finite (Identity a)

instance (Finite a) ⇒ Finite (Const a b)

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
  asList = toList (powerSet asSet)
  asSet  ∷ Set (Set a)
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
  -- https://oeis.org/A000522
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
-- For `Maybe a` types where `a` is enumerable, enumerate as `Nothing : fmap Just asList`.
instance (Enum a, Bounded a)
       ⇒ Enum (Maybe a) where
  toEnum   ∷ Int     → Maybe a
  toEnum 0 = Nothing
  toEnum n = Just (toEnum (pred n))
  fromEnum ∷ Maybe a → Int
  fromEnum = maybe 0 (succ . fromEnum)
  enumFrom ∷ Maybe a → [Maybe a]
  enumFrom = maybe (Nothing : fmap Just (boundedEnumFrom minBound)) (fmap Just . boundedEnumFrom)
instance (Finite a)
       ⇒ Finite (Maybe a) where
  asList ∷ [Maybe a]
  asList = Nothing : fmap Just asList
  asSet  ∷ Set (Maybe a)
  asSet  = Set.insert Nothing (Set.mapMonotonic Just asSet)

instance (Bounded a, Bounded b)
       ⇒ Bounded (Either a b) where
  minBound ∷ Either a b
  minBound = Left  minBound
  maxBound ∷ Either a b
  maxBound = Right maxBound
-- For `(Either a b)` where types `a` and `b` are enumerable,
-- enumerate as the concatenation of the enumerations of `Left` then `Right` types.
-- FIXME I am able to relax these constraints because I'm not using `asList` anymore
-- FIXME e.g. `instance (U.Finite a, Enum a, Bounded a, Enum b, Bounded b)`
-- FIXME but I have yet to think about if that is indeed better.
instance (Finite a, Finite b)
       ⇒ Enum (Either a b) where
  toEnum   ∷ Int → Either a b
  toEnum   = liftA3 bool (Left . toEnum) (Right . toEnum . flip (-) (fromIntegral cardinality_a)) ((≤) cardinality_a . fromIntegral)
    where
      cardinality_a ∷ ℕ
      cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
  fromEnum ∷ Either a b → Int
  fromEnum = either fromEnum ((+) (fromIntegral cardinality_a) . fromEnum)
    where
      cardinality_a ∷ ℕ
      cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
  enumFrom ∷ Either a b → [Either a b]
  enumFrom = boundedEnumFrom
instance (Finite a, Finite b)
       ⇒ Finite (Either a b) where
  asList ∷ [Either a b]
  asList = (Left  <$> asList)
         ⋄ (Right <$> asList)
  asSet  ∷ Set (Either a b)
  asSet  = asSet ⊎ asSet

instance (Bounded a, Bounded b)
       ⇒ Bounded (These a b) where
  minBound ∷ These a b
  minBound = toThese minBound -- This  minBound
  maxBound ∷ These a b
  maxBound = toThese maxBound -- These maxBound maxBound
instance (Finite a, Finite b)
       ⇒ Enum (These a b) where
  toEnum   ∷ Int → These a b
  toEnum   = toThese . toEnum
  fromEnum ∷ These a b → Int
  fromEnum = fromEnum . fromThese
  enumFrom ∷ These a b → [These a b]
  enumFrom = boundedEnumFrom
instance (U.Universe a, U.Universe b)
       ⇒ U.Universe (These a b) where
  universe ∷ [These a b]
  universe = fmap toThese U.universe
instance (U.Finite a, U.Finite b)
       ⇒ U.Finite (These a b) where
  -- a + b + ab
  cardinality ∷ Tagged (These a b) ℕ
  cardinality = liftA2 (\a b → a + b + a * b) (retag (U.cardinality ∷ Tagged a ℕ)) (retag (U.cardinality ∷ Tagged b ℕ))
  universeF ∷ [These a b]
  universeF = fmap toThese U.universeF
instance (Finite a, Finite b)
       ⇒ Finite (These a b) where
  asList ∷ [These a b]
  asList = fmap toThese asList
  asSet  ∷ Set (These a b)
  asSet  = Set.map toThese asSet

-- EXPERIMENTAL
-- Wedge
instance (Bounded a, Bounded b)
       ⇒ Bounded (Wedge a b) where
  minBound ∷ Wedge a b
  minBound = toWedge minBound -- Nowhere
  maxBound ∷ Wedge a b
  maxBound = toWedge maxBound -- There maxBound
instance (Finite a, Finite b)
       ⇒ Enum (Wedge a b) where
  toEnum   ∷ Int → Wedge a b
  toEnum   = toWedge . toEnum
  fromEnum ∷ Wedge a b → Int
  fromEnum = fromEnum . fromWedge
  enumFrom ∷ Wedge a b → [Wedge a b]
  enumFrom = boundedEnumFrom
instance (U.Universe a, U.Universe b)
       ⇒ U.Universe (Wedge a b) where
  universe ∷ [Wedge a b]
  universe = fmap toWedge U.universe
instance (U.Finite a, U.Finite b)
       ⇒ U.Finite (Wedge a b) where
  -- 1 + a + b
  cardinality ∷ Tagged (Wedge a b) ℕ
  cardinality = liftA2 (\a b → 1 + a + b) (retag (U.cardinality ∷ Tagged a ℕ)) (retag (U.cardinality ∷ Tagged b ℕ))
  universeF ∷ [Wedge a b]
  universeF = fmap toWedge U.universeF
instance (Finite a, Finite b)
       ⇒ Finite (Wedge a b) where
  asList ∷ [Wedge a b]
  asList = fmap toWedge asList
  asSet  ∷ Set (Wedge a b)
  asSet  = Set.map toWedge asSet

-- Can
instance (Bounded a, Bounded b)
       ⇒ Bounded (Can a b) where
  minBound ∷ Can a b
  minBound = toCan minBound -- Non
  maxBound ∷ Can a b
  maxBound = toCan maxBound -- Two maxBound maxBound
instance (Finite a, Finite b)
       ⇒ Enum (Can a b) where
  toEnum   ∷ Int → Can a b
  toEnum   = toCan . toEnum
  fromEnum ∷ Can a b → Int
  fromEnum = fromEnum . fromCan
  enumFrom ∷ Can a b → [Can a b]
  enumFrom = boundedEnumFrom
instance (U.Universe a, U.Universe b)
       ⇒ U.Universe (Can a b) where
  universe ∷ [Can a b]
  universe = fmap toCan U.universe
instance (U.Finite a, U.Finite b)
       ⇒ U.Finite (Can a b) where
  -- 1 + a + b + ab
  cardinality ∷ Tagged (Can a b) ℕ
  cardinality = liftA2 (\a b → 1 + a + b + a * b) (retag (U.cardinality ∷ Tagged a ℕ)) (retag (U.cardinality ∷ Tagged b ℕ))
  universeF ∷ [Can a b]
  universeF = fmap toCan U.universeF
instance (Finite a, Finite b)
       ⇒ Finite (Can a b) where
  asList ∷ [Can a b]
  asList = fmap toCan asList
  asSet  ∷ Set (Can a b)
  asSet  = Set.map toCan asSet

-- Smash
instance (Bounded a, Bounded b)
       ⇒ Bounded (Smash a b) where
  minBound ∷ Smash a b
  minBound = toSmash minBound -- Nada
  maxBound ∷ Smash a b
  maxBound = toSmash maxBound -- Smash maxBound maxBound
instance (Finite a, Finite b)
       ⇒ Enum (Smash a b) where
  toEnum   ∷ Int → Smash a b
  toEnum   = toSmash . toEnum
  fromEnum ∷ Smash a b → Int
  -- fromEnum = smash 0 (\a b → succ (fromEnum (a, b)))
  -- fromEnum = smash 0 (succ ‥ (fromEnum ‥ (,)))
  fromEnum = fromEnum . fromSmash
  enumFrom ∷ Smash a b → [Smash a b]
  enumFrom = boundedEnumFrom
instance (U.Universe a, U.Universe b)
       ⇒ U.Universe (Smash a b) where
  universe ∷ [Smash a b]
  universe = fmap toSmash U.universe
instance (U.Finite a, U.Finite b)
       ⇒ U.Finite (Smash a b) where
  -- 1 + ab
  cardinality ∷ Tagged (Smash a b) ℕ
  cardinality = liftA2 (\a b → 1 + a * b) (retag (U.cardinality ∷ Tagged a ℕ)) (retag (U.cardinality ∷ Tagged b ℕ))
  universeF ∷ [Smash a b]
  universeF = fmap toSmash U.universeF
instance (Finite a, Finite b)
       ⇒ Finite (Smash a b) where
  asList ∷ [Smash a b]
  -- asList = Nada : fmap (toSmash . Just) (asList @ (a, b))
  asList = fmap toSmash asList
  asSet  ∷ Set (Smash a b)
  asSet  = Set.map toSmash asSet

-- For tuples where types `a` and `b` are enumerable, allow the tuple to be enumerated as `a` × `b`
instance (Bounded a, Enum a, U.Finite a, Bounded b, Enum b, U.Finite b)
       ⇒ Enum (a, b) where
  toEnum ∷ Int → (a, b)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ)
    where
      (i₁, bᵢ) = i₀ `quotRem` fromIntegral cardinality_b
        where
          cardinality_b ∷ ℕ
          cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      (_,  aᵢ) = i₁ `quotRem` fromIntegral cardinality_a
        where
          cardinality_a ∷ ℕ
          cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
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
  asSet  ∷ Set (a, b)
  asSet  = asSet × asSet
  asList ∷ [(a, b)]
  asList = liftA2 (,) asList asList

-- For tuples where types `a`, `b`, and `c` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c`
instance (Bounded a, Enum a, U.Finite a, Bounded b, Enum b, U.Finite b, Bounded c, Enum c, U.Finite c)
       ⇒ Enum (a, b, c) where
  toEnum ∷ Int → (a, b, c)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ)
    where
      (i₁, cᵢ) = i₀ `quotRem` fromIntegral cardinality_c
        where
          cardinality_c ∷ ℕ
          cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      (i₂, bᵢ) = i₁ `quotRem` fromIntegral cardinality_b
        where
          cardinality_b ∷ ℕ
          cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      (_,  aᵢ) = i₂ `quotRem` fromIntegral cardinality_a
        where
          cardinality_a ∷ ℕ
          cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
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
instance (Bounded a, Enum a, U.Finite a, Bounded b, Enum b, U.Finite b, Bounded c, Enum c, U.Finite c, Bounded d, Enum d, U.Finite d)
       ⇒ Enum (a, b, c, d) where
  toEnum ∷ Int → (a, b, c, d)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ, toEnum dᵢ)
    where
      (i₁, dᵢ) = i₀ `quotRem` fromIntegral cardinality_d ∷ (Int, Int)
        where
          cardinality_d ∷ ℕ
          cardinality_d = unTagged (U.cardinality ∷ Tagged d ℕ)
      (i₂, cᵢ) = i₁ `quotRem` fromIntegral cardinality_c ∷ (Int, Int)
        where
          cardinality_c ∷ ℕ
          cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      (i₃, bᵢ) = i₂ `quotRem` fromIntegral cardinality_b ∷ (Int, Int)
        where
          cardinality_b ∷ ℕ
          cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      (_,  aᵢ) = i₃ `quotRem` fromIntegral cardinality_a ∷ (Int, Int)
        where
          cardinality_a ∷ ℕ
          cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
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
  asList = liftA4 (,,,) asList asList asList asList

-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Bounded a, Enum a, U.Finite a, Bounded b, Enum b, U.Finite b, Bounded c, Enum c, U.Finite c, Bounded d, Enum d, U.Finite d, Bounded e, Enum e, U.Finite e)
       ⇒ Enum (a, b, c, d, e) where
  toEnum ∷ Int → (a, b, c, d, e)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ, toEnum dᵢ, toEnum eᵢ)
    where
      (i₁, eᵢ) = i₀ `quotRem` fromIntegral cardinality_e
        where
          cardinality_e ∷ ℕ
          cardinality_e = unTagged (U.cardinality ∷ Tagged e ℕ)
      (i₂, dᵢ) = i₁ `quotRem` fromIntegral cardinality_d
        where
          cardinality_d ∷ ℕ
          cardinality_d = unTagged (U.cardinality ∷ Tagged d ℕ)
      (i₃, cᵢ) = i₂ `quotRem` fromIntegral cardinality_c
        where
          cardinality_c ∷ ℕ
          cardinality_c = unTagged (U.cardinality ∷ Tagged c ℕ)
      (i₄, bᵢ) = i₃ `quotRem` fromIntegral cardinality_b
        where
          cardinality_b ∷ ℕ
          cardinality_b = unTagged (U.cardinality ∷ Tagged b ℕ)
      (_,  aᵢ) = i₄ `quotRem` fromIntegral cardinality_a
        where
          cardinality_a ∷ ℕ
          cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
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
  asList = liftA5 (,,,,) asList asList asList asList asList

instance (Finite a, Eq b) ⇒ Eq (a → b) where
  (==) ∷ (a → b) → (a → b) → Bool
  (==) = flip all asList ‥ liftA2 (==)

instance (Bounded b) ⇒ Bounded (a → b) where
  minBound ∷ (a → b)
  minBound = const minBound
  maxBound ∷ (a → b)
  maxBound = const maxBound

-- Something like Fin₀
instance Enum Void where
  toEnum   ∷ Int → Void
  toEnum   = undefined
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
  asSet  ∷ Set Void
  asSet  = (∅)

type Nat10  = 'Nat.S Nat.Nat9
type Nat11  = 'Nat.S Nat10
type Nat12  = 'Nat.S Nat11
type Nat13  = 'Nat.S Nat12
type Nat14  = 'Nat.S Nat13
type Nat15  = 'Nat.S Nat14
type Nat16  = 'Nat.S Nat15

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
type Fin₁₆ = Fin Nat16

-- "case analysis for `Fin₀` type" :)
fin₀ ∷ Fin₀ → a
fin₀ = Fin.absurd

-- case analysis for `Fin₁` type
fin₁ ∷ a → Fin₁ → a
fin₁ a 0 = a
fin₁ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₂` type
fin₂ ∷ a → a → Fin₂ → a
fin₂ a _ 0 = a
fin₂ _ a 1 = a
fin₂ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₃` type
fin₃ ∷ a → a → a → Fin₃ → a
fin₃ a _ _ 0 = a
fin₃ _ a _ 1 = a
fin₃ _ _ a 2 = a
fin₃ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₄` type
fin₄ ∷ a → a → a → a → Fin₄ → a
fin₄ a _ _ _ 0 = a
fin₄ _ a _ _ 1 = a
fin₄ _ _ a _ 2 = a
fin₄ _ _ _ a 3 = a
fin₄ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₅` type
fin₅ ∷ a → a → a → a → a → Fin₅ → a
fin₅ a _ _ _ _ 0 = a
fin₅ _ a _ _ _ 1 = a
fin₅ _ _ a _ _ 2 = a
fin₅ _ _ _ a _ 3 = a
fin₅ _ _ _ _ a 4 = a
fin₅ _ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₆` type
fin₆ ∷ a → a → a → a → a → a → Fin₆ → a
fin₆ a _ _ _ _ _ 0 = a
fin₆ _ a _ _ _ _ 1 = a
fin₆ _ _ a _ _ _ 2 = a
fin₆ _ _ _ a _ _ 3 = a
fin₆ _ _ _ _ a _ 4 = a
fin₆ _ _ _ _ _ a 5 = a
fin₆ _ _ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₇` type
fin₇ ∷ a → a → a → a → a → a → a → Fin₇ → a
fin₇ a _ _ _ _ _ _ 0 = a
fin₇ _ a _ _ _ _ _ 1 = a
fin₇ _ _ a _ _ _ _ 2 = a
fin₇ _ _ _ a _ _ _ 3 = a
fin₇ _ _ _ _ a _ _ 4 = a
fin₇ _ _ _ _ _ a _ 5 = a
fin₇ _ _ _ _ _ _ a 6 = a
fin₇ _ _ _ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₈` type
fin₈ ∷ a → a → a → a → a → a → a → a → Fin₈ → a
fin₈ a _ _ _ _ _ _ _ 0 = a
fin₈ _ a _ _ _ _ _ _ 1 = a
fin₈ _ _ a _ _ _ _ _ 2 = a
fin₈ _ _ _ a _ _ _ _ 3 = a
fin₈ _ _ _ _ a _ _ _ 4 = a
fin₈ _ _ _ _ _ a _ _ 5 = a
fin₈ _ _ _ _ _ _ a _ 6 = a
fin₈ _ _ _ _ _ _ _ a 7 = a
fin₈ _ _ _ _ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₉` type
fin₉ ∷ a → a → a → a → a → a → a → a → a → Fin₉ → a
fin₉ a _ _ _ _ _ _ _ _ 0 = a
fin₉ _ a _ _ _ _ _ _ _ 1 = a
fin₉ _ _ a _ _ _ _ _ _ 2 = a
fin₉ _ _ _ a _ _ _ _ _ 3 = a
fin₉ _ _ _ _ a _ _ _ _ 4 = a
fin₉ _ _ _ _ _ a _ _ _ 5 = a
fin₉ _ _ _ _ _ _ a _ _ 6 = a
fin₉ _ _ _ _ _ _ _ a _ 7 = a
fin₉ _ _ _ _ _ _ _ _ a 8 = a
fin₉ _ _ _ _ _ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₁₀` type
fin₁₀ ∷ a → a → a → a → a → a → a → a → a → a → Fin₁₀ → a
fin₁₀ a _ _ _ _ _ _ _ _ _ 0 = a
fin₁₀ _ a _ _ _ _ _ _ _ _ 1 = a
fin₁₀ _ _ a _ _ _ _ _ _ _ 2 = a
fin₁₀ _ _ _ a _ _ _ _ _ _ 3 = a
fin₁₀ _ _ _ _ a _ _ _ _ _ 4 = a
fin₁₀ _ _ _ _ _ a _ _ _ _ 5 = a
fin₁₀ _ _ _ _ _ _ a _ _ _ 6 = a
fin₁₀ _ _ _ _ _ _ _ a _ _ 7 = a
fin₁₀ _ _ _ _ _ _ _ _ a _ 8 = a
fin₁₀ _ _ _ _ _ _ _ _ _ a 9 = a
fin₁₀ _ _ _ _ _ _ _ _ _ _ _ = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₁₁` type
fin₁₁ ∷ a → a → a → a → a → a → a → a → a → a → a → Fin₁₁ → a
fin₁₁ a _ _ _ _ _ _ _ _ _ _ 0  = a
fin₁₁ _ a _ _ _ _ _ _ _ _ _ 1  = a
fin₁₁ _ _ a _ _ _ _ _ _ _ _ 2  = a
fin₁₁ _ _ _ a _ _ _ _ _ _ _ 3  = a
fin₁₁ _ _ _ _ a _ _ _ _ _ _ 4  = a
fin₁₁ _ _ _ _ _ a _ _ _ _ _ 5  = a
fin₁₁ _ _ _ _ _ _ a _ _ _ _ 6  = a
fin₁₁ _ _ _ _ _ _ _ a _ _ _ 7  = a
fin₁₁ _ _ _ _ _ _ _ _ a _ _ 8  = a
fin₁₁ _ _ _ _ _ _ _ _ _ a _ 9  = a
fin₁₁ _ _ _ _ _ _ _ _ _ _ a 10 = a
fin₁₁ _ _ _ _ _ _ _ _ _ _ _ _  = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₁₂` type
fin₁₂ ∷ a → a → a → a → a → a → a → a → a → a → a → a → Fin₁₂ → a
fin₁₂ a _ _ _ _ _ _ _ _ _ _ _ 0  = a
fin₁₂ _ a _ _ _ _ _ _ _ _ _ _ 1  = a
fin₁₂ _ _ a _ _ _ _ _ _ _ _ _ 2  = a
fin₁₂ _ _ _ a _ _ _ _ _ _ _ _ 3  = a
fin₁₂ _ _ _ _ a _ _ _ _ _ _ _ 4  = a
fin₁₂ _ _ _ _ _ a _ _ _ _ _ _ 5  = a
fin₁₂ _ _ _ _ _ _ a _ _ _ _ _ 6  = a
fin₁₂ _ _ _ _ _ _ _ a _ _ _ _ 7  = a
fin₁₂ _ _ _ _ _ _ _ _ a _ _ _ 8  = a
fin₁₂ _ _ _ _ _ _ _ _ _ a _ _ 9  = a
fin₁₂ _ _ _ _ _ _ _ _ _ _ a _ 10 = a
fin₁₂ _ _ _ _ _ _ _ _ _ _ _ a 11 = a
fin₁₂ _ _ _ _ _ _ _ _ _ _ _ _ _  = impossible -- add unreachable case to get rid of GHC warning


-- case analysis for `Fin₁₃` type
fin₁₃ ∷ a → a → a → a → a → a → a → a → a → a → a → a → a → Fin₁₃ → a
fin₁₃ a _ _ _ _ _ _ _ _ _ _ _ _ 0  = a
fin₁₃ _ a _ _ _ _ _ _ _ _ _ _ _ 1  = a
fin₁₃ _ _ a _ _ _ _ _ _ _ _ _ _ 2  = a
fin₁₃ _ _ _ a _ _ _ _ _ _ _ _ _ 3  = a
fin₁₃ _ _ _ _ a _ _ _ _ _ _ _ _ 4  = a
fin₁₃ _ _ _ _ _ a _ _ _ _ _ _ _ 5  = a
fin₁₃ _ _ _ _ _ _ a _ _ _ _ _ _ 6  = a
fin₁₃ _ _ _ _ _ _ _ a _ _ _ _ _ 7  = a
fin₁₃ _ _ _ _ _ _ _ _ a _ _ _ _ 8  = a
fin₁₃ _ _ _ _ _ _ _ _ _ a _ _ _ 9  = a
fin₁₃ _ _ _ _ _ _ _ _ _ _ a _ _ 10 = a
fin₁₃ _ _ _ _ _ _ _ _ _ _ _ a _ 11 = a
fin₁₃ _ _ _ _ _ _ _ _ _ _ _ _ a 12 = a
fin₁₃ _ _ _ _ _ _ _ _ _ _ _ _ _ _  = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₁₄` type
fin₁₄ ∷ a → a → a → a → a → a → a → a → a → a → a → a → a → a → Fin₁₄ → a
fin₁₄ a _ _ _ _ _ _ _ _ _ _ _ _ _ 0  = a
fin₁₄ _ a _ _ _ _ _ _ _ _ _ _ _ _ 1  = a
fin₁₄ _ _ a _ _ _ _ _ _ _ _ _ _ _ 2  = a
fin₁₄ _ _ _ a _ _ _ _ _ _ _ _ _ _ 3  = a
fin₁₄ _ _ _ _ a _ _ _ _ _ _ _ _ _ 4  = a
fin₁₄ _ _ _ _ _ a _ _ _ _ _ _ _ _ 5  = a
fin₁₄ _ _ _ _ _ _ a _ _ _ _ _ _ _ 6  = a
fin₁₄ _ _ _ _ _ _ _ a _ _ _ _ _ _ 7  = a
fin₁₄ _ _ _ _ _ _ _ _ a _ _ _ _ _ 8  = a
fin₁₄ _ _ _ _ _ _ _ _ _ a _ _ _ _ 9  = a
fin₁₄ _ _ _ _ _ _ _ _ _ _ a _ _ _ 10 = a
fin₁₄ _ _ _ _ _ _ _ _ _ _ _ a _ _ 11 = a
fin₁₄ _ _ _ _ _ _ _ _ _ _ _ _ a _ 12 = a
fin₁₄ _ _ _ _ _ _ _ _ _ _ _ _ _ a 13 = a
fin₁₄ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₁₅` type
fin₁₅ ∷ a → a → a → a → a → a → a → a → a → a → a → a → a → a → a → Fin₁₅ → a
fin₁₅ a _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0  = a
fin₁₅ _ a _ _ _ _ _ _ _ _ _ _ _ _ _ 1  = a
fin₁₅ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ 2  = a
fin₁₅ _ _ _ a _ _ _ _ _ _ _ _ _ _ _ 3  = a
fin₁₅ _ _ _ _ a _ _ _ _ _ _ _ _ _ _ 4  = a
fin₁₅ _ _ _ _ _ a _ _ _ _ _ _ _ _ _ 5  = a
fin₁₅ _ _ _ _ _ _ a _ _ _ _ _ _ _ _ 6  = a
fin₁₅ _ _ _ _ _ _ _ a _ _ _ _ _ _ _ 7  = a
fin₁₅ _ _ _ _ _ _ _ _ a _ _ _ _ _ _ 8  = a
fin₁₅ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ 9  = a
fin₁₅ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ 10 = a
fin₁₅ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ 11 = a
fin₁₅ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ 12 = a
fin₁₅ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ 13 = a
fin₁₅ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 14 = a
fin₁₅ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  = impossible -- add unreachable case to get rid of GHC warning

-- case analysis for `Fin₁₆` type
fin₁₆ ∷ a → a → a → a → a → a → a → a → a → a → a → a → a → a → a → a → Fin₁₆ → a
fin₁₆ a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0  = a
fin₁₆ _ a _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1  = a
fin₁₆ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ _ 2  = a
fin₁₆ _ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ 3  = a
fin₁₆ _ _ _ _ a _ _ _ _ _ _ _ _ _ _ _ 4  = a
fin₁₆ _ _ _ _ _ a _ _ _ _ _ _ _ _ _ _ 5  = a
fin₁₆ _ _ _ _ _ _ a _ _ _ _ _ _ _ _ _ 6  = a
fin₁₆ _ _ _ _ _ _ _ a _ _ _ _ _ _ _ _ 7  = a
fin₁₆ _ _ _ _ _ _ _ _ a _ _ _ _ _ _ _ 8  = a
fin₁₆ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ _ 9  = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ 10 = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ 11 = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ 12 = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ 13 = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ 14 = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 15 = a
fin₁₆ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  = impossible -- add unreachable case to get rid of GHC warning

-- FIXME finish idea about partition₀

partition₁ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₁) → f a → [a]
partition₁ cmp = foldr select' [] . toList
  where
    select' ∷ a → [a] → [a]
    select' a eq = fin₁
                     (a : eq)
                   (cmp a)

partition₂ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₂) → f a → ([a], [a])
partition₂ cmp = foldr select' ([], []) . toList
  where
    select' ∷ a → ([a], [a]) → ([a], [a])
    select' a ~(lt, gt) = fin₂
                            (a : lt,     gt)
                            (    lt, a : gt)
                          (cmp a)

partition₃ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₃) → f a → ([a], [a], [a])
partition₃ cmp = foldr select' ([], [], []) . toList
  where
    select' ∷ a → ([a], [a], [a]) → ([a], [a], [a])
    select' a ~(lt, eq, gt) = fin₃
                                (a : lt,     eq,     gt)
                                (    lt, a : eq,     gt)
                                (    lt,     eq, a : gt)
                              (cmp a)

partition₄ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₄) → f a → ([a], [a], [a], [a])
partition₄ cmp = foldr select' ([], [], [], []) . toList
  where
    select' ∷ a → ([a], [a], [a], [a]) → ([a], [a], [a], [a])
    select' a ~(i, ii, iii, iv) = fin₄
                                    (a : i,     ii,     iii,     iv)
                                    (    i, a : ii,     iii,     iv)
                                    (    i,     ii, a : iii,     iv)
                                    (    i,     ii,     iii, a : iv)
                                  (cmp a)

partition₅ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₅) → f a → ([a], [a], [a], [a], [a])
partition₅ cmp = foldr select' ([], [], [], [], []) . toList
  where
    select' ∷ a → ([a], [a], [a], [a], [a]) → ([a], [a], [a], [a], [a])
    select' a ~(i, ii, iii, iv, v) = fin₅
                                       (a : i,     ii,     iii,     iv,     v)
                                       (    i, a : ii,     iii,     iv,     v)
                                       (    i,     ii, a : iii,     iv,     v)
                                       (    i,     ii,     iii, a : iv,     v)
                                       (    i,     ii,     iii,     iv, a : v)
                                     (cmp a)
partition₆ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₆) → f a → ([a], [a], [a], [a], [a], [a])
partition₆ cmp = foldr select' ([], [], [], [], [], []) . toList
  where
    select' ∷ a → ([a], [a], [a], [a], [a], [a]) → ([a], [a], [a], [a], [a], [a])
    select' a ~(i, ii, iii, iv, v, vi) = fin₆
                                           (a : i,     ii,     iii,     iv,     v,     vi)
                                           (    i, a : ii,     iii,     iv,     v,     vi)
                                           (    i,     ii, a : iii,     iv,     v,     vi)
                                           (    i,     ii,     iii, a : iv,     v,     vi)
                                           (    i,     ii,     iii,     iv, a : v,     vi)
                                           (    i,     ii,     iii,     iv,     v, a : vi)
                                         (cmp a)

partition₇ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₇) → f a → ([a], [a], [a], [a], [a], [a], [a])
partition₇ cmp = foldr select' ([], [], [], [], [], [], []) . toList
  where
    select' ∷ a → ([a], [a], [a], [a], [a], [a], [a]) → ([a], [a], [a], [a], [a], [a], [a])
    select' a ~(i, ii, iii, iv, v, vi, vii) = fin₇
                                                (a : i,     ii,     iii,     iv,     v,     vi,     vii)
                                                (    i, a : ii,     iii,     iv,     v,     vi,     vii)
                                                (    i,     ii, a : iii,     iv,     v,     vi,     vii)
                                                (    i,     ii,     iii, a : iv,     v,     vi,     vii)
                                                (    i,     ii,     iii,     iv, a : v,     vi,     vii)
                                                (    i,     ii,     iii,     iv,     v, a : vi,     vii)
                                                (    i,     ii,     iii,     iv,     v,     vi, a : vii)
                                              (cmp a)

partition₈ ∷ ∀ f a . (Foldable f) ⇒ (a → Fin₈) → f a → ([a], [a], [a], [a], [a], [a], [a], [a])
partition₈ cmp = foldr select' ([], [], [], [], [], [], [], []) . toList
  where
    select' ∷ a → ([a], [a], [a], [a], [a], [a], [a], [a]) → ([a], [a], [a], [a], [a], [a], [a], [a])
    select' a ~(i, ii, iii, iv, v, vi, vii, viii) = fin₈
                                                      (a : i,     ii,     iii,     iv,     v,     vi,     vii,     viii)
                                                      (    i, a : ii,     iii,     iv,     v,     vi,     vii,     viii)
                                                      (    i,     ii, a : iii,     iv,     v,     vi,     vii,     viii)
                                                      (    i,     ii,     iii, a : iv,     v,     vi,     vii,     viii)
                                                      (    i,     ii,     iii,     iv, a : v,     vi,     vii,     viii)
                                                      (    i,     ii,     iii,     iv,     v, a : vi,     vii,     viii)
                                                      (    i,     ii,     iii,     iv,     v,     vi, a : vii,     viii)
                                                      (    i,     ii,     iii,     iv,     v,     vi,     vii, a : viii)
                                                    (cmp a)

-- non unicode aliases for convenience
fin0  ∷                                                                                 Fin₀ → a
fin0  = fin₀
fin1  ∷                                                                            a → (Fin₁ → a)
fin1  = fin₁
fin2  ∷                                                                       a → (a → (Fin₂ → a))
fin2  = fin₂
fin3  ∷                                                                  a → (a → (a → (Fin₃ → a)))
fin3  = fin₃
fin4  ∷                                                             a → (a → (a → (a → (Fin₄ → a))))
fin4  = fin₄
fin5  ∷                                                        a → (a → (a → (a → (a → (Fin₅ → a)))))
fin5  = fin₅
fin6  ∷                                                   a → (a → (a → (a → (a → (a → (Fin₆ → a))))))
fin6  = fin₆
fin7  ∷                                              a → (a → (a → (a → (a → (a → (a → (Fin₇ → a)))))))
fin7  = fin₇
fin8  ∷                                         a → (a → (a → (a → (a → (a → (a → (a → (Fin₈ → a))))))))
fin8  = fin₈
fin9  ∷                                    a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₉ → a)))))))))
fin9  = fin₉
fin10 ∷                               a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₀ → a))))))))))
fin10 = fin₁₀
fin11 ∷                          a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₁ → a)))))))))))
fin11 = fin₁₁
fin12 ∷                     a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₂ → a))))))))))))
fin12 = fin₁₂
fin13 ∷                a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₃ → a)))))))))))))
fin13 = fin₁₃
fin14 ∷           a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₄ → a))))))))))))))
fin14 = fin₁₄
fin15 ∷      a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₅ → a)))))))))))))))
fin15 = fin₁₅
fin16 ∷ a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (a → (Fin₁₆ → a))))))))))))))))
fin16 = fin₁₆

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
type Fin16 = Fin₁₆

instance U.Universe Fin₀ where
  universe ∷ [Fin₀]
  universe = []
instance U.Finite Fin₀ where
  cardinality ∷ Tagged Fin₀ ℕ
  cardinality = Tagged 0

instance U.Universe Fin₁
instance U.Finite   Fin₁ where
  cardinality ∷ Tagged Fin₁ ℕ
  cardinality = Tagged 1
instance Finite     Fin₁

instance U.Universe Fin₂
instance U.Finite   Fin₂ where
  cardinality ∷ Tagged Fin₂ ℕ
  cardinality = Tagged 2
instance Finite     Fin₂

-- Addition modulo 3
-- https://proofwiki.org/wiki/Modulo_Addition/Cayley_Table/Modulo_3
instance Semigroup Fin₃ where
  (<>) ∷ Fin₃ → Fin₃ → Fin₃
  (<>) = toEnum' ‥ (flip mod 3 ‥ ((+) `on` Fin.toNatural))
instance Monoid Fin₃ where
  mempty ∷ Fin₃
  mempty = 0
-- 0 +₃ 0 = 0
-- 1 +₃ 2 = 0
-- 2 +₃ 1 = 0
instance Group Fin₃ where
  invert ∷ Fin₃ → Fin₃
  invert = fin₃ 0 2 1
instance U.Universe Fin₃
instance U.Finite   Fin₃ where
  cardinality ∷ Tagged Fin₃ ℕ
  cardinality = Tagged 3
instance Finite     Fin₃

-- Addition modulo 4
-- https://proofwiki.org/wiki/Modulo_Addition/Cayley_Table/Modulo_4
instance Semigroup Fin₄ where
  (<>) ∷ Fin₄ → Fin₄ → Fin₄
  (<>) = toEnum' ‥ (flip mod 4 ‥ ((+) `on` Fin.toNatural))
instance Monoid Fin₄ where
  mempty ∷ Fin₄
  mempty = 0
-- 0 +₄ 0 = 0
-- 1 +₄ 3 = 0
-- 2 +₄ 2 = 0
-- 3 +₄ 1 = 0
instance Group Fin₄ where
  invert ∷ Fin₄ → Fin₄
  invert = fin₄ 0 3 2 1
instance U.Universe Fin₄
instance U.Finite   Fin₄ where
  cardinality ∷ Tagged Fin₄ ℕ
  cardinality = Tagged 4
instance Finite     Fin₄

-- Addition modulo 5
-- https://proofwiki.org/wiki/Modulo_Addition/Cayley_Table/Modulo_5
instance Semigroup Fin₅ where
  (<>) ∷ Fin₅ → Fin₅ → Fin₅
  (<>) = toEnum' ‥ (flip mod 5 ‥ ((+) `on` Fin.toNatural))
instance Monoid Fin₅ where
  mempty ∷ Fin₅
  mempty = 0
-- 0 +₅ 0 = 0
-- 1 +₅ 4 = 0
-- 2 +₅ 3 = 0
-- 3 +₅ 2 = 0
-- 4 +₅ 1 = 0
instance Group Fin₅ where
  invert ∷ Fin₅ → Fin₅
  invert = fin₅ 0 4 3 2 1
instance U.Universe Fin₅
instance U.Finite   Fin₅ where
  cardinality ∷ Tagged Fin₅ ℕ
  cardinality = Tagged 5
instance Finite     Fin₅

-- Addition modulo 6
-- https://proofwiki.org/wiki/Modulo_Addition/Cayley_Table/Modulo_6
instance Semigroup Fin₆ where
  (<>) ∷ Fin₆ → Fin₆ → Fin₆
  (<>) = toEnum' ‥ (flip mod 6 ‥ ((+) `on` Fin.toNatural))
instance Monoid Fin₆ where
  mempty ∷ Fin₆
  mempty = 0
-- 0 +₆ 0 = 0
-- 1 +₆ 5 = 0
-- 2 +₆ 4 = 0
-- 3 +₆ 3 = 0
-- 4 +₆ 2 = 0
-- 5 +₆ 1 = 0
instance Group Fin₆ where
  invert ∷ Fin₆ → Fin₆
  invert = fin₆ 0 5 4 3 2 1
instance U.Universe Fin₆
instance U.Finite   Fin₆ where
  cardinality ∷ Tagged Fin₆ ℕ
  cardinality = Tagged 6
instance Finite     Fin₆

instance U.Universe Fin₇
instance U.Finite   Fin₇ where
  cardinality ∷ Tagged Fin₇ ℕ
  cardinality = Tagged 7
instance Finite     Fin₇

-- Addition modulo 8
instance Semigroup Fin₈ where
  (<>) ∷ Fin₈ → Fin₈ → Fin₈
  (<>) = toEnum' ‥ (flip mod 8 ‥ ((+) `on` Fin.toNatural))
instance Monoid Fin₈ where
  mempty ∷ Fin₈
  mempty = 0
instance Group Fin₈ where
  invert ∷ Fin₈ → Fin₈
  invert = fin₈ 0 7 6 5 4 3 2 1
instance U.Universe Fin₈
instance U.Finite   Fin₈ where
  cardinality ∷ Tagged Fin₈ ℕ
  cardinality = Tagged 8
instance Finite     Fin₈

instance U.Universe Fin₉
instance U.Finite   Fin₉ where
  cardinality ∷ Tagged Fin₉ ℕ
  cardinality = Tagged 9
instance Finite     Fin₉

instance U.Universe Fin₁₀
instance U.Finite   Fin₁₀ where
  cardinality ∷ Tagged Fin₁₀ ℕ
  cardinality = Tagged 10
instance Finite     Fin₁₀

instance U.Universe Fin₁₁
instance U.Finite   Fin₁₁ where
  cardinality ∷ Tagged Fin₁₁ ℕ
  cardinality = Tagged 11
instance Finite     Fin₁₁

instance U.Universe Fin₁₂
instance U.Finite   Fin₁₂ where
  cardinality ∷ Tagged Fin₁₂ ℕ
  cardinality = Tagged 12
instance Finite     Fin₁₂

instance U.Universe Fin₁₃
instance U.Finite   Fin₁₃ where
  cardinality ∷ Tagged Fin₁₃ ℕ
  cardinality = Tagged 13
instance Finite     Fin₁₃

instance U.Universe Fin₁₄
instance U.Finite   Fin₁₄ where
  cardinality ∷ Tagged Fin₁₄ ℕ
  cardinality = Tagged 14
instance Finite     Fin₁₄

instance U.Universe Fin₁₅
instance U.Finite   Fin₁₅ where
  cardinality ∷ Tagged Fin₁₅ ℕ
  cardinality = Tagged 15
instance Finite     Fin₁₅

instance U.Universe Fin₁₆
instance U.Finite   Fin₁₆ where
  cardinality ∷ Tagged Fin₁₆ ℕ
  cardinality = Tagged 16
instance Finite     Fin₁₆

instance (Show a, Finite a) ⇒ Show (Predicate a) where
  show ∷ Predicate a → String
  show = showpredpart
    where
      -- show predicate as a bitstring
      showpredbits ∷ ∀ a . (Finite a) ⇒ Predicate a → String
      showpredbits = (<&>) asList . (bool '0' '1' ‥ getPredicate)
      -- show predicate as a function
      showpredf ∷ ∀ a . (Show a, Finite a) ⇒ Predicate a → String
      showpredf (Predicate p) = unlines (fmap (\(a, b) → quoteWith (show a) (show b) " ↦ ") graph)
        where
          graph ∷ [(a, Bool)]
          graph = zip domain image
            where
              domain ∷ [a]
              domain = asList
              image ∷ [Bool]
              image = fmap p domain
      -- show predicate as a set
      showpredset ∷ ∀ a . (Show a, Finite a) ⇒ Predicate a → String
      showpredset = show . Set' . flip Set.filter asSet . getPredicate
      -- show the elements of 'a', with coloring determined by the predicate
      showcolors ∷ ∀ a . (Show a, Finite a) ⇒ Predicate a → String
      -- showcolors (Predicate p) = concatMap (\a → bool ((flip toColor) Red (show a)) ((flip toColor) Green (show a)) (p a)) asList
      showcolors = (>>=) asList . liftA3 bool ((`toColor` Red) . show) ((`toColor` Green) . show) . getPredicate
      -- show predicate as a partitioned set
      showpredpart ∷ ∀ a . (Show a, Finite a) ⇒ Predicate a → String
      showpredpart = quoteWith "{"  "}" . intercalate ", " . fmap (either ((`toColor` Red) . show) ((`toColor` Green) . show)) . label
        where
          -- label each `a` such that
          -- `Left  a` ≢ p a
          -- `Right a` ≡ p a
          label ∷ (Finite a) ⇒ Predicate a → [Either a a]
          label = (<&>) asList . liftA3 bool Left Right . getPredicate

instance (Finite a)
       ⇒ Eq (Predicate a) where
  (==) ∷ Predicate a → Predicate a → Bool
  (==) (Predicate p₁) (Predicate p₂) = all (liftA2 (==) p₁ p₂) asList
instance Bounded (Predicate a) where
  minBound ∷ Predicate a
  minBound = Predicate (const False)
  maxBound ∷ Predicate a
  maxBound = Predicate (const True)
instance (Finite a)
       ⇒ Ord (Predicate a) where
  compare ∷ Predicate a → Predicate a → Ordering
  compare (Predicate p₁) (Predicate p₂) = foldMap (liftA2 compare p₁ p₂) asList
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
      bits ∷ [[Bool]]
      bits = replicateM' cardinality_a bs
        where
          bs ∷ [Bool]
          bs = asList
          cardinality_a ∷ ℕ
          cardinality_a = unTagged (U.cardinality ∷ Tagged a ℕ)
      toFunction ∷ [(a, Bool)] → a → Bool
      toFunction = fromJust ‥ flip lookup

-- TODO may want to move this code (if keeping it) to testing folder when done implementing `Finite` instance for `Equivalence`.

-- Restricted Growth String type, where `a` is the
-- underlying `Finite` type.
-- TODO this might be better as `NonEmpty ℕ → RGS a`?
--
-- TODO Pg. 163 "RGS serves as the /digits/ of a number system, while the edge weights serve as the /coefficients/."
data RGS a where
  RGS ∷ (Finite a) ⇒ [ℕ] → RGS a

getRGS ∷ (Finite a) ⇒ RGS a → [ℕ]
getRGS (RGS rgs) = rgs

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
  (==) = (==) `on` getRGS

instance (Finite a) ⇒ Ord (RGS a) where
  compare ∷ RGS a → RGS a → Ordering
  compare = compare `on` getRGS

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

-- TODO lots of room for improvement here, but this works for now
-- This function takes two RGSs over the same finite type `a`, and returns a list of all indices
-- for which the element of `a` gets sent to differing blocks (a /block/ is a disjoint part of a set partition).
-- It is perhaps worth noting that the implemented `restricted` condition always requires a₁ = 0, so two `RGS` should
-- never disagree at index 0.
disagreements ∷ (Finite a) ⇒ RGS a → RGS a → [ℕ]
disagreements (RGS rgs₁) (RGS rgs₂) = fmap snd (List.filter ((≠) EQ . fst) (indexed (zipWith compare rgs₁ rgs₂)))

-- TODO may change this definition slightly and also the type signature
-- TODO testing
-- Two partitionings are said to be /close/ when they only differ by moving exactly one element to a new block.
close ∷ (Finite a) ⇒ Equivalence a → Equivalence a → Bool
close (⮂) (⮀) = (==) (1 ∷ ℕ) (genericLength (disagreements (toRGS (⮂)) (toRGS (⮀))))

-- TODO I think I tested this version in GHCI earlier but still need to add to test suit
-- TODO a lot to rework/clean up here but this works for now
-- TODO better name?
-- Checks the following two conditions:
-- a₁ = 0
-- and
-- aᵢ₊₁ ≤ 1 + max (a₁, a₂, ..., aᵢ)
restricted ∷ Predicate (NonEmpty ℕ)
restricted = Predicate p
  where
    p ∷ NonEmpty ℕ → Bool
    p (0 :| t) = res
      where
        (res, _) = foldl check (True, 0) t
          where
            check ∷ (Bool, ℕ) → ℕ → (Bool, ℕ)
            check     (True,  maxₙ) n = (n ≤ maxₙ + 1, max maxₙ n)
            check ret@(False, _   ) _ = ret
    p (_ :| _) = False
    -- p ∷ NonEmpty ℕ → Bool
    -- p (0 :| t) = fst (foldl (uncurry ((bool (const . ((,) False)) ((liftA2 (,) . (≥) . succ) <*> max)))) (True, 0) t)
    -- p _        = False

-- TODO https://proofwiki.org/wiki/Definition:Cycle_Decomposition
cycles ∷ (Finite a) ⇒ Comparison a → Equivalence a
cycles = Equivalence . ((∋) ‥ orbit)

-- " the orbit of an element is all its possible destinations under the group action."
-- https://proofwiki.org/wiki/Definition:Orbit_(Group_Theory)
orbit ∷ (Finite a) ⇒ Comparison a → a → NonEmpty a
orbit c a = a :| takeWhile (≠ a) (iterate (representativeC c) (representativeC c a))
{-
-- TODO
orbit ∷ ∀ a . (Finite a) ⇒ Comparison a → a → NonEmpty a
orbit cmp a₁ = NE.unfoldr c a₁
  where
    -- take an `a` and then give it back (i.e. we get identity for free), with possibly
    -- an even further destinatiton
    c ∷ a → (a, Maybe a) -- if acting on `a` changes it, we can return just the change, otherwise nothing :)
    c a₂ = (a₂, act cmp a₂ `when'` (act cmp a₂ ≠ a₁))
-}

-- FIXME
-- ~the least number of times the permutation has to be composed with itself
-- such that it would "become" the identity function.
--
-- https://en.wikipedia.org/wiki/Permutation#Permutation_order
-- "It is the least common multiple of its cycles lengths. For example, the order of (1 3 2)(4 5) is 2 * 3 = 6."
order ∷ (Finite a) ⇒ Comparison a → ℕ
order = foldl lcm 1 . fmap length' . fromEquivalence . cycles

eqOrder ∷ (Finite a) ⇒ Equivalence (Comparison a)
eqOrder = equating' order

-- Count the number of elements for which the predicate returns `True`
countImage ∷ (Finite a) ⇒ Predicate a → ℕ
countImage = length' . flip filter' asList

-- Something like `a`'s powerset grouped by size
eqCountingImage ∷ (Finite a) ⇒ Equivalence (Predicate a)
eqCountingImage = equating' countImage

-- Count the parts of an equivalence
countParts ∷ (Finite a) ⇒ Equivalence a → ℕ
countParts = genericLength . fromEquivalence

eqCountingParts ∷ (Finite a) ⇒ Equivalence (Equivalence a)
eqCountingParts = equating' countParts

eqLength ∷ (Foldable t) ⇒ Equivalence (t a)
eqLength = equating' length

-- group "pieces of pie" (equivalence classes) which are the same size (length)
eqEqClassLength ∷ (Finite a) ⇒ Equivalence a → Equivalence a
eqEqClassLength = (>&<) (eqLength ∷ Equivalence (NonEmpty a)) . equivalenceClass

shape ∷ (Finite a) ⇒ Equivalence a → [ℕ]
shape = sort . fmap length' . fromEquivalence

eqShape ∷ (Finite a) ⇒ Equivalence (Equivalence a)
eqShape = equating' shape

-- TODO consider moving to src/Common.hs
-- Some equivalence relations formed by equating constructors.

eqMaybe ∷ Equivalence (Maybe a)
eqMaybe = comparisonEquivalence cmpMaybe

eqCan ∷ Equivalence (Can a b)
eqCan = comparisonEquivalence cmpCan

eqSmash ∷ Equivalence (Smash a b)
eqSmash = comparisonEquivalence cmpSmash

eqWedge ∷ Equivalence (Wedge a b)
eqWedge = comparisonEquivalence cmpWedge

eqThese ∷ Equivalence (These a b)
eqThese = comparisonEquivalence cmpThese

eqEither ∷ Equivalence (Either a b)
eqEither = comparisonEquivalence cmpEither

eqLefts ∷ (Foldable t, Eq a) ⇒ Equivalence (t (Either a b))
eqLefts = equating' lefts'

eqRights ∷ (Foldable t, Eq b) ⇒ Equivalence (t (Either a b))
eqRights = equating' rights'

-- Some total orderings based on comparing constructors.
cmpMaybe ∷ Comparison (Maybe a)
cmpMaybe = Comparison c
  where
    c ∷ Maybe a → Maybe a → Ordering
    c Nothing  Nothing  = EQ
    c Nothing  (Just _) = LT
    c (Just _) Nothing  = GT
    c (Just _) (Just _) = EQ

cmpCan ∷ Comparison (Can a b)
cmpCan = Comparison c
  where
    c ∷ Can b c → Can b c → Ordering
    c C.Non       C.Non       = EQ
    c C.Non       (C.One _  ) = LT
    c C.Non       (C.Eno   _) = LT
    c C.Non       (C.Two _ _) = LT
    c (C.One _  ) C.Non       = GT
    c (C.One _  ) (C.One _  ) = EQ
    c (C.One _  ) (C.Eno   _) = LT
    c (C.One _  ) (C.Two _ _) = LT
    c (C.Eno   _) C.Non       = GT
    c (C.Eno   _) (C.One _  ) = GT
    c (C.Eno   _) (C.Eno   _) = EQ
    c (C.Eno   _) (C.Two _ _) = LT
    c (C.Two _ _) C.Non       = GT
    c (C.Two _ _) (C.One _  ) = GT
    c (C.Two _ _) (C.Eno   _) = GT
    c (C.Two _ _) (C.Two _ _) = EQ

cmpSmash ∷ Comparison (Smash a b)
cmpSmash = Comparison c
  where
    c ∷ Smash a b → Smash a b → Ordering
    c Nada        Nada        = EQ
    c Nada        (Smash _ _) = LT
    c (Smash _ _) Nada        = GT
    c (Smash _ _) (Smash _ _) = EQ

cmpWedge ∷ Comparison (Wedge a b)
cmpWedge = Comparison c
  where
    c ∷ Wedge a b → Wedge a b → Ordering
    c Nowhere   Nowhere   = EQ
    c Nowhere   (Here  _) = LT
    c Nowhere   (There _) = LT
    c (Here  _) Nowhere   = GT
    c (Here  _) (Here  _) = EQ
    c (Here  _) (There _) = LT
    c (There _) Nowhere   = GT
    c (There _) (Here  _) = GT
    c (There _) (There _) = EQ

cmpThese ∷ Comparison (These a b)
cmpThese = Comparison c
  where
    c ∷ These a b → These a b → Ordering
    c (This  _  ) (This  _  ) = EQ
    c (This  _  ) (That    _) = LT
    c (This  _  ) (These _ _) = LT
    c (That    _) (This  _  ) = GT
    c (That    _) (That    _) = EQ
    c (That    _) (These _ _) = LT
    c (These _ _) (This  _  ) = GT
    c (These _ _) (That    _) = GT
    c (These _ _) (These _ _) = EQ

cmpEither ∷ Comparison (Either a b)
cmpEither = Comparison c
  where
    c ∷ Either a b → Either a b → Ordering
    c (Left  _) (Left  _) = EQ
    c (Left  _) (Right _) = LT
    c (Right _) (Right _) = EQ
    c (Right _) (Left  _) = GT

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
    p c = all (\(a₁, a₂) → ((a₁ ≤ a₂) ∧ (a₂ ≤ a₁)) `implies` (a₁ ≡ a₂)) asSet
      where
        (≤) ∷ a → a → Bool
        (≤) = tolteq c
        (≡) ∷ a → a → Bool
        (≡) = getEquivalence (comparisonEquivalence c)

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
-- reverseC c = Comparison (flip (getComparison c))
-- reverseC = Comparison . flip . getComparison

-- Checks to make sure no two indices match between the two total orders
-- https://mathworld.wolfram.com/Derangement.html
derangement ∷ (Finite a) ⇒ Comparison a → Comparison a → Bool
derangement c₁ c₂ = and (zipWith (≠) (comparisonToList c₁) (comparisonToList c₂))

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
elemIndexTotal permutation a = fromJust (elemIndex' a (toList permutation))

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
-- representativeC = getOp . contramap fromEnum' . Op . genericIndex . comparisonToList

-- I mean technically you could :P lol
equivalenceClassC ∷ (Finite a) ⇒ Comparison a → a → NonEmpty a
equivalenceClassC = pure ‥ representativeC

-- TODO
composeC ∷ ∀ a . (Finite a) ⇒ Comparison a → Comparison a → Comparison a
composeC c₁ c₂ = listToComparison (fmap (representativeC c₁ . representativeC c₂) asList)
-- composeC c₁ c₂ = listToComparison (flip fmap asList (((.) `on` representativeC) c₁ c₂))

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
      _showp ∷ ∀ a . (Show a, Finite a) ⇒ Comparison a → String
      _showp cmp = quoteWith (top asList) (bot (comparisonToList cmp)) "\n"
        where
          top ∷ [a] → String
          top = quoteWith "⦍" "⦐" . (=<<) show
          bot ∷ [a] → String
          bot = quoteWith "⦏" "⦎" . (=<<) show
      -- show a Comparison as a permutation (in cyclic notation)
      _showc ∷ ∀ a . (Show a, Finite a) ⇒ Comparison a → String
      _showc cmp = (=<<) (quoteWith "(" ")" . intercalate " " . toList . fmap show) orbits
        where
          orbits ∷ [NonEmpty a]
          orbits = fromEquivalence (cycles cmp)
      -- show Comparison as a function
      _showf ∷ ∀ a . (Show a, Finite a) ⇒ Comparison a → String
      _showf (Comparison cmp) = unlines (fmap show'' graph)
        where
          graph  ∷ [(a, a, Ordering)]
          graph  = fmap (\(a₁, a₂) → (a₁, a₂, a₁ `cmp` a₂)) domain
            where
              domain ∷ [(a, a)]
              domain = asList
          show'' ∷ (a, a, Ordering) → String
          show'' (a₁, a₂, o) = quoteWith (quoteWith (show a₁) (show a₂) ", ") (show o) " ↦ "

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
finer (Equivalence (⮀)) (Equivalence (⮂)) = all (\(a₁, a₂) → (a₁ ⮀ a₂) `implies` (a₁ ⮂ a₂)) asList

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
-- fromPredicate p = equating' (getPredicate p)
-- fromPredicate = equating' . getPredicate

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
equivalenceClass eq a = NE.insert a (fmap snd (catThese (partitionedBy eq a)))
  where
    -- TODO describe in terms of irreflexive kernel / anti-reflexive kernel?
    partitionedBy ∷ Equivalence a → a → [These a a] -- ∀ a . (Finite a) ⇒ Equivalence a → a → [These a a]
    partitionedBy (Equivalence (≡)) a₁ = fmap f (asList ∷ [a])
      where
        f ∷ a → These a a
        f a₂ | a₁ == a₂ = This  a₁    -- equal by `==`
        f a₂ | a₁ ≡ a₂  = These a₁ a₂ -- equal by `≡` but not `==`
        f a₂            = That     a₂ -- not equal

-- https://arxiv.org/pdf/math/0601081.pdf
singletons ∷ ∀ a . (Finite a) ⇒ Equivalence a → [a]
singletons (≡) = List.filter (\a → (==) (a :| []) (equivalenceClass (≡) a)) asList

-- https://arxiv.org/pdf/0904.1097.pdf
-- non-maximal elements of the blocks
openers ∷ ∀ a . (Finite a) ⇒ Equivalence a → [a]
openers (≡) = List.filter (\a → a ≠ maximum (equivalenceClass (≡) a)) asList

-- https://arxiv.org/pdf/0904.1097.pdf
-- non-minimal elements of the blocks
closers ∷ ∀ a . (Finite a) ⇒ Equivalence a → [a]
closers (≡) = List.filter (\a → a ≠ minimum (equivalenceClass (≡) a)) asList

-- https://arxiv.org/pdf/math/0601081.pdf
-- neither minimal nor maximal elements of the blocks
transients ∷ ∀ a . (Finite a) ⇒ Equivalence a → [a]
transients (≡) = List.filter (\a → a ≠ maximum (equivalenceClass (≡) a)
                                 ∧ a ≠ minimum (equivalenceClass (≡) a)) asList

-- TODO deleteme
instance (Show a, Finite a) ⇒ Show (Equivalence a) where
  show ∷ Equivalence a → String
  show = showl
    where
      -- show an Equivalence as a list of disjoint lists of elements
      showl ∷ Equivalence a → String -- ∷ ∀ a . (Show a, Finite a) ⇒ Equivalence a → String
      showl = show . fmap NE.toList . fromEquivalence
      -- show an Equivalence as a function
      _showf ∷ Equivalence a → String -- ∷ ∀ a . (Show a, Finite a) ⇒ Equivalence a → String
      _showf (Equivalence (≡)) = unlines (fmap show'' graph)
        where
          graph  ∷ [(a, a, Bool)]
          graph  = fmap (\(a₁, a₂) → (a₁, a₂, a₁ ≡ a₂)) domain
            where
              domain ∷ [(a, a)]
              domain = asList
          show''  ∷ (a, a, Bool) → String
          show'' (a₁, a₂, b) = quoteWith (quoteWith (show a₁) (show a₂) ", ") (show b) " ↦ "
      -- show an Equivalence relation as a Ferrer's diagram -- TODO can improve this later, but this works
      _showferrers ∷ Equivalence a → String -- ∷ ∀ a . (Show a, Finite a) ⇒ Equivalence a → String
      _showferrers = unlines . fmap (fmap (const '*') . NE.toList) . ferrers

ferrers ∷ (Finite a) ⇒ Equivalence a → [NonEmpty ()]
ferrers = sortOn (Down . length') . fmap void . fromEquivalence

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
       ⇒ U.Finite (Equivalence a) where
  cardinality ∷ Tagged (Equivalence a) ℕ
  cardinality = fmap bell (retag (U.cardinality ∷ Tagged a ℕ))
instance (Finite a)
       ⇒ Finite (Equivalence a) where
  asList ∷ [Equivalence a]
  asList = fmap toEquivalence (partitions' asList)

data Alpha where
  A ∷ Alpha
  B ∷ Alpha
  C ∷ Alpha
  D ∷ Alpha
  E ∷ Alpha
  F ∷ Alpha
  G ∷ Alpha
  H ∷ Alpha
  I ∷ Alpha
  J ∷ Alpha
  K ∷ Alpha
  L ∷ Alpha
  M ∷ Alpha
  N ∷ Alpha
  O ∷ Alpha
  P ∷ Alpha
  Q ∷ Alpha
  R ∷ Alpha
  S ∷ Alpha
  T ∷ Alpha
  U ∷ Alpha
  V ∷ Alpha
  W ∷ Alpha
  X ∷ Alpha
  Y ∷ Alpha
  Z ∷ Alpha
  deriving (Eq, Ord, Enum, Bounded, Show, Read)
instance U.Universe Alpha
instance U.Finite   Alpha where
  cardinality ∷ Tagged Alpha ℕ
  cardinality = Tagged 26
instance Finite     Alpha
instance Fancy      Alpha where
  unicode ∷ Alpha → Char
  unicode A = 'A'
  unicode B = 'B'
  unicode C = 'C'
  unicode D = 'D'
  unicode E = 'E'
  unicode F = 'F'
  unicode G = 'G'
  unicode H = 'H'
  unicode I = 'I'
  unicode J = 'J'
  unicode K = 'K'
  unicode L = 'L'
  unicode M = 'M'
  unicode N = 'N'
  unicode O = 'O'
  unicode P = 'P'
  unicode Q = 'Q'
  unicode R = 'R'
  unicode S = 'S'
  unicode T = 'T'
  unicode U = 'U'
  unicode V = 'V'
  unicode W = 'W'
  unicode X = 'X'
  unicode Y = 'Y'
  unicode Z = 'Z'
  unicode' ∷ Alpha → Char
  unicode' = toLower . unicode
  plain ∷ Alpha → String
  plain = charToString . unicode
  named ∷ Alpha → String
  named = const "Alpha"

data DNA = Adenine | Cytosine | Guanine | Thymine deriving (Eq, Ord, Bounded, Enum)
instance Show DNA where
  show ∷ DNA → String
  show Adenine  = "A"
  show Cytosine = "C"
  show Guanine  = "G"
  show Thymine  = "T"
instance U.Universe DNA
instance U.Finite   DNA where
  cardinality ∷ Tagged DNA ℕ
  cardinality = Tagged 4
instance Finite     DNA


newtype Init = Init () deriving (Eq, Ord, Bounded, Enum)
instance U.Universe Init
instance U.Finite   Init where
  cardinality ∷ Tagged Init ℕ
  cardinality = Tagged 1
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
instance U.Finite   Final where
  cardinality ∷ Tagged Final ℕ
  cardinality = Tagged 1
instance Finite     Final where
  asList ∷ [Final]
  asList = [Final ()]
  asSet ∷ Set Final
  asSet  = Set.singleton (Final ())
instance Show Final where
  show ∷ Final → String
  show (Final ()) = "qᶠ"

data (:🎲) where
  (:⚀) ∷ (:🎲)
  (:⚁) ∷ (:🎲)
  (:⚂) ∷ (:🎲)
  (:⚃) ∷ (:🎲)
  (:⚄) ∷ (:🎲)
  (:⚅) ∷ (:🎲)
  deriving (Eq, Enum, Ord, Bounded)

-- aliases
(⚀) ∷ (:🎲)
(⚀) = (:⚀)

(⚁) ∷ (:🎲)
(⚁) = (:⚁)

(⚂) ∷ (:🎲)
(⚂) = (:⚂)

(⚃) ∷ (:🎲)
(⚃) = (:⚃)

(⚄) ∷ (:🎲)
(⚄) = (:⚄)

(⚅) ∷ (:🎲)
(⚅) = (:⚅)

-- non unicode aliases for convenience
type D6 = (:🎲)
side1 ∷ (:🎲)
side1 = (⚀)
side2 ∷ (:🎲)
side2 = (⚁)
side3 ∷ (:🎲)
side3 = (⚂)
side4 ∷ (:🎲)
side4 = (⚃)
side5 ∷ (:🎲)
side5 = (⚄)
side6 ∷ (:🎲)
side6 = (⚅)

instance Show (:🎲) where
  show ∷ (:🎲) → String
  show = show'

instance U.Universe (:🎲)
instance U.Finite   (:🎲) where
  cardinality ∷ Tagged (:🎲) ℕ
  cardinality = Tagged 6
instance Finite     (:🎲)

instance Fancy (:🎲) where
  unicode  ∷ (:🎲) → Char
  -- unicode = getOp (contramap (toEnum . fromEnum) (Op (fin₆ '⚀' '⚁' '⚂' '⚃' '⚄' '⚅')))
  unicode (:⚀) = '⚀'
  unicode (:⚁) = '⚁'
  unicode (:⚂) = '⚂'
  unicode (:⚃) = '⚃'
  unicode (:⚄) = '⚄'
  unicode (:⚅) = '⚅'
  plain ∷ (:🎲) → String
  -- plain = getOp (contramap (toEnum . fromEnum) (Op (fin₆ "(:⚀)" "(:⚁)" "(:⚂)" "(:⚃)" "(:⚄)" "(:⚅)")))
  plain (:⚀) = "(:⚀)"
  plain (:⚁) = "(:⚁)"
  plain (:⚂) = "(:⚂)"
  plain (:⚃) = "(:⚃)"
  plain (:⚄) = "(:⚄)"
  plain (:⚅) = "(:⚅)"
  show' ∷ (:🎲) → String
  show' d = charToString (unicode d) `toColor` toColor' d
  named ∷ (:🎲) → String
  named = const (charToString '🎲')

-- automorphism which computes the flip of the six-sided die to the opposite side
flipped ∷ (:🎲) → (:🎲)
flipped (:⚀) = (⚅)
flipped (:⚁) = (⚄)
flipped (:⚂) = (⚃)
flipped (:⚃) = (⚂)
flipped (:⚄) = (⚁)
flipped (:⚅) = (⚀)

-- non-deterministically knock over a die (rotate by 90 degrees)
rotate90 ∷ (:🎲) → NonEmpty (:🎲)
rotate90 (:⚀) = (⚁) :| [(⚂), (⚃), (⚄)]
rotate90 (:⚁) = (⚀) :| [(⚂), (⚃), (⚅)]
rotate90 (:⚂) = (⚀) :| [(⚁), (⚄), (⚅)]
rotate90 (:⚃) = (⚀) :| [(⚁), (⚄), (⚅)]
rotate90 (:⚄) = (⚀) :| [(⚂), (⚃), (⚅)]
rotate90 (:⚅) = (⚁) :| [(⚂), (⚃), (⚄)]

{-
-- https://www.unicode.org/charts/PDF/U1F030.pdf
🁢
🁣 🁤 🁥 🁦 🁧 🁨 🁩
🁪 🁫 🁬 🁭 🁮 🁯 🁰
🁱 🁲 🁳 🁴 🁵 🁶 🁷
🁸 🁹 🁺 🁻 🁼 🁽 🁾
🁿 🂀 🂁 🂂 🂃 🂄 🂅
🂆 🂇 🂈 🂉 🂊 🂋 🂌
🂍 🂎 🂏 🂐 🂑 🂒 🂓

🀰
🀱 🀲 🀳 🀴 🀵 🀶 🀷
🀸 🀹 🀺 🀻 🀼 🀽 🀾
🀿 🁀 🁁 🁂 🁃 🁄 🁅
🁆 🁇 🁈 🁉 🁊 🁋 🁌
🁍 🁎 🁏 🁐 🁑 🁒 🁓
🁔 🁕 🁖 🁗 🁘 🁙 🁚
🁛 🁜 🁝 🁞 🁟 🁠 🁡
-}
data (🀰) where
  (:🀱) ∷ (🀰)
  (:🀲) ∷ (🀰)
  (:🀳) ∷ (🀰)
  (:🀴) ∷ (🀰)
  (:🀵) ∷ (🀰)
  (:🀶) ∷ (🀰)
  (:🀷) ∷ (🀰)
  (:🀸) ∷ (🀰)
  (:🀹) ∷ (🀰)
  (:🀺) ∷ (🀰)
  (:🀻) ∷ (🀰)
  (:🀼) ∷ (🀰)
  (:🀽) ∷ (🀰)
  (:🀾) ∷ (🀰)
  (:🀿) ∷ (🀰)
  (:🁀) ∷ (🀰)
  (:🁁) ∷ (🀰)
  (:🁂) ∷ (🀰)
  (:🁃) ∷ (🀰)
  (:🁄) ∷ (🀰)
  (:🁅) ∷ (🀰)
  (:🁆) ∷ (🀰)
  (:🁇) ∷ (🀰)
  (:🁈) ∷ (🀰)
  (:🁉) ∷ (🀰)
  (:🁊) ∷ (🀰)
  (:🁋) ∷ (🀰)
  (:🁌) ∷ (🀰)
  (:🁍) ∷ (🀰)
  (:🁎) ∷ (🀰)
  (:🁏) ∷ (🀰)
  (:🁐) ∷ (🀰)
  (:🁑) ∷ (🀰)
  (:🁒) ∷ (🀰)
  (:🁓) ∷ (🀰)
  (:🁔) ∷ (🀰)
  (:🁕) ∷ (🀰)
  (:🁖) ∷ (🀰)
  (:🁗) ∷ (🀰)
  (:🁘) ∷ (🀰)
  (:🁙) ∷ (🀰)
  (:🁚) ∷ (🀰)
  (:🁛) ∷ (🀰)
  (:🁜) ∷ (🀰)
  (:🁝) ∷ (🀰)
  (:🁞) ∷ (🀰)
  (:🁟) ∷ (🀰)
  (:🁠) ∷ (🀰)
  (:🁡) ∷ (🀰)
  deriving (Eq, Ord, Bounded, Enum)

instance U.Universe (🀰)
instance U.Finite   (🀰) where
  cardinality ∷ Tagged (🀰) ℕ
  cardinality = Tagged 49
instance Finite     (🀰)

instance Show (🀰) where
  show ∷ (🀰) → String
  show = show'
instance Fancy (🀰) where
  unicode ∷ (🀰) → Char
  unicode (:🀱) = '🀱'
  unicode (:🀲) = '🀲'
  unicode (:🀳) = '🀳'
  unicode (:🀴) = '🀴'
  unicode (:🀵) = '🀵'
  unicode (:🀶) = '🀶'
  unicode (:🀷) = '🀷'
  unicode (:🀸) = '🀸'
  unicode (:🀹) = '🀹'
  unicode (:🀺) = '🀺'
  unicode (:🀻) = '🀻'
  unicode (:🀼) = '🀼'
  unicode (:🀽) = '🀽'
  unicode (:🀾) = '🀾'
  unicode (:🀿) = '🀿'
  unicode (:🁀) = '🁀'
  unicode (:🁁) = '🁁'
  unicode (:🁂) = '🁂'
  unicode (:🁃) = '🁃'
  unicode (:🁄) = '🁄'
  unicode (:🁅) = '🁅'
  unicode (:🁆) = '🁆'
  unicode (:🁇) = '🁇'
  unicode (:🁈) = '🁈'
  unicode (:🁉) = '🁉'
  unicode (:🁊) = '🁊'
  unicode (:🁋) = '🁋'
  unicode (:🁌) = '🁌'
  unicode (:🁍) = '🁍'
  unicode (:🁎) = '🁎'
  unicode (:🁏) = '🁏'
  unicode (:🁐) = '🁐'
  unicode (:🁑) = '🁑'
  unicode (:🁒) = '🁒'
  unicode (:🁓) = '🁓'
  unicode (:🁔) = '🁔'
  unicode (:🁕) = '🁕'
  unicode (:🁖) = '🁖'
  unicode (:🁗) = '🁗'
  unicode (:🁘) = '🁘'
  unicode (:🁙) = '🁙'
  unicode (:🁚) = '🁚'
  unicode (:🁛) = '🁛'
  unicode (:🁜) = '🁜'
  unicode (:🁝) = '🁝'
  unicode (:🁞) = '🁞'
  unicode (:🁟) = '🁟'
  unicode (:🁠) = '🁠'
  unicode (:🁡) = '🁡'
  plain ∷ (🀰) → String
  plain (:🀱) = "(:🀱)"
  plain (:🀲) = "(:🀲)"
  plain (:🀳) = "(:🀳)"
  plain (:🀴) = "(:🀴)"
  plain (:🀵) = "(:🀵)"
  plain (:🀶) = "(:🀶)"
  plain (:🀷) = "(:🀷)"
  plain (:🀸) = "(:🀸)"
  plain (:🀹) = "(:🀹)"
  plain (:🀺) = "(:🀺)"
  plain (:🀻) = "(:🀻)"
  plain (:🀼) = "(:🀼)"
  plain (:🀽) = "(:🀽)"
  plain (:🀾) = "(:🀾)"
  plain (:🀿) = "(:🀿)"
  plain (:🁀) = "(:🁀)"
  plain (:🁁) = "(:🁁)"
  plain (:🁂) = "(:🁂)"
  plain (:🁃) = "(:🁃)"
  plain (:🁄) = "(:🁄)"
  plain (:🁅) = "(:🁅)"
  plain (:🁆) = "(:🁆)"
  plain (:🁇) = "(:🁇)"
  plain (:🁈) = "(:🁈)"
  plain (:🁉) = "(:🁉)"
  plain (:🁊) = "(:🁊)"
  plain (:🁋) = "(:🁋)"
  plain (:🁌) = "(:🁌)"
  plain (:🁍) = "(:🁍)"
  plain (:🁎) = "(:🁎)"
  plain (:🁏) = "(:🁏)"
  plain (:🁐) = "(:🁐)"
  plain (:🁑) = "(:🁑)"
  plain (:🁒) = "(:🁒)"
  plain (:🁓) = "(:🁓)"
  plain (:🁔) = "(:🁔)"
  plain (:🁕) = "(:🁕)"
  plain (:🁖) = "(:🁖)"
  plain (:🁗) = "(:🁗)"
  plain (:🁘) = "(:🁘)"
  plain (:🁙) = "(:🁙)"
  plain (:🁚) = "(:🁚)"
  plain (:🁛) = "(:🁛)"
  plain (:🁜) = "(:🁜)"
  plain (:🁝) = "(:🁝)"
  plain (:🁞) = "(:🁞)"
  plain (:🁟) = "(:🁟)"
  plain (:🁠) = "(:🁠)"
  plain (:🁡) = "(:🁡)"
  show' ∷ (🀰) → String
  show' d = charToString (unicode d) `toColor` toColor' d
  named ∷ (🀰) → String
  named = const (charToString '🀰')

-- unicode aliases for convenience
(🀱) ∷ (🀰)
(🀱) = (:🀱)
(🀲) ∷ (🀰)
(🀲) = (:🀲)
(🀳) ∷ (🀰)
(🀳) = (:🀳)
(🀴) ∷ (🀰)
(🀴) = (:🀴)
(🀵) ∷ (🀰)
(🀵) = (:🀵)
(🀶) ∷ (🀰)
(🀶) = (:🀶)
(🀷) ∷ (🀰)
(🀷) = (:🀷)

(🀸) ∷ (🀰)
(🀸) = (:🀸)
(🀹) ∷ (🀰)
(🀹) = (:🀹)
(🀺) ∷ (🀰)
(🀺) = (:🀺)
(🀻) ∷ (🀰)
(🀻) = (:🀻)
(🀼) ∷ (🀰)
(🀼) = (:🀼)
(🀽) ∷ (🀰)
(🀽) = (:🀽)
(🀾) ∷ (🀰)
(🀾) = (:🀾)

(🀿) ∷ (🀰)
(🀿) = (:🀿)
(🁀) ∷ (🀰)
(🁀) = (:🁀)
(🁁) ∷ (🀰)
(🁁) = (:🁁)
(🁂) ∷ (🀰)
(🁂) = (:🁂)
(🁃) ∷ (🀰)
(🁃) = (:🁃)
(🁄) ∷ (🀰)
(🁄) = (:🁄)
(🁅) ∷ (🀰)
(🁅) = (:🁅)

(🁆) ∷ (🀰)
(🁆) = (:🁆)
(🁇) ∷ (🀰)
(🁇) = (:🁇)
(🁈) ∷ (🀰)
(🁈) = (:🁈)
(🁉) ∷ (🀰)
(🁉) = (:🁉)
(🁊) ∷ (🀰)
(🁊) = (:🁊)
(🁋) ∷ (🀰)
(🁋) = (:🁋)
(🁌) ∷ (🀰)
(🁌) = (:🁌)

(🁍) ∷ (🀰)
(🁍) = (:🁍)
(🁎) ∷ (🀰)
(🁎) = (:🁎)
(🁏) ∷ (🀰)
(🁏) = (:🁏)
(🁐) ∷ (🀰)
(🁐) = (:🁐)
(🁑) ∷ (🀰)
(🁑) = (:🁑)
(🁒) ∷ (🀰)
(🁒) = (:🁒)
(🁓) ∷ (🀰)
(🁓) = (:🁓)

(🁔) ∷ (🀰)
(🁔) = (:🁔)
(🁕) ∷ (🀰)
(🁕) = (:🁕)
(🁖) ∷ (🀰)
(🁖) = (:🁖)
(🁗) ∷ (🀰)
(🁗) = (:🁗)
(🁘) ∷ (🀰)
(🁘) = (:🁘)
(🁙) ∷ (🀰)
(🁙) = (:🁙)
(🁚) ∷ (🀰)
(🁚) = (:🁚)

(🁛) ∷ (🀰)
(🁛) = (:🁛)
(🁜) ∷ (🀰)
(🁜) = (:🁜)
(🁝) ∷ (🀰)
(🁝) = (:🁝)
(🁞) ∷ (🀰)
(🁞) = (:🁞)
(🁟) ∷ (🀰)
(🁟) = (:🁟)
(🁠) ∷ (🀰)
(🁠) = (:🁠)
(🁡) ∷ (🀰)
(🁡) = (:🁡)

flipH ∷ (🀰) → (🀰)
flipH (:🀱) = (🀱)
flipH (:🀲) = (🀸)
flipH (:🀳) = (🀿)
flipH (:🀴) = (🁆)
flipH (:🀵) = (🁍)
flipH (:🀶) = (🁔)
flipH (:🀷) = (🁛)
flipH (:🀸) = (🀲)
flipH (:🀹) = (🀹)
flipH (:🀺) = (🁀)
flipH (:🀻) = (🁇)
flipH (:🀼) = (🁎)
flipH (:🀽) = (🁕)
flipH (:🀾) = (🁜)
flipH (:🀿) = (🀳)
flipH (:🁀) = (🀺)
flipH (:🁁) = (🁁)
flipH (:🁂) = (🁈)
flipH (:🁃) = (🁏)
flipH (:🁄) = (🁖)
flipH (:🁅) = (🁝)
flipH (:🁆) = (🀴)
flipH (:🁇) = (🀻)
flipH (:🁈) = (🁂)
flipH (:🁉) = (🁉)
flipH (:🁊) = (🁐)
flipH (:🁋) = (🁗)
flipH (:🁌) = (🁞)
flipH (:🁍) = (🀵)
flipH (:🁎) = (🀼)
flipH (:🁏) = (🁃)
flipH (:🁐) = (🁊)
flipH (:🁑) = (🁑)
flipH (:🁒) = (🁘)
flipH (:🁓) = (🁟)
flipH (:🁔) = (🀶)
flipH (:🁕) = (🀽)
flipH (:🁖) = (🁄)
flipH (:🁗) = (🁋)
flipH (:🁘) = (🁒)
flipH (:🁙) = (🁙)
flipH (:🁚) = (🁠)
flipH (:🁛) = (🀷)
flipH (:🁜) = (🀾)
flipH (:🁝) = (🁅)
flipH (:🁞) = (🁌)
flipH (:🁟) = (🁓)
flipH (:🁠) = (🁚)
flipH (:🁡) = (🁡)

leftOf ∷ (🀰) → Maybe (:🎲)
leftOf (:🀱) = Nothing
leftOf (:🀲) = Nothing
leftOf (:🀳) = Nothing
leftOf (:🀴) = Nothing
leftOf (:🀵) = Nothing
leftOf (:🀶) = Nothing
leftOf (:🀷) = Nothing
leftOf (:🀸) = Just (⚀)
leftOf (:🀹) = Just (⚀)
leftOf (:🀺) = Just (⚀)
leftOf (:🀻) = Just (⚀)
leftOf (:🀼) = Just (⚀)
leftOf (:🀽) = Just (⚀)
leftOf (:🀾) = Just (⚀)
leftOf (:🀿) = Just (⚁)
leftOf (:🁀) = Just (⚁)
leftOf (:🁁) = Just (⚁)
leftOf (:🁂) = Just (⚁)
leftOf (:🁃) = Just (⚁)
leftOf (:🁄) = Just (⚁)
leftOf (:🁅) = Just (⚁)
leftOf (:🁆) = Just (⚂)
leftOf (:🁇) = Just (⚂)
leftOf (:🁈) = Just (⚂)
leftOf (:🁉) = Just (⚂)
leftOf (:🁊) = Just (⚂)
leftOf (:🁋) = Just (⚂)
leftOf (:🁌) = Just (⚂)
leftOf (:🁍) = Just (⚃)
leftOf (:🁎) = Just (⚃)
leftOf (:🁏) = Just (⚃)
leftOf (:🁐) = Just (⚃)
leftOf (:🁑) = Just (⚃)
leftOf (:🁒) = Just (⚃)
leftOf (:🁓) = Just (⚃)
leftOf (:🁔) = Just (⚄)
leftOf (:🁕) = Just (⚄)
leftOf (:🁖) = Just (⚄)
leftOf (:🁗) = Just (⚄)
leftOf (:🁘) = Just (⚄)
leftOf (:🁙) = Just (⚄)
leftOf (:🁚) = Just (⚄)
leftOf (:🁛) = Just (⚅)
leftOf (:🁜) = Just (⚅)
leftOf (:🁝) = Just (⚅)
leftOf (:🁞) = Just (⚅)
leftOf (:🁟) = Just (⚅)
leftOf (:🁠) = Just (⚅)
leftOf (:🁡) = Just (⚅)

rightOf ∷ (🀰) → Maybe (:🎲)
rightOf (:🀱) = Nothing
rightOf (:🀲) = Just (⚀)
rightOf (:🀳) = Just (⚁)
rightOf (:🀴) = Just (⚂)
rightOf (:🀵) = Just (⚃)
rightOf (:🀶) = Just (⚄)
rightOf (:🀷) = Just (⚅)
rightOf (:🀸) = Nothing
rightOf (:🀹) = Just (⚀)
rightOf (:🀺) = Just (⚁)
rightOf (:🀻) = Just (⚂)
rightOf (:🀼) = Just (⚃)
rightOf (:🀽) = Just (⚄)
rightOf (:🀾) = Just (⚅)
rightOf (:🀿) = Nothing
rightOf (:🁀) = Just (⚀)
rightOf (:🁁) = Just (⚁)
rightOf (:🁂) = Just (⚂)
rightOf (:🁃) = Just (⚃)
rightOf (:🁄) = Just (⚄)
rightOf (:🁅) = Just (⚅)
rightOf (:🁆) = Nothing
rightOf (:🁇) = Just (⚀)
rightOf (:🁈) = Just (⚁)
rightOf (:🁉) = Just (⚂)
rightOf (:🁊) = Just (⚃)
rightOf (:🁋) = Just (⚄)
rightOf (:🁌) = Just (⚅)
rightOf (:🁍) = Nothing
rightOf (:🁎) = Just (⚀)
rightOf (:🁏) = Just (⚁)
rightOf (:🁐) = Just (⚂)
rightOf (:🁑) = Just (⚃)
rightOf (:🁒) = Just (⚄)
rightOf (:🁓) = Just (⚅)
rightOf (:🁔) = Nothing
rightOf (:🁕) = Just (⚀)
rightOf (:🁖) = Just (⚁)
rightOf (:🁗) = Just (⚂)
rightOf (:🁘) = Just (⚃)
rightOf (:🁙) = Just (⚄)
rightOf (:🁚) = Just (⚅)
rightOf (:🁛) = Nothing
rightOf (:🁜) = Just (⚀)
rightOf (:🁝) = Just (⚁)
rightOf (:🁞) = Just (⚂)
rightOf (:🁟) = Just (⚃)
rightOf (:🁠) = Just (⚄)
rightOf (:🁡) = Just (⚅)

byRightOf ∷ Equivalence (🀰)
byRightOf = equating' rightOf

byLeftOf ∷ Equivalence (🀰)
byLeftOf = equating' leftOf

byEqualLR ∷ Equivalence (🀰)
byEqualLR = equating' (liftA2 (==) leftOf rightOf)

type Domino' = (🀰)

data (🁢) where
  (:🁣) ∷ (🁢)
  (:🁤) ∷ (🁢)
  (:🁥) ∷ (🁢)
  (:🁦) ∷ (🁢)
  (:🁧) ∷ (🁢)
  (:🁨) ∷ (🁢)
  (:🁩) ∷ (🁢)
  (:🁪) ∷ (🁢)
  (:🁫) ∷ (🁢)
  (:🁬) ∷ (🁢)
  (:🁭) ∷ (🁢)
  (:🁮) ∷ (🁢)
  (:🁯) ∷ (🁢)
  (:🁰) ∷ (🁢)
  (:🁱) ∷ (🁢)
  (:🁲) ∷ (🁢)
  (:🁳) ∷ (🁢)
  (:🁴) ∷ (🁢)
  (:🁵) ∷ (🁢)
  (:🁶) ∷ (🁢)
  (:🁷) ∷ (🁢)
  (:🁸) ∷ (🁢)
  (:🁹) ∷ (🁢)
  (:🁺) ∷ (🁢)
  (:🁻) ∷ (🁢)
  (:🁼) ∷ (🁢)
  (:🁽) ∷ (🁢)
  (:🁾) ∷ (🁢)
  (:🁿) ∷ (🁢)
  (:🂀) ∷ (🁢)
  (:🂁) ∷ (🁢)
  (:🂂) ∷ (🁢)
  (:🂃) ∷ (🁢)
  (:🂄) ∷ (🁢)
  (:🂅) ∷ (🁢)
  (:🂆) ∷ (🁢)
  (:🂇) ∷ (🁢)
  (:🂈) ∷ (🁢)
  (:🂉) ∷ (🁢)
  (:🂊) ∷ (🁢)
  (:🂋) ∷ (🁢)
  (:🂌) ∷ (🁢)
  (:🂍) ∷ (🁢)
  (:🂎) ∷ (🁢)
  (:🂏) ∷ (🁢)
  (:🂐) ∷ (🁢)
  (:🂑) ∷ (🁢)
  (:🂒) ∷ (🁢)
  (:🂓) ∷ (🁢)
  deriving (Eq, Ord, Bounded, Enum)

instance U.Universe (🁢)
instance U.Finite   (🁢) where
  cardinality ∷ Tagged (🁢) ℕ
  cardinality = Tagged 49
instance Finite     (🁢)

instance Show (🁢) where
  show ∷ (🁢) → String
  show = show₂
    where
      show₀ ∷ (🁢) → String
      show₀ = show'
      show₁ ∷ (🁢) → String
      show₁ d = show (valTop d, valBottom d)
      show₂ ∷ (🁢) → String
      show₂ d = quoteWith "(" ")" (quoteWith (toColor (show (valTop    d)) Red    )
                                             (toColor (show (valBottom d)) Magenta) ",")
instance Fancy (🁢) where
  unicode ∷ (🁢) → Char
  unicode (:🁣) = '🁣'
  unicode (:🁤) = '🁤'
  unicode (:🁥) = '🁥'
  unicode (:🁦) = '🁦'
  unicode (:🁧) = '🁧'
  unicode (:🁨) = '🁨'
  unicode (:🁩) = '🁩'
  unicode (:🁪) = '🁪'
  unicode (:🁫) = '🁫'
  unicode (:🁬) = '🁬'
  unicode (:🁭) = '🁭'
  unicode (:🁮) = '🁮'
  unicode (:🁯) = '🁯'
  unicode (:🁰) = '🁰'
  unicode (:🁱) = '🁱'
  unicode (:🁲) = '🁲'
  unicode (:🁳) = '🁳'
  unicode (:🁴) = '🁴'
  unicode (:🁵) = '🁵'
  unicode (:🁶) = '🁶'
  unicode (:🁷) = '🁷'
  unicode (:🁸) = '🁸'
  unicode (:🁹) = '🁹'
  unicode (:🁺) = '🁺'
  unicode (:🁻) = '🁻'
  unicode (:🁼) = '🁼'
  unicode (:🁽) = '🁽'
  unicode (:🁾) = '🁾'
  unicode (:🁿) = '🁿'
  unicode (:🂀) = '🂀'
  unicode (:🂁) = '🂁'
  unicode (:🂂) = '🂂'
  unicode (:🂃) = '🂃'
  unicode (:🂄) = '🂄'
  unicode (:🂅) = '🂅'
  unicode (:🂆) = '🂆'
  unicode (:🂇) = '🂇'
  unicode (:🂈) = '🂈'
  unicode (:🂉) = '🂉'
  unicode (:🂊) = '🂊'
  unicode (:🂋) = '🂋'
  unicode (:🂌) = '🂌'
  unicode (:🂍) = '🂍'
  unicode (:🂎) = '🂎'
  unicode (:🂏) = '🂏'
  unicode (:🂐) = '🂐'
  unicode (:🂑) = '🂑'
  unicode (:🂒) = '🂒'
  unicode (:🂓) = '🂓'
  plain ∷ (🁢) → String
  plain (:🁣) = "(:🁣)"
  plain (:🁤) = "(:🁤)"
  plain (:🁥) = "(:🁥)"
  plain (:🁦) = "(:🁦)"
  plain (:🁧) = "(:🁧)"
  plain (:🁨) = "(:🁨)"
  plain (:🁩) = "(:🁩)"
  plain (:🁪) = "(:🁪)"
  plain (:🁫) = "(:🁫)"
  plain (:🁬) = "(:🁬)"
  plain (:🁭) = "(:🁭)"
  plain (:🁮) = "(:🁮)"
  plain (:🁯) = "(:🁯)"
  plain (:🁰) = "(:🁰)"
  plain (:🁱) = "(:🁱)"
  plain (:🁲) = "(:🁲)"
  plain (:🁳) = "(:🁳)"
  plain (:🁴) = "(:🁴)"
  plain (:🁵) = "(:🁵)"
  plain (:🁶) = "(:🁶)"
  plain (:🁷) = "(:🁷)"
  plain (:🁸) = "(:🁸)"
  plain (:🁹) = "(:🁹)"
  plain (:🁺) = "(:🁺)"
  plain (:🁻) = "(:🁻)"
  plain (:🁼) = "(:🁼)"
  plain (:🁽) = "(:🁽)"
  plain (:🁾) = "(:🁾)"
  plain (:🁿) = "(:🁿)"
  plain (:🂀) = "(:🂀)"
  plain (:🂁) = "(:🂁)"
  plain (:🂂) = "(:🂂)"
  plain (:🂃) = "(:🂃)"
  plain (:🂄) = "(:🂄)"
  plain (:🂅) = "(:🂅)"
  plain (:🂆) = "(:🂆)"
  plain (:🂇) = "(:🂇)"
  plain (:🂈) = "(:🂈)"
  plain (:🂉) = "(:🂉)"
  plain (:🂊) = "(:🂊)"
  plain (:🂋) = "(:🂋)"
  plain (:🂌) = "(:🂌)"
  plain (:🂍) = "(:🂍)"
  plain (:🂎) = "(:🂎)"
  plain (:🂏) = "(:🂏)"
  plain (:🂐) = "(:🂐)"
  plain (:🂑) = "(:🂑)"
  plain (:🂒) = "(:🂒)"
  plain (:🂓) = "(:🂓)"
  show' ∷ (🁢) → String
  show' d = charToString (unicode d) `toColor` toColor' d
  named ∷ (🁢) → String
  named = const (charToString '🁢')

-- unicode aliases for convenience
(🁣) ∷ (🁢)
(🁣) = (:🁣)
(🁤) ∷ (🁢)
(🁤) = (:🁤)
(🁥) ∷ (🁢)
(🁥) = (:🁥)
(🁦) ∷ (🁢)
(🁦) = (:🁦)
(🁧) ∷ (🁢)
(🁧) = (:🁧)
(🁨) ∷ (🁢)
(🁨) = (:🁨)
(🁩) ∷ (🁢)
(🁩) = (:🁩)

(🁪) ∷ (🁢)
(🁪) = (:🁪)
(🁫) ∷ (🁢)
(🁫) = (:🁫)
(🁬) ∷ (🁢)
(🁬) = (:🁬)
(🁭) ∷ (🁢)
(🁭) = (:🁭)
(🁮) ∷ (🁢)
(🁮) = (:🁮)
(🁯) ∷ (🁢)
(🁯) = (:🁯)
(🁰) ∷ (🁢)
(🁰) = (:🁰)

(🁱) ∷ (🁢)
(🁱) = (:🁱)
(🁲) ∷ (🁢)
(🁲) = (:🁲)
(🁳) ∷ (🁢)
(🁳) = (:🁳)
(🁴) ∷ (🁢)
(🁴) = (:🁴)
(🁵) ∷ (🁢)
(🁵) = (:🁵)
(🁶) ∷ (🁢)
(🁶) = (:🁶)
(🁷) ∷ (🁢)
(🁷) = (:🁷)

(🁸) ∷ (🁢)
(🁸) = (:🁸)
(🁹) ∷ (🁢)
(🁹) = (:🁹)
(🁺) ∷ (🁢)
(🁺) = (:🁺)
(🁻) ∷ (🁢)
(🁻) = (:🁻)
(🁼) ∷ (🁢)
(🁼) = (:🁼)
(🁽) ∷ (🁢)
(🁽) = (:🁽)
(🁾) ∷ (🁢)
(🁾) = (:🁾)

(🁿) ∷ (🁢)
(🁿) = (:🁿)
(🂀) ∷ (🁢)
(🂀) = (:🂀)
(🂁) ∷ (🁢)
(🂁) = (:🂁)
(🂂) ∷ (🁢)
(🂂) = (:🂂)
(🂃) ∷ (🁢)
(🂃) = (:🂃)
(🂄) ∷ (🁢)
(🂄) = (:🂄)
(🂅) ∷ (🁢)
(🂅) = (:🂅)

(🂆) ∷ (🁢)
(🂆) = (:🂆)
(🂇) ∷ (🁢)
(🂇) = (:🂇)
(🂈) ∷ (🁢)
(🂈) = (:🂈)
(🂉) ∷ (🁢)
(🂉) = (:🂉)
(🂊) ∷ (🁢)
(🂊) = (:🂊)
(🂋) ∷ (🁢)
(🂋) = (:🂋)
(🂌) ∷ (🁢)
(🂌) = (:🂌)

(🂍) ∷ (🁢)
(🂍) = (:🂍)
(🂎) ∷ (🁢)
(🂎) = (:🂎)
(🂏) ∷ (🁢)
(🂏) = (:🂏)
(🂐) ∷ (🁢)
(🂐) = (:🂐)
(🂑) ∷ (🁢)
(🂑) = (:🂑)
(🂒) ∷ (🁢)
(🂒) = (:🂒)
(🂓) ∷ (🁢)
(🂓) = (:🂓)

flipV ∷ (🁢) → (🁢)
flipV (:🁣) = (🁣)
flipV (:🁤) = (🁪)
flipV (:🁥) = (🁱)
flipV (:🁦) = (🁸)
flipV (:🁧) = (🁿)
flipV (:🁨) = (🂆)
flipV (:🁩) = (🂍)
flipV (:🁪) = (🁤)
flipV (:🁫) = (🁫)
flipV (:🁬) = (🁲)
flipV (:🁭) = (🁹)
flipV (:🁮) = (🂀)
flipV (:🁯) = (🂇)
flipV (:🁰) = (🂎)
flipV (:🁱) = (🁥)
flipV (:🁲) = (🁬)
flipV (:🁳) = (🁳)
flipV (:🁴) = (🁺)
flipV (:🁵) = (🂁)
flipV (:🁶) = (🂈)
flipV (:🁷) = (🂏)
flipV (:🁸) = (🁦)
flipV (:🁹) = (🁭)
flipV (:🁺) = (🁴)
flipV (:🁻) = (🁻)
flipV (:🁼) = (🂂)
flipV (:🁽) = (🂉)
flipV (:🁾) = (🂐)
flipV (:🁿) = (🁧)
flipV (:🂀) = (🁮)
flipV (:🂁) = (🁵)
flipV (:🂂) = (🁼)
flipV (:🂃) = (🂃)
flipV (:🂄) = (🂊)
flipV (:🂅) = (🂑)
flipV (:🂆) = (🁨)
flipV (:🂇) = (🁯)
flipV (:🂈) = (🁶)
flipV (:🂉) = (🁽)
flipV (:🂊) = (🂄)
flipV (:🂋) = (🂋)
flipV (:🂌) = (🂒)
flipV (:🂍) = (🁩)
flipV (:🂎) = (🁰)
flipV (:🂏) = (🁷)
flipV (:🂐) = (🁾)
flipV (:🂑) = (🂅)
flipV (:🂒) = (🂌)
flipV (:🂓) = (🂓)

topOf ∷ (🁢) → Maybe (:🎲)
topOf (:🁣) = Nothing
topOf (:🁤) = Nothing
topOf (:🁥) = Nothing
topOf (:🁦) = Nothing
topOf (:🁧) = Nothing
topOf (:🁨) = Nothing
topOf (:🁩) = Nothing
topOf (:🁪) = Just (⚀)
topOf (:🁫) = Just (⚀)
topOf (:🁬) = Just (⚀)
topOf (:🁭) = Just (⚀)
topOf (:🁮) = Just (⚀)
topOf (:🁯) = Just (⚀)
topOf (:🁰) = Just (⚀)
topOf (:🁱) = Just (⚁)
topOf (:🁲) = Just (⚁)
topOf (:🁳) = Just (⚁)
topOf (:🁴) = Just (⚁)
topOf (:🁵) = Just (⚁)
topOf (:🁶) = Just (⚁)
topOf (:🁷) = Just (⚁)
topOf (:🁸) = Just (⚂)
topOf (:🁹) = Just (⚂)
topOf (:🁺) = Just (⚂)
topOf (:🁻) = Just (⚂)
topOf (:🁼) = Just (⚂)
topOf (:🁽) = Just (⚂)
topOf (:🁾) = Just (⚂)
topOf (:🁿) = Just (⚃)
topOf (:🂀) = Just (⚃)
topOf (:🂁) = Just (⚃)
topOf (:🂂) = Just (⚃)
topOf (:🂃) = Just (⚃)
topOf (:🂄) = Just (⚃)
topOf (:🂅) = Just (⚃)
topOf (:🂆) = Just (⚄)
topOf (:🂇) = Just (⚄)
topOf (:🂈) = Just (⚄)
topOf (:🂉) = Just (⚄)
topOf (:🂊) = Just (⚄)
topOf (:🂋) = Just (⚄)
topOf (:🂌) = Just (⚄)
topOf (:🂍) = Just (⚅)
topOf (:🂎) = Just (⚅)
topOf (:🂏) = Just (⚅)
topOf (:🂐) = Just (⚅)
topOf (:🂑) = Just (⚅)
topOf (:🂒) = Just (⚅)
topOf (:🂓) = Just (⚅)

bottomOf ∷ (🁢) → Maybe (:🎲)
bottomOf (:🁣) = Nothing
bottomOf (:🁤) = Just (⚀)
bottomOf (:🁥) = Just (⚁)
bottomOf (:🁦) = Just (⚂)
bottomOf (:🁧) = Just (⚃)
bottomOf (:🁨) = Just (⚄)
bottomOf (:🁩) = Just (⚅)
bottomOf (:🁪) = Nothing
bottomOf (:🁫) = Just (⚀)
bottomOf (:🁬) = Just (⚁)
bottomOf (:🁭) = Just (⚂)
bottomOf (:🁮) = Just (⚃)
bottomOf (:🁯) = Just (⚄)
bottomOf (:🁰) = Just (⚅)
bottomOf (:🁱) = Nothing
bottomOf (:🁲) = Just (⚀)
bottomOf (:🁳) = Just (⚁)
bottomOf (:🁴) = Just (⚂)
bottomOf (:🁵) = Just (⚃)
bottomOf (:🁶) = Just (⚄)
bottomOf (:🁷) = Just (⚅)
bottomOf (:🁸) = Nothing
bottomOf (:🁹) = Just (⚀)
bottomOf (:🁺) = Just (⚁)
bottomOf (:🁻) = Just (⚂)
bottomOf (:🁼) = Just (⚃)
bottomOf (:🁽) = Just (⚄)
bottomOf (:🁾) = Just (⚅)
bottomOf (:🁿) = Nothing
bottomOf (:🂀) = Just (⚀)
bottomOf (:🂁) = Just (⚁)
bottomOf (:🂂) = Just (⚂)
bottomOf (:🂃) = Just (⚃)
bottomOf (:🂄) = Just (⚄)
bottomOf (:🂅) = Just (⚅)
bottomOf (:🂆) = Nothing
bottomOf (:🂇) = Just (⚀)
bottomOf (:🂈) = Just (⚁)
bottomOf (:🂉) = Just (⚂)
bottomOf (:🂊) = Just (⚃)
bottomOf (:🂋) = Just (⚄)
bottomOf (:🂌) = Just (⚅)
bottomOf (:🂍) = Nothing
bottomOf (:🂎) = Just (⚀)
bottomOf (:🂏) = Just (⚁)
bottomOf (:🂐) = Just (⚂)
bottomOf (:🂑) = Just (⚃)
bottomOf (:🂒) = Just (⚄)
bottomOf (:🂓) = Just (⚅)

byBottomOf ∷ Equivalence (🁢)
byBottomOf = equating' bottomOf

byTopOf ∷ Equivalence (🁢)
byTopOf = equating' topOf

byEqualTB ∷ Equivalence (🁢)
byEqualTB = equating' (liftA2 (==) topOf bottomOf)

valBottom ∷ (🁢) → ℕ
valBottom = maybe 0 (succ . fromEnum') . bottomOf

valTop    ∷ (🁢) → ℕ
valTop    = maybe 0 (succ . fromEnum') . topOf

valRight  ∷ (🀰) → ℕ
valRight  = maybe 0 (succ . fromEnum') . rightOf

valLeft   ∷ (🀰) → ℕ
valLeft   = maybe 0 (succ . fromEnum') . leftOf

bySum ∷ Equivalence (🁢)
bySum = equating' (liftA2 (+) valTop valBottom)

byProduct ∷ Equivalence (🁢)
byProduct = equating' (liftA2 (*) valTop valBottom)

byExp ∷ Equivalence (🁢)
byExp = equating' (liftA2 (^) valBottom valTop)

byExp' ∷ Equivalence (🁢)
byExp' = equating' (liftA2 (^) valTop valBottom)

type Domino = (🁢)

fromHorizontal ∷ (🀰) → (🁢)
fromHorizontal (:🀱) = (🁣)
fromHorizontal (:🀲) = (🁤)
fromHorizontal (:🀳) = (🁥)
fromHorizontal (:🀴) = (🁦)
fromHorizontal (:🀵) = (🁧)
fromHorizontal (:🀶) = (🁨)
fromHorizontal (:🀷) = (🁩)
fromHorizontal (:🀸) = (🁪)
fromHorizontal (:🀹) = (🁫)
fromHorizontal (:🀺) = (🁬)
fromHorizontal (:🀻) = (🁭)
fromHorizontal (:🀼) = (🁮)
fromHorizontal (:🀽) = (🁯)
fromHorizontal (:🀾) = (🁰)
fromHorizontal (:🀿) = (🁱)
fromHorizontal (:🁀) = (🁲)
fromHorizontal (:🁁) = (🁳)
fromHorizontal (:🁂) = (🁴)
fromHorizontal (:🁃) = (🁵)
fromHorizontal (:🁄) = (🁶)
fromHorizontal (:🁅) = (🁷)
fromHorizontal (:🁆) = (🁸)
fromHorizontal (:🁇) = (🁹)
fromHorizontal (:🁈) = (🁺)
fromHorizontal (:🁉) = (🁻)
fromHorizontal (:🁊) = (🁼)
fromHorizontal (:🁋) = (🁽)
fromHorizontal (:🁌) = (🁾)
fromHorizontal (:🁍) = (🁿)
fromHorizontal (:🁎) = (🂀)
fromHorizontal (:🁏) = (🂁)
fromHorizontal (:🁐) = (🂂)
fromHorizontal (:🁑) = (🂃)
fromHorizontal (:🁒) = (🂄)
fromHorizontal (:🁓) = (🂅)
fromHorizontal (:🁔) = (🂆)
fromHorizontal (:🁕) = (🂇)
fromHorizontal (:🁖) = (🂈)
fromHorizontal (:🁗) = (🂉)
fromHorizontal (:🁘) = (🂊)
fromHorizontal (:🁙) = (🂋)
fromHorizontal (:🁚) = (🂌)
fromHorizontal (:🁛) = (🂍)
fromHorizontal (:🁜) = (🂎)
fromHorizontal (:🁝) = (🂏)
fromHorizontal (:🁞) = (🂐)
fromHorizontal (:🁟) = (🂑)
fromHorizontal (:🁠) = (🂒)
fromHorizontal (:🁡) = (🂓)

fromVertical ∷ (🁢) → (🀰)
fromVertical (:🁣) = (🀱)
fromVertical (:🁤) = (🀲)
fromVertical (:🁥) = (🀳)
fromVertical (:🁦) = (🀴)
fromVertical (:🁧) = (🀵)
fromVertical (:🁨) = (🀶)
fromVertical (:🁩) = (🀷)
fromVertical (:🁪) = (🀸)
fromVertical (:🁫) = (🀹)
fromVertical (:🁬) = (🀺)
fromVertical (:🁭) = (🀻)
fromVertical (:🁮) = (🀼)
fromVertical (:🁯) = (🀽)
fromVertical (:🁰) = (🀾)
fromVertical (:🁱) = (🀿)
fromVertical (:🁲) = (🁀)
fromVertical (:🁳) = (🁁)
fromVertical (:🁴) = (🁂)
fromVertical (:🁵) = (🁃)
fromVertical (:🁶) = (🁄)
fromVertical (:🁷) = (🁅)
fromVertical (:🁸) = (🁆)
fromVertical (:🁹) = (🁇)
fromVertical (:🁺) = (🁈)
fromVertical (:🁻) = (🁉)
fromVertical (:🁼) = (🁊)
fromVertical (:🁽) = (🁋)
fromVertical (:🁾) = (🁌)
fromVertical (:🁿) = (🁍)
fromVertical (:🂀) = (🁎)
fromVertical (:🂁) = (🁏)
fromVertical (:🂂) = (🁐)
fromVertical (:🂃) = (🁑)
fromVertical (:🂄) = (🁒)
fromVertical (:🂅) = (🁓)
fromVertical (:🂆) = (🁔)
fromVertical (:🂇) = (🁕)
fromVertical (:🂈) = (🁖)
fromVertical (:🂉) = (🁗)
fromVertical (:🂊) = (🁘)
fromVertical (:🂋) = (🁙)
fromVertical (:🂌) = (🁚)
fromVertical (:🂍) = (🁛)
fromVertical (:🂎) = (🁜)
fromVertical (:🂏) = (🁝)
fromVertical (:🂐) = (🁞)
fromVertical (:🂑) = (🁟)
fromVertical (:🂒) = (🁠)
fromVertical (:🂓) = (🁡)

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
instance U.Finite   Month where
  cardinality ∷ Tagged Month ℕ
  cardinality = Tagged 12
instance Finite     Month

-- https://en.wikipedia.org/wiki/Quadrant_(plane_geometry)
data Quadrant where
  Q₁ ∷ Quadrant
  Q₂ ∷ Quadrant
  Q₃ ∷ Quadrant
  Q₄ ∷ Quadrant
  deriving (Eq, Enum, Ord, Bounded)

instance U.Universe Quadrant
instance U.Finite   Quadrant where
  cardinality ∷ Tagged Quadrant ℕ
  cardinality = Tagged 4
instance Finite     Quadrant
instance Fancy      Quadrant where
  unicode  ∷ Quadrant → Char
  unicode  = quadrant 'Ⅰ' 'Ⅱ' 'Ⅲ' 'Ⅳ'
  unicode' ∷ Quadrant → Char
  unicode' = quadrant 'ⅰ' 'ⅱ' 'ⅲ' 'ⅳ'
  plain    ∷ Quadrant → String
  plain    = quadrant "Q₁" "Q₂" "Q₃" "Q₄"
  named    ∷ Quadrant → String
  named    = const "Quadrant"
instance Show Quadrant where
  show ∷ Quadrant → String
  show = show₂
    where
      show₁ ∷ Quadrant → String
      show₁ = show'
      show₂ ∷ Quadrant → String
      show₂ = quadrant "(+; +)" "(−; +)" "(−; −)" "(+; −)"
      show₃ ∷ Quadrant → String
      show₃ q = toColor (show₂ q) (toColor' q)
-- non unicode aliases for convenience
type Q1 = 'Q₁
type Q2 = 'Q₂
type Q3 = 'Q₃
type Q4 = 'Q₄
-- case analysis for `Quadrant` type
quadrant ∷ a → a → a → a → Quadrant → a
quadrant i _  _   _  Q₁ = i
quadrant _ ii _   _  Q₂ = ii
quadrant _ _  iii _  Q₃ = iii
quadrant _ _  _   iv Q₄ = iv

-- TODO consider type signature
-- TODO quadrants ∷ ∀ a b . (Num a, Ord a, Num b, Ord b) ⇒ Equivalence (a, b)
-- TODO may want to explore proofs for that scenario, however.
-- TODO e.g. 1/1 as a different number than 1, etc.
-- TODO also this doesn't need to be in src/Finite.hs
quadrants ∷ ∀ a . (Num a, Ord a) ⇒ Equivalence (a, a)
quadrants = Equivalence ((==) `on` getQuadrant)
  where
    -- https://mathworld.wolfram.com/Quadrant.html
    getQuadrant ∷ (a, a) → Maybe Quadrant
    getQuadrant (a₁, a₂) | a₁ > 0 ∧ a₂ > 0 = Just Q₁
                         | a₁ < 0 ∧ a₂ > 0 = Just Q₂
                         | a₁ < 0 ∧ a₂ < 0 = Just Q₃
                         | a₁ > 0 ∧ a₂ < 0 = Just Q₄
                         | otherwise       = Nothing

-- TODO better name?
graphComponents ∷ ∀ a . (Num a, Eq a) ⇒ Equivalence (a, a)
graphComponents = contramap getComponents eqCan
  where
    getComponents ∷ (a, a) → Can a a
    getComponents (0,  0 ) = C.Non       -- origin
    getComponents (a₁, 0 ) = C.One a₁    -- x-axis
    getComponents (0,  a₂) = C.Eno    a₂ -- y-axis
    getComponents (a₁, a₂) = C.Two a₁ a₂ -- quadrant

-- https://en.wikipedia.org/wiki/Octant_(solid_geometry)
data Octant where
  O₁ ∷ Octant
  O₂ ∷ Octant
  O₃ ∷ Octant
  O₄ ∷ Octant
  O₅ ∷ Octant
  O₆ ∷ Octant
  O₇ ∷ Octant
  O₈ ∷ Octant
  deriving (Eq, Enum, Ord, Bounded)

instance U.Universe Octant
instance U.Finite   Octant where
  cardinality ∷ Tagged Octant ℕ
  cardinality = Tagged 8
instance Finite     Octant
instance Fancy      Octant where
  unicode  ∷ Octant → Char
  unicode  = octant 'Ⅰ' 'Ⅱ' 'Ⅲ' 'Ⅳ' 'Ⅴ' 'Ⅵ' 'Ⅶ' 'Ⅷ'
  unicode' ∷ Octant → Char
  unicode' = octant 'ⅰ' 'ⅱ' 'ⅲ' 'ⅳ' 'ⅴ' 'ⅵ' 'ⅶ' 'ⅷ'
  plain    ∷ Octant → String
  plain    = octant "O₁" "O₂" "O₃" "O₄" "O₅" "O₆" "O₇" "O₈"
  named    ∷ Octant → String
  named    = const "Octant"
instance Show Octant where
  show ∷ Octant → String
  show = show₂
    where
      show₁ ∷ Octant → String
      show₁ = show'
      -- https://en.wikipedia.org/wiki/Octant_(solid_geometry)
      -- "The Roman enumeration of the quadrants is in Gray code order, so the corresponding Gray code is also shown for the octants."
      -- TODO other possible enumerations
      show₂ ∷ Octant → String
      show₂ = octant "(+; +; +)" "(-; +; +)" "(-; -; +)" "(+; -; +)" "(+; -; -)" "(-; -; -)" "(-; +; -)" "(+; +; -)"
      -- https://en.wikipedia.org/wiki/Octant_(plane_geometry)
      show₃ ∷ Octant → String
      show₃ = getOp (contramap toFin (Op (fin₈ "N" "NE" "E" "SE" "S" "SW" "W" "NW")))
        where
          fromFin ∷ Fin₈ → Octant
          fromFin = fin₈ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈
          toFin ∷ Octant → Fin₈
          toFin = octant 0 1 2 3 4 5 6 7

-- non unicode aliases for convenience
type O1 = 'O₁
type O2 = 'O₂
type O3 = 'O₃
type O4 = 'O₄
type O5 = 'O₅
type O6 = 'O₆
type O7 = 'O₇
type O8 = 'O₈
-- case analysis for `Octant` type
octant ∷ a → a → a → a → a → a → a → a → Octant → a
octant i _  _   _  _ _  _   _    O₁ = i
octant _ ii _   _  _ _  _   _    O₂ = ii
octant _ _  iii _  _ _  _   _    O₃ = iii
octant _ _  _   iv _ _  _   _    O₄ = iv
octant _ _  _   _  v _  _   _    O₅ = v
octant _ _  _   _  _ vi _   _    O₆ = vi
octant _ _  _   _  _ _  vii _    O₇ = vii
octant _ _  _   _  _ _  _   viii O₈ = viii

data Checker where
  (:⛀) ∷ Checker
  (:⛁) ∷ Checker
  (:⛂) ∷ Checker
  (:⛃) ∷ Checker
  deriving (Eq, Enum, Ord, Bounded)
instance U.Universe Checker
instance U.Finite   Checker where
  cardinality ∷ Tagged Checker ℕ
  cardinality = Tagged 4
instance Finite     Checker
instance Fancy      Checker where
  unicode ∷ Checker → Char
  unicode (:⛀) = '⛀'
  unicode (:⛁) = '⛁'
  unicode (:⛂) = '⛂'
  unicode (:⛃) = '⛃'
  plain ∷ Checker → String
  plain (:⛀) = "(:⛀)"
  plain (:⛁) = "(:⛁)"
  plain (:⛂) = "(:⛂)"
  plain (:⛃) = "(:⛃)"
  named ∷ Checker → String
  named = const "Checker"
instance Show Checker where
  show ∷ Checker → String
  show = show₁
    where
      show₁ ∷ Checker → String
      show₁ = show'
      show₂ ∷ Checker → String
      show₂ c = toColor (show' c) (toColor' c)

-- unicode aliases for convenience
(⛀) ∷ Checker
(⛀) = (:⛀)
(⛁) ∷ Checker
(⛁) = (:⛁)
(⛂) ∷ Checker
(⛂) = (:⛂)
(⛃) ∷ Checker
(⛃) = (:⛃)

data Suit where
  Spade   ∷ Suit
  Heart   ∷ Suit
  Diamond ∷ Suit
  Club    ∷ Suit
  deriving (Eq, Enum, Ord, Bounded)

instance U.Universe Suit
instance U.Finite   Suit where
  cardinality ∷ Tagged Suit ℕ
  cardinality = Tagged 4
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
  named ∷ Suit → String
  named = const "Suit"
  show' ∷ Suit → String
  show' s = charToString (unicode s) `toColor` toColor' s

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
  named ∷ Rank → String
  named = const "Rank"

instance Show Rank where
  show ∷ Rank → String
  show = show'

instance U.Universe Rank
instance U.Finite   Rank where
  cardinality ∷ Tagged Rank ℕ
  cardinality = Tagged 13
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
instance U.Finite   Card where
  cardinality ∷ Tagged Card ℕ
  cardinality = Tagged 52
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
  plain (Card r s) = plain r ++ " of " ++ plain s ++ "s"
  named ∷ Card → String
  named = const "Card"

instance Show Card where
  show ∷ Card → String
  show c = show' c `toColor` toColor' c

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

instance U.Universe      DisplayColor
instance U.Finite        DisplayColor where
  cardinality ∷ Tagged DisplayColor ℕ
  cardinality = Tagged 8
instance Finite          DisplayColor
instance HasDisplayColor DisplayColor where
  toColor' ∷ DisplayColor → DisplayColor
  toColor' = id
instance Show            DisplayColor where
  show ∷ DisplayColor → String
  show Black   = toColor "Black"   (toColor' Black)
  show Red     = toColor "Red"     (toColor' Red)
  show Green   = toColor "Green"   (toColor' Green)
  show Yellow  = toColor "Yellow"  (toColor' Yellow)
  show Blue    = toColor "Blue"    (toColor' Blue)
  show Magenta = toColor "Magenta" (toColor' Magenta)
  show Cyan    = toColor "Cyan"    (toColor' Cyan)
  show White   = toColor "White"   (toColor' White)

instance HasDisplayColor Suit where
  toColor' ∷ Suit → DisplayColor
  toColor' Spade   = Black
  toColor' Heart   = Red
  toColor' Diamond = Red
  toColor' Club    = Black

instance HasDisplayColor Checker where
  toColor' ∷ Checker → DisplayColor
  toColor' (:⛀) = Red
  toColor' (:⛁) = Red
  toColor' (:⛂) = Black
  toColor' (:⛃) = Black

instance HasDisplayColor Card where
  toColor' ∷ Card → DisplayColor
  toColor' = toColor' . suit

instance HasDisplayColor (:🎲) where
  -- TODO almost have the six colors of Rubik's cube, maybe try to update?
  toColor' ∷ (:🎲) → DisplayColor
  toColor' (:⚀) = Red     -- "⚀"
  toColor' (:⚁) = Magenta -- "⚁" -- Orange
  toColor' (:⚂) = Yellow  -- "⚂"
  toColor' (:⚃) = Green   -- "⚃"
  toColor' (:⚄) = Blue    -- "⚄"
  toColor' (:⚅) = White   -- "⚅"

instance HasDisplayColor (🁢) where
  toColor' ∷ (🁢) → DisplayColor
  toColor' = coloring . pick
    where
      pick ∷ (🁢) → Maybe (:🎲)
      pick = topOf -- bottomOf
      coloring ∷ Maybe (:🎲) → DisplayColor
      coloring = maybe Black toColor'
instance HasDisplayColor (🀰) where
  toColor' ∷ (🀰) → DisplayColor
  toColor' = coloring . pick
    where
      pick ∷ (🀰) → Maybe (:🎲)
      pick = leftOf -- rightOf
      coloring ∷ Maybe (:🎲) → DisplayColor
      coloring = maybe Black toColor'

instance HasDisplayColor Quadrant where
  toColor' ∷ Quadrant → DisplayColor
  toColor' = quadrant Black Red Green Yellow

instance HasDisplayColor Octant where
  toColor' ∷ Octant → DisplayColor
  toColor' = octant   Black Red Green Yellow Blue Magenta Cyan White

-- An involution is a mapping, f, that coincides with its own inverse, i.e.,
-- f x ≡ f⁻¹ x
-- or, equivalently,
-- f (f x) ≡ x
-- FIXME need to make this:
-- FIXME `⇒ NonEmpty (Either a b) → (a → b) → (b → a) → Bool`
-- FIXME so as to avoid:
-- FIXME ```
-- FIXME λ> involution [] id (const False)
-- FIXME True
-- FIXME ```
-- FIXME (but I want to address EasyTest problem first)
involution
  ∷ ∀ a b . (Eq a, Eq b)
  ⇒ [Either a b] → (a → b) → (b → a) → Bool
involution x ab ba = fmap (f . f) x == x
  where
    -- Turn an `a` into a `b` or
    -- turn a `b` into an `a`
    f ∷ Either a b → Either a b
    f = either (Right . ab) (Left . ba)

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses
-- A retraction, aka "left inverse"
retraction
  ∷ ∀ a b . (Finite a, Eq b)
  ⇒ (a → b) → (b → a) → Bool
retraction = involution (fmap Left (asList ∷ [a]))

-- A section, aka "right inverse"
section
  ∷ ∀ a b . (Eq a, Finite b)
  ⇒ (a → b) → (b → a) → Bool
section = involution (fmap Right (asList ∷ [b]))

bijection
  ∷ ∀ a b . (Finite a, Finite b)
  ⇒ (a → b) → (b → a) → Bool
bijection = involution (asList ∷ [Either a b])

