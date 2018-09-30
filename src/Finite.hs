{-# LANGUAGE InstanceSigs, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving, UnicodeSyntax, ExplicitForAll, ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}

module Finite where

import           Data.Set as Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Eq.Unicode
import           Control.Monad
import           Control.Applicative
import           Data.Maybe
import           Data.List
import           Data.Void
import           Data.Functor.Contravariant
import           Common
import           GHC.Enum
import           Data.Char

import qualified Data.Fin as F
import qualified Data.Type.Nat as N

instance Finite (F.Fin N.Nat1)
instance Finite (F.Fin N.Nat2)
instance Finite (F.Fin N.Nat3)
instance Finite (F.Fin N.Nat4)
instance Finite (F.Fin N.Nat5)
instance Finite (F.Fin N.Nat6)
instance Finite (F.Fin N.Nat7)
instance Finite (F.Fin N.Nat8)
instance Finite (F.Fin N.Nat9)

-- An imperfect, somewhat practical, representation of a Finite type constraint
-- The poor Haskeller's version of a Finite type constraint without reaching for dependent types
-- Will probably delete most of this once Haskell has better dependent type support :)
class (Enum a, Bounded a, Ord a) ⇒ Finite a where
  -- N.B. if overridding asList, make sure the list contains only distinct elements in ascending order.
  asList ∷ [a]
  asList = boundedEnumFrom minBound
  asSet ∷ Set a
  asSet = Set.fromDistinctAscList asList

class (Finite sigma) => Σ formalism sigma | formalism -> sigma where
  -- Σ, The alphabet of the formalism
  sigma :: formalism -> Set sigma
  sigma _ = asSet

  -- Σ⋆, Given a formalism, use its alphabet to lazily generate all possible strings
  sigmaStar :: formalism -> [[sigma]]
  sigmaStar _ = freeMonoid asList

  -- Σ⁺ = Σ⋆ \ {ε}, the positive closure
  sigmaPlus :: formalism -> [[sigma]]
  sigmaPlus _ = freeSemigroup asList

  -- (Σ ∪ {ε})
  sigma_ε :: formalism -> Set (Maybe sigma)
  sigma_ε m = Nothing `Set.insert` Set.mapMonotonic Just (sigma m)

-- Note well: some classes such as `MYT` and `GFA` need to account for extra states when declaring an instance of `Q`!
class (Finite q) => Q automaton q | automaton -> q where
  -- Q, The states of the Automaton
  qs :: automaton -> Set q
  qs _ = asSet

class (Finite g) => Γ automaton g | automaton -> g where
  -- Γ, the external alphabet of the automaton
  gamma :: automaton -> Set g
  gamma _ = asSet

instance                                                      Finite () where
  asList = [()]
  asSet  = Set.singleton ()
instance                                                      Finite Bool where
  asList = [False, True]
instance                                                      Finite Char

instance (Finite a) ⇒                                         Bounded (Set a) where
  minBound = (∅)
  -- I'd rather this were just `asSet` as in a Hasse diagram (even though there is a total order)
  -- but that would be inaccurate for the Data.Set implementation
  maxBound = singleton maxBound
-- For `Set a` where `a` is enumerable, enumerate the set as the powerset.
instance (Finite a) ⇒                                         Enum    (Set a) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a) ⇒                                         Finite  (Set a) where
  asList = Set.toList (powerSet asSet)
  asSet  = powerSet asSet

-- If `a` is bounded, then just move the lower bound to `Nothing`, and wrap the upper bound in a `Just`
-- This is one arbitrary possible instance
instance (Bounded a) ⇒                                        Bounded (Maybe a) where
  minBound = Nothing
  maxBound = Just maxBound
-- For `Maybe a` types where `a` is enumerable, enumerate as `Nothing : fmap Just [toEnum 0..]`.
instance (Finite a) ⇒                                         Enum    (Maybe a) where
  toEnum   ∷ Int     → Maybe a
  toEnum 0 = Nothing
  toEnum n = Just (toEnum (n - 1))
  fromEnum ∷ Maybe a → Int
  fromEnum Nothing  = 0
  fromEnum (Just t) = fromEnum t + 1
  enumFrom ∷ Maybe a → [Maybe a]
  enumFrom Nothing  = asList
  enumFrom (Just t) = fmap Just (enumFrom t)
instance (Finite a) ⇒                                         Finite  (Maybe a) where
  asList = Nothing : fmap Just asList
  asSet  = Set.insert Nothing (Set.mapMonotonic Just asSet)


instance (Bounded a, Bounded b) ⇒                             Bounded (Either a b) where
  minBound = Left  minBound
  maxBound = Right maxBound
-- For `(Either a b)` where types `a` and `b` are enumerable,
-- enumerate as the concatenation of the enumerations of `Left` then `Right` types.
instance (Finite a, Finite b) ⇒                               Enum    (Either a b) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a, Finite b) ⇒                               Finite  (Either a b) where
  asList = toList asSet
  asSet  = asSet ⊎ asSet


-- For tuples where types `a` and `b` are enumerable, allow the tuple to be enumerated as `a` × `b`
instance (Finite a, Finite b) ⇒                               Enum   (a, b) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a, Finite b) ⇒                               Finite (a, b) where
  asSet  = asSet × asSet
  asList = liftA2 (,)    asList asList


-- For tuples where types `a`, `b`, and `c` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c`
instance (Finite a, Finite b, Finite c) ⇒                     Enum   (a, b, c) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a, Finite b, Finite c) ⇒                     Finite (a, b, c) where
  asList = liftA3 (,,)   asList asList asList


-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Finite a, Finite b, Finite c, Finite d) ⇒           Enum   (a, b, c, d) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a, Finite b, Finite c, Finite d) ⇒           Finite (a, b, c, d) where
  asList = liftM4 (,,,)  asList asList asList asList


-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Finite a, Finite b, Finite c, Finite d, Finite e) ⇒ Enum   (a, b, c, d, e) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a, Finite b, Finite c, Finite d, Finite e) ⇒ Finite (a, b, c, d, e) where
  asList = liftM5 (,,,,) asList asList asList asList asList

-- Something like Fin₀
instance                                                      Enum    Void where
  toEnum   = undefined
  fromEnum = absurd
-- Easier to do this than write "BoundedOrEmpty" class because Enum and Bounded are everywhere :)
instance                                                      Bounded Void where
  minBound = undefined
  maxBound = undefined
instance                                                      Finite  Void where
  asList = []
  asSet  = (∅)

-- N.B. That it is possible to construct invalid Finₙ types, e.g. (`Fin₂ 9`) is perfectly legal Haskell and will compile
-- look away, I'm hideous
newtype Fin₁ = Fin₁ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁ where
  minBound = Fin₁ 0
  maxBound = Fin₁ 0
instance Enum Fin₁ where
  toEnum         0  = Fin₁ 0
  toEnum         n  = toEnumError "invalid Fin₁" n (minBound :: Fin₁, maxBound :: Fin₁)
  fromEnum (Fin₁ 0) =      0
  fromEnum (Fin₁ n) = error ("invalid (Fin₁ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁ where
  asList = [Fin₁ 0]

newtype Fin₂ = Fin₂ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₂ where
  minBound = Fin₂ 0
  maxBound = Fin₂ 1
instance Enum Fin₂ where
  toEnum         0  = Fin₂ 0
  toEnum         1  = Fin₂ 1
  toEnum         n  = toEnumError "invalid Fin₂" n (minBound :: Fin₂, maxBound :: Fin₂)
  fromEnum (Fin₂ 0) =      0
  fromEnum (Fin₂ 1) =      1
  fromEnum (Fin₂ n) = error ("invalid (Fin₂ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₂ where
  asList = [Fin₂ 0, Fin₂ 1]

newtype Fin₃ = Fin₃ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₃ where
  minBound = Fin₃ 0
  maxBound = Fin₃ 2
instance Enum Fin₃ where
  toEnum         0  = Fin₃ 0
  toEnum         1  = Fin₃ 1
  toEnum         2  = Fin₃ 2
  toEnum         n  = toEnumError "invalid Fin₃" n (minBound :: Fin₃, maxBound :: Fin₃)
  fromEnum (Fin₃ 0) =      0
  fromEnum (Fin₃ 1) =      1
  fromEnum (Fin₃ 2) =      2
  fromEnum (Fin₃ n) = error ("invalid (Fin₃ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₃ where
  asList = [Fin₃ 0, Fin₃ 1, Fin₃ 2]

newtype Fin₄ = Fin₄ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₄ where
  minBound = Fin₄ 0
  maxBound = Fin₄ 3
instance Enum Fin₄ where
  toEnum         0  = Fin₄ 0
  toEnum         1  = Fin₄ 1
  toEnum         2  = Fin₄ 2
  toEnum         3  = Fin₄ 3
  toEnum         n  = toEnumError "invalid Fin₄" n (minBound :: Fin₄, maxBound :: Fin₄)
  fromEnum (Fin₄ 0) =      0
  fromEnum (Fin₄ 1) =      1
  fromEnum (Fin₄ 2) =      2
  fromEnum (Fin₄ 3) =      3
  fromEnum (Fin₄ n) = error ("invalid (Fin₄ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₄ where
  asList = [Fin₄ 0, Fin₄ 1, Fin₄ 2, Fin₄ 3]

newtype Fin₅ = Fin₅ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₅ where
  minBound = Fin₅ 0
  maxBound = Fin₅ 4

instance Enum Fin₅ where
  toEnum         0  = Fin₅ 0
  toEnum         1  = Fin₅ 1
  toEnum         2  = Fin₅ 2
  toEnum         3  = Fin₅ 3
  toEnum         4  = Fin₅ 4
  toEnum         n  = toEnumError "invalid Fin₅" n (minBound :: Fin₅, maxBound :: Fin₅)
  fromEnum (Fin₅ 0) =      0
  fromEnum (Fin₅ 1) =      1
  fromEnum (Fin₅ 2) =      2
  fromEnum (Fin₅ 3) =      3
  fromEnum (Fin₅ 4) =      4
  fromEnum (Fin₅ n) = error ("invalid (Fin₅ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₅ where
  asList = [Fin₅ 0, Fin₅ 1, Fin₅ 2, Fin₅ 3, Fin₅ 4]

newtype Fin₆ = Fin₆ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₆ where
  minBound = Fin₆ 0
  maxBound = Fin₆ 5
instance Enum Fin₆ where
  toEnum         0  = Fin₆ 0
  toEnum         1  = Fin₆ 1
  toEnum         2  = Fin₆ 2
  toEnum         3  = Fin₆ 3
  toEnum         4  = Fin₆ 4
  toEnum         5  = Fin₆ 5
  toEnum         n  = toEnumError "invalid Fin₆" n (minBound :: Fin₆, maxBound :: Fin₆)
  fromEnum (Fin₆ 0) =      0
  fromEnum (Fin₆ 1) =      1
  fromEnum (Fin₆ 2) =      2
  fromEnum (Fin₆ 3) =      3
  fromEnum (Fin₆ 4) =      4
  fromEnum (Fin₆ 5) =      5
  fromEnum (Fin₆ n) = error ("invalid (Fin₆ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₆ where
  asList = [Fin₆ 0, Fin₆ 1, Fin₆ 2, Fin₆ 3, Fin₆ 4, Fin₆ 5]

newtype Fin₇ = Fin₇ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₇ where
  minBound = Fin₇ 0
  maxBound = Fin₇ 6
instance Enum Fin₇ where
  toEnum         0  = Fin₇ 0
  toEnum         1  = Fin₇ 1
  toEnum         2  = Fin₇ 2
  toEnum         3  = Fin₇ 3
  toEnum         4  = Fin₇ 4
  toEnum         5  = Fin₇ 5
  toEnum         6  = Fin₇ 6
  toEnum         n  = toEnumError "invalid Fin₇" n (minBound :: Fin₇, maxBound :: Fin₇)
  fromEnum (Fin₇ 0) =      0
  fromEnum (Fin₇ 1) =      1
  fromEnum (Fin₇ 2) =      2
  fromEnum (Fin₇ 3) =      3
  fromEnum (Fin₇ 4) =      4
  fromEnum (Fin₇ 5) =      5
  fromEnum (Fin₇ 6) =      6
  fromEnum (Fin₇ n) = error ("invalid (Fin₇ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₇ where
  asList = [Fin₇ 0, Fin₇ 1, Fin₇ 2, Fin₇ 3, Fin₇ 4, Fin₇ 5, Fin₇ 6]

newtype Fin₈ = Fin₈ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₈ where
  minBound = Fin₈ 0
  maxBound = Fin₈ 7
instance Enum Fin₈ where
  toEnum         0  = Fin₈ 0
  toEnum         1  = Fin₈ 1
  toEnum         2  = Fin₈ 2
  toEnum         3  = Fin₈ 3
  toEnum         4  = Fin₈ 4
  toEnum         5  = Fin₈ 5
  toEnum         6  = Fin₈ 6
  toEnum         7  = Fin₈ 7
  toEnum         n  = toEnumError "invalid Fin₈" n (minBound :: Fin₈, maxBound :: Fin₈)
  fromEnum (Fin₈ 0) =      0
  fromEnum (Fin₈ 1) =      1
  fromEnum (Fin₈ 2) =      2
  fromEnum (Fin₈ 3) =      3
  fromEnum (Fin₈ 4) =      4
  fromEnum (Fin₈ 5) =      5
  fromEnum (Fin₈ 6) =      6
  fromEnum (Fin₈ 7) =      7
  fromEnum (Fin₈ n) = error ("invalid (Fin₈ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₈ where
  asList = [Fin₈ 0, Fin₈ 1, Fin₈ 2, Fin₈ 3, Fin₈ 4, Fin₈ 5, Fin₈ 6, Fin₈ 7]

newtype Fin₉ = Fin₉ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₉ where
  minBound = Fin₉ 0
  maxBound = Fin₉ 8
instance Enum Fin₉ where
  toEnum         0  = Fin₉ 0
  toEnum         1  = Fin₉ 1
  toEnum         2  = Fin₉ 2
  toEnum         3  = Fin₉ 3
  toEnum         4  = Fin₉ 4
  toEnum         5  = Fin₉ 5
  toEnum         6  = Fin₉ 6
  toEnum         7  = Fin₉ 7
  toEnum         8  = Fin₉ 8
  toEnum         n  = toEnumError "invalid Fin₉" n (minBound :: Fin₉, maxBound :: Fin₉)
  fromEnum (Fin₉ 0) =      0
  fromEnum (Fin₉ 1) =      1
  fromEnum (Fin₉ 2) =      2
  fromEnum (Fin₉ 3) =      3
  fromEnum (Fin₉ 4) =      4
  fromEnum (Fin₉ 5) =      5
  fromEnum (Fin₉ 6) =      6
  fromEnum (Fin₉ 7) =      7
  fromEnum (Fin₉ 8) =      8
  fromEnum (Fin₉ n) = error ("invalid (Fin₉ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₉ where
  asList = [Fin₉ 0, Fin₉ 1, Fin₉ 2, Fin₉ 3, Fin₉ 4, Fin₉ 5, Fin₉ 6, Fin₉ 7, Fin₉ 8]

newtype Fin₁₀ = Fin₁₀ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁₀ where
  minBound = Fin₁₀ 0
  maxBound = Fin₁₀ 9
instance Enum Fin₁₀ where
  toEnum          0  = Fin₁₀ 0
  toEnum          1  = Fin₁₀ 1
  toEnum          2  = Fin₁₀ 2
  toEnum          3  = Fin₁₀ 3
  toEnum          4  = Fin₁₀ 4
  toEnum          5  = Fin₁₀ 5
  toEnum          6  = Fin₁₀ 6
  toEnum          7  = Fin₁₀ 7
  toEnum          8  = Fin₁₀ 8
  toEnum          9  = Fin₁₀ 9
  toEnum          n  = toEnumError "invalid Fin₁₀" n (minBound :: Fin₁₀, maxBound :: Fin₁₀)
  fromEnum (Fin₁₀ 0) =       0
  fromEnum (Fin₁₀ 1) =       1
  fromEnum (Fin₁₀ 2) =       2
  fromEnum (Fin₁₀ 3) =       3
  fromEnum (Fin₁₀ 4) =       4
  fromEnum (Fin₁₀ 5) =       5
  fromEnum (Fin₁₀ 6) =       6
  fromEnum (Fin₁₀ 7) =       7
  fromEnum (Fin₁₀ 8) =       8
  fromEnum (Fin₁₀ 9) =       9
  fromEnum (Fin₁₀ n) = error ("invalid (Fin₁₀ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁₀ where
  asList = [Fin₁₀ 0, Fin₁₀ 1, Fin₁₀ 2, Fin₁₀ 3, Fin₁₀ 4, Fin₁₀ 5, Fin₁₀ 6, Fin₁₀ 7, Fin₁₀ 8, Fin₁₀ 9]

newtype Fin₁₁ = Fin₁₁ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁₁ where
  minBound = Fin₁₁ 0
  maxBound = Fin₁₁ 10
instance Enum Fin₁₁ where
  toEnum          0   = Fin₁₁ 0
  toEnum          1   = Fin₁₁ 1
  toEnum          2   = Fin₁₁ 2
  toEnum          3   = Fin₁₁ 3
  toEnum          4   = Fin₁₁ 4
  toEnum          5   = Fin₁₁ 5
  toEnum          6   = Fin₁₁ 6
  toEnum          7   = Fin₁₁ 7
  toEnum          8   = Fin₁₁ 8
  toEnum          9   = Fin₁₁ 9
  toEnum          10  = Fin₁₁ 10
  toEnum          n   = toEnumError "invalid Fin₁₁" n (minBound :: Fin₁₁, maxBound :: Fin₁₁)
  fromEnum (Fin₁₁ 0)  =       0
  fromEnum (Fin₁₁ 1)  =       1
  fromEnum (Fin₁₁ 2)  =       2
  fromEnum (Fin₁₁ 3)  =       3
  fromEnum (Fin₁₁ 4)  =       4
  fromEnum (Fin₁₁ 5)  =       5
  fromEnum (Fin₁₁ 6)  =       6
  fromEnum (Fin₁₁ 7)  =       7
  fromEnum (Fin₁₁ 8)  =       8
  fromEnum (Fin₁₁ 9)  =       9
  fromEnum (Fin₁₁ 10) =       10
  fromEnum (Fin₁₁ n)  = error ("invalid (Fin₁₁ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁₁ where
  asList = [Fin₁₁ 0, Fin₁₁ 1, Fin₁₁ 2, Fin₁₁ 3, Fin₁₁ 4, Fin₁₁ 5, Fin₁₁ 6, Fin₁₁ 7, Fin₁₁ 8, Fin₁₁ 9, Fin₁₁ 10]

newtype Fin₁₂ = Fin₁₂ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁₂ where
  minBound = Fin₁₂ 0
  maxBound = Fin₁₂ 11
instance Enum Fin₁₂ where
  toEnum          0   = Fin₁₂ 0
  toEnum          1   = Fin₁₂ 1
  toEnum          2   = Fin₁₂ 2
  toEnum          3   = Fin₁₂ 3
  toEnum          4   = Fin₁₂ 4
  toEnum          5   = Fin₁₂ 5
  toEnum          6   = Fin₁₂ 6
  toEnum          7   = Fin₁₂ 7
  toEnum          8   = Fin₁₂ 8
  toEnum          9   = Fin₁₂ 9
  toEnum          10  = Fin₁₂ 10
  toEnum          11  = Fin₁₂ 11
  toEnum          n   = toEnumError "invalid Fin₁₂" n (minBound :: Fin₁₂, maxBound :: Fin₁₂)
  fromEnum (Fin₁₂ 0)  =       0
  fromEnum (Fin₁₂ 1)  =       1
  fromEnum (Fin₁₂ 2)  =       2
  fromEnum (Fin₁₂ 3)  =       3
  fromEnum (Fin₁₂ 4)  =       4
  fromEnum (Fin₁₂ 5)  =       5
  fromEnum (Fin₁₂ 6)  =       6
  fromEnum (Fin₁₂ 7)  =       7
  fromEnum (Fin₁₂ 8)  =       8
  fromEnum (Fin₁₂ 9)  =       9
  fromEnum (Fin₁₂ 10) =       10
  fromEnum (Fin₁₂ 11) =       11
  fromEnum (Fin₁₂ n)  = error ("invalid (Fin₁₂ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁₂ where
  asList = [Fin₁₂ 0, Fin₁₂ 1, Fin₁₂ 2, Fin₁₂ 3, Fin₁₂ 4, Fin₁₂ 5, Fin₁₂ 6, Fin₁₂ 7, Fin₁₂ 8, Fin₁₂ 9, Fin₁₂ 10, Fin₁₂ 11]

newtype Fin₁₃ = Fin₁₃ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁₃ where
  minBound = Fin₁₃ 0
  maxBound = Fin₁₃ 12
instance Enum Fin₁₃ where
  toEnum          0   = Fin₁₃ 0
  toEnum          1   = Fin₁₃ 1
  toEnum          2   = Fin₁₃ 2
  toEnum          3   = Fin₁₃ 3
  toEnum          4   = Fin₁₃ 4
  toEnum          5   = Fin₁₃ 5
  toEnum          6   = Fin₁₃ 6
  toEnum          7   = Fin₁₃ 7
  toEnum          8   = Fin₁₃ 8
  toEnum          9   = Fin₁₃ 9
  toEnum          10  = Fin₁₃ 10
  toEnum          11  = Fin₁₃ 11
  toEnum          12  = Fin₁₃ 12
  toEnum          n   = toEnumError "invalid Fin₁₃" n (minBound :: Fin₁₃, maxBound :: Fin₁₃)
  fromEnum (Fin₁₃ 0)  =       0
  fromEnum (Fin₁₃ 1)  =       1
  fromEnum (Fin₁₃ 2)  =       2
  fromEnum (Fin₁₃ 3)  =       3
  fromEnum (Fin₁₃ 4)  =       4
  fromEnum (Fin₁₃ 5)  =       5
  fromEnum (Fin₁₃ 6)  =       6
  fromEnum (Fin₁₃ 7)  =       7
  fromEnum (Fin₁₃ 8)  =       8
  fromEnum (Fin₁₃ 9)  =       9
  fromEnum (Fin₁₃ 10) =       10
  fromEnum (Fin₁₃ 11) =       11
  fromEnum (Fin₁₃ 12) =       12
  fromEnum (Fin₁₃ n) = error ("invalid (Fin₁₃ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁₃ where
  asList = [Fin₁₃ 0, Fin₁₃ 1, Fin₁₃ 2, Fin₁₃ 3, Fin₁₃ 4, Fin₁₃ 5, Fin₁₃ 6, Fin₁₃ 7, Fin₁₃ 8, Fin₁₃ 9, Fin₁₃ 10, Fin₁₃ 11, Fin₁₃ 12]

newtype Fin₁₄ = Fin₁₄ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁₄ where
  minBound = Fin₁₄ 0
  maxBound = Fin₁₄ 13
instance Enum Fin₁₄ where
  toEnum          0   = Fin₁₄ 0
  toEnum          1   = Fin₁₄ 1
  toEnum          2   = Fin₁₄ 2
  toEnum          3   = Fin₁₄ 3
  toEnum          4   = Fin₁₄ 4
  toEnum          5   = Fin₁₄ 5
  toEnum          6   = Fin₁₄ 6
  toEnum          7   = Fin₁₄ 7
  toEnum          8   = Fin₁₄ 8
  toEnum          9   = Fin₁₄ 9
  toEnum          10  = Fin₁₄ 10
  toEnum          11  = Fin₁₄ 11
  toEnum          12  = Fin₁₄ 12
  toEnum          13  = Fin₁₄ 13
  toEnum          n   = toEnumError "invalid Fin₁₄" n (minBound :: Fin₁₄, maxBound :: Fin₁₄)
  fromEnum (Fin₁₄ 0)  =       0
  fromEnum (Fin₁₄ 1)  =       1
  fromEnum (Fin₁₄ 2)  =       2
  fromEnum (Fin₁₄ 3)  =       3
  fromEnum (Fin₁₄ 4)  =       4
  fromEnum (Fin₁₄ 5)  =       5
  fromEnum (Fin₁₄ 6)  =       6
  fromEnum (Fin₁₄ 7)  =       7
  fromEnum (Fin₁₄ 8)  =       8
  fromEnum (Fin₁₄ 9)  =       9
  fromEnum (Fin₁₄ 10) =       10
  fromEnum (Fin₁₄ 11) =       11
  fromEnum (Fin₁₄ 12) =       12
  fromEnum (Fin₁₄ 13) =       13
  fromEnum (Fin₁₄ n)  = error ("invalid (Fin₁₄ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁₄ where
  asList = [Fin₁₄ 0, Fin₁₄ 1, Fin₁₄ 2, Fin₁₄ 3, Fin₁₄ 4, Fin₁₄ 5, Fin₁₄ 6, Fin₁₄ 7, Fin₁₄ 8, Fin₁₄ 9, Fin₁₄ 10, Fin₁₄ 11, Fin₁₄ 12, Fin₁₄ 13]

newtype Fin₁₅ = Fin₁₅ ℕ deriving (Eq, Ord, Num, Show)
instance Bounded Fin₁₅ where
  minBound = Fin₁₅ 0
  maxBound = Fin₁₅ 14
instance Enum Fin₁₅ where
  toEnum          0   = Fin₁₅ 0
  toEnum          1   = Fin₁₅ 1
  toEnum          2   = Fin₁₅ 2
  toEnum          3   = Fin₁₅ 3
  toEnum          4   = Fin₁₅ 4
  toEnum          5   = Fin₁₅ 5
  toEnum          6   = Fin₁₅ 6
  toEnum          7   = Fin₁₅ 7
  toEnum          8   = Fin₁₅ 8
  toEnum          9   = Fin₁₅ 9
  toEnum          10  = Fin₁₅ 10
  toEnum          11  = Fin₁₅ 11
  toEnum          12  = Fin₁₅ 12
  toEnum          13  = Fin₁₅ 13
  toEnum          14  = Fin₁₅ 14
  toEnum          n   = toEnumError "invalid Fin₁₅" n (minBound :: Fin₁₅, maxBound :: Fin₁₅)
  fromEnum (Fin₁₅ 0)  =       0
  fromEnum (Fin₁₅ 1)  =       1
  fromEnum (Fin₁₅ 2)  =       2
  fromEnum (Fin₁₅ 3)  =       3
  fromEnum (Fin₁₅ 4)  =       4
  fromEnum (Fin₁₅ 5)  =       5
  fromEnum (Fin₁₅ 6)  =       6
  fromEnum (Fin₁₅ 7)  =       7
  fromEnum (Fin₁₅ 8)  =       8
  fromEnum (Fin₁₅ 9)  =       9
  fromEnum (Fin₁₅ 10) =       10
  fromEnum (Fin₁₅ 11) =       11
  fromEnum (Fin₁₅ 12) =       12
  fromEnum (Fin₁₅ 13) =       13
  fromEnum (Fin₁₅ 14) =       14
  fromEnum (Fin₁₅ n)  = error ("invalid (Fin₁₅ " ++ show n ++ ") in fromEnum")
  enumFrom     = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
instance Finite Fin₁₅ where
  asList = [Fin₁₅ 0, Fin₁₅ 1, Fin₁₅ 2, Fin₁₅ 3, Fin₁₅ 4, Fin₁₅ 5, Fin₁₅ 6, Fin₁₅ 7, Fin₁₅ 8, Fin₁₅ 9, Fin₁₅ 10, Fin₁₅ 11, Fin₁₅ 12, Fin₁₅ 13, Fin₁₅ 14]

-- TODO deleteme
instance (Show a, Finite a) ⇒ Show (Predicate a) where
  show (Predicate p) = unlines (fmap show' res1)
                 where domain = asList ∷ [a]
                       res1 = zip domain (fmap p domain)
                       show' (a, b) = show a ++ " ↦ " ++ show b

instance (Finite a) ⇒                                         Eq      (Predicate a) where
  (==) ∷ Predicate a → Predicate a → Bool
  (Predicate f) == (Predicate g) = and (fmap (\x → f x == g x) asList)
instance (Finite a) ⇒                                         Bounded (Predicate a) where
  minBound = Predicate (const False)
  maxBound = Predicate (const True)
instance (Finite a) ⇒                                         Ord     (Predicate a) where
  compare ∷ Predicate a → Predicate a → Ordering
  compare (Predicate f) (Predicate g) = mconcat (fmap (\x → f x `compare` g x) asList)
instance (Finite a) ⇒                                         Enum    (Predicate a) where
  toEnum   ∷ Int         → Predicate a
  toEnum     =                       (asList !!)
  fromEnum ∷ Predicate a → Int
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom ∷ Predicate a → [Predicate a]
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a) ⇒                                         Finite  (Predicate a) where
  asList ∷ [Predicate a]
  asList = fmap (Predicate . toFunction . zip as) bits
        where as ∷ [a]
              as = asList
              bs ∷ [Bool]
              bs = asList
              bits :: [[Bool]]
              bits = replicateM (length as) bs
              toFunction ∷ [(a, Bool)] → a → Bool
              -- toFunction list = \a → fromJust (lookup a list) -- TODO I like this better but need to get rid of hlint warning -- {-# ANN asList "HLint: warn Redundant lambda" #-}
              toFunction list a = fromJust (lookup a list)

data Alpha = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z deriving (Eq, Ord, Enum, Bounded, Show, Read)
instance                                                       Finite Alpha where
  asList = [A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z]



data Digits = Zero | One | Two   | Three | Four
            | Five | Six | Seven | Eight | Nine deriving (Eq, Ord, Enum, Bounded)
instance Show Digits where
  show = show . fromEnum
instance                                                       Finite Digits where
  asList = [Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine]

-- TODO move this helper function back to Common once `ℕ` is added to unicode lib; putting it in Common would cause an import cycle for now though..
toDigits :: ℕ -> [Digits]
toDigits = fmap (toEnum . digitToInt) . show

data DNA = Adenine | Cytosine | Guanine | Thymine deriving (Eq, Ord, Bounded, Enum)
instance Show DNA where
  show Adenine  = "A"
  show Cytosine = "C"
  show Guanine  = "G"
  show Thymine  = "T"
instance Finite DNA where
  asList = [Adenine, Cytosine, Guanine, Thymine]


newtype Init  =  Init () deriving (Eq, Ord, Bounded, Enum)
instance                                                       Finite Init where
  asList = [Init ()]
  asSet  = Set.singleton (Init ())
instance Show Init where
  show (Init ()) = "qᵢ"
newtype Final = Final () deriving (Eq, Ord, Bounded, Enum)
instance                                                       Finite Final where
  asList = [Final ()]
  asSet  = Set.singleton (Final ())
instance Show Final where
  show (Final ()) = "qᶠ"
type InitOrFinal = Either Init Final
