{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExplicitForAll             #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}

module Finite where

import           Data.Set as Set
import           Data.Set.Unicode
import           Data.Eq.Unicode
import           Data.Bool.Unicode
import           Control.Monad
import           Control.Applicative
import           Data.List as List
import           Data.List.NonEmpty (NonEmpty, NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import           Data.Maybe
import           Data.These
import           Data.Void
import           Data.Function
import           Data.Functor.Contravariant
import           Common
import           GHC.Enum (boundedEnumFrom)
import           Data.Fin (Fin)
import qualified Data.Type.Nat as Nat
-- import qualified Data.Universe as U

-- An imperfect, somewhat practical, representation of a Finite type constraint
-- The poor Haskeller's version of a Finite type constraint without reaching for dependent types
-- Will probably delete most of this once Haskell has better dependent type support :)
class (Enum a, Bounded a, Ord a) ⇒ Finite a where
  -- N.B. if overridding asList, make sure the list contains only distinct elements in ascending order.
  asList ∷ [a]
  asList = boundedEnumFrom minBound
  asSet ∷ Set a
  asSet = Set.fromDistinctAscList asList

class (Finite sigma) ⇒ Σ formalism sigma | formalism → sigma where
  -- Σ, The alphabet of the formalism
  sigma ∷ formalism → Set sigma
  sigma _ = asSet

  -- Σ⋆, Given a formalism, use its alphabet to lazily generate all possible strings
  sigmaStar ∷ formalism → [[sigma]]
  sigmaStar _ = freeMonoid asList

  -- Σ⁺ = Σ⋆ \ {ε}, the positive closure
  sigmaPlus ∷ formalism → [[sigma]]
  sigmaPlus _ = freeSemigroup asList

  -- (Σ ∪ {ε})
  sigma_ε ∷ formalism → Set (Maybe sigma)
  sigma_ε m = Nothing `Set.insert` Set.mapMonotonic Just (sigma m)

-- Note well: some classes such as `MYT` and `GFA` need to account for extra states when declaring an instance of `Q`!
class (Finite q) ⇒ Q automaton q | automaton → q where
  -- Q, The states of the Automaton
  qs ∷ automaton → Set q
  qs _ = asSet

class (Finite g) ⇒ Γ automaton g | automaton → g where
  -- Γ, the external alphabet of the automaton
  gamma ∷ automaton → Set g
  gamma _ = asSet

instance                                                      Finite () where
  asList = [()]
  asSet  = Set.singleton ()
instance                                                      Finite Bool where
  asList = [False, True]
instance                                                      Finite Ordering where
  asList = [LT, EQ, GT]
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

instance (Bounded a, Bounded b) ⇒                             Bounded (These a b) where
  minBound ∷ These a b
  minBound = This  minBound
  maxBound ∷ These a b
  maxBound = These  maxBound maxBound  -- maxBound = That  maxBound
instance (Finite a, Finite b) ⇒                               Enum    (These a b) where
  toEnum     =                       (asList !!)
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a, Finite b) ⇒                               Finite  (These a b) where
  asList ∷ [These a b]
  asList = toList asSet
  asSet ∷ Set (These a b)
  asSet = Set.map to (products ⊎ sums)
    where
      to   ∷ Either (a, b) (Either a b) → These a b
      to   (Left  (a, b)  )             = These a b
      to   (Right (Right b))            = That    b
      to   (Right (Left  a))            = This  a
      from ∷ These a b                  → Either (a, b) (Either a b)
      from (These a b)                  = Left  (a, b)
      from (That    b)                  = Right (Right b)
      from (This  a  )                  = Right (Left  a)
      products ∷ Set (a, b) 
      products = asSet
      sums ∷ Set (Either a b)
      sums = asSet -- asSet ⊎ asSet

-- For tuples where types `a` and `b` are enumerable, allow the tuple to be enumerated as `a` × `b`
instance (Finite a, Finite b) ⇒                               Enum   (a, b) where
  toEnum ∷ Int → (a, b)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ)
    where (i₁, bᵢ) = i₀ `quotRem` length (asList ∷ [b])
          (_,  aᵢ) = i₁ `quotRem` length (asList ∷ [a])
  fromEnum ∷ (a, b) → Int
  fromEnum (a, b) = (aᵢ * lb) + bᵢ
    where (aᵢ, bᵢ) = (fromEnum a, fromEnum b)
          lb = length (asList ∷ [b])

  enumFrom ∷ (a, b) → [(a, b)]
  -- enumFrom t = dropWhile (≠ t)        asList
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b) ⇒                               Finite (a, b) where
  asSet  = asSet × asSet
  asList = liftA2 (,)    asList asList


-- For tuples where types `a`, `b`, and `c` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c`
instance (Finite a, Finite b, Finite c) ⇒                     Enum   (a, b, c) where
  toEnum ∷ Int → (a, b, c)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ)
    where (i₁, cᵢ) = i₀ `quotRem` length (asList ∷ [c])
          (i₂, bᵢ) = i₁ `quotRem` length (asList ∷ [b])
          (_,  aᵢ) = i₂ `quotRem` length (asList ∷ [a])
  fromEnum ∷ (a, b, c) → Int
  fromEnum (a, b, c) = (aᵢ * lb * lc) + (bᵢ * lc) + cᵢ
    where (aᵢ, bᵢ, cᵢ) = (fromEnum a, fromEnum b, fromEnum c)
          lb = length (asList ∷ [b])
          lc = length (asList ∷ [c])
  enumFrom ∷ (a, b, c) → [(a, b, c)]
  -- enumFrom t = dropWhile (≠ t)        asList
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b, Finite c) ⇒                     Finite (a, b, c) where
  asList = liftA3 (,,)   asList asList asList


-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Finite a, Finite b, Finite c, Finite d) ⇒           Enum   (a, b, c, d) where
  toEnum ∷ Int → (a, b, c, d)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ, toEnum dᵢ)
    where (i₁, dᵢ) = i₀ `quotRem` length (asList ∷ [d])
          (i₂, cᵢ) = i₁ `quotRem` length (asList ∷ [c])
          (i₃, bᵢ) = i₂ `quotRem` length (asList ∷ [b])
          (_,  aᵢ) = i₃ `quotRem` length (asList ∷ [a])
  fromEnum ∷ (a, b, c, d) → Int
  fromEnum (a, b, c, d) = (aᵢ * lb * lc * ld) + (bᵢ * lc * ld) + (cᵢ * ld) + dᵢ
    where (aᵢ, bᵢ, cᵢ, dᵢ) = (fromEnum a, fromEnum b, fromEnum c, fromEnum d)
          lb = length (asList ∷ [b])
          lc = length (asList ∷ [c])
          ld = length (asList ∷ [d])
  enumFrom ∷ (a, b, c, d) → [(a, b, c, d)]
  -- enumFrom t = dropWhile (≠ t)        asList
  enumFrom = boundedEnumFrom

instance (Finite a, Finite b, Finite c, Finite d) ⇒           Finite (a, b, c, d) where
  asList = liftM4 (,,,)  asList asList asList asList


-- For tuples where types `a`, `b`, `c` and `d` are enumerable, allow the tuple to be enumerated as `a` × `b` × `c` × `d`
instance (Finite a, Finite b, Finite c, Finite d, Finite e) ⇒ Enum   (a, b, c, d, e) where
  toEnum ∷ Int → (a, b, c, d, e)
  toEnum i₀ = (toEnum aᵢ, toEnum bᵢ, toEnum cᵢ, toEnum dᵢ, toEnum eᵢ)
    where
      (i₁, eᵢ) = i₀ `quotRem` length (asList ∷ [e])
      (i₂, dᵢ) = i₁ `quotRem` length (asList ∷ [d])
      (i₃, cᵢ) = i₂ `quotRem` length (asList ∷ [c])
      (i₄, bᵢ) = i₃ `quotRem` length (asList ∷ [b])
      (_,  aᵢ) = i₄ `quotRem` length (asList ∷ [a])

  fromEnum ∷ (a, b, c, d, e) → Int
  fromEnum (a, b, c, d, e) = (aᵢ * lb * lc * ld * le) + (bᵢ * lc * ld * le) + (cᵢ * ld * le) + (dᵢ * le) + eᵢ
    where (aᵢ, bᵢ, cᵢ, dᵢ, eᵢ) = (fromEnum a, fromEnum b, fromEnum c, fromEnum d, fromEnum e)
          lb = length (asList ∷ [b])
          lc = length (asList ∷ [c])
          ld = length (asList ∷ [d])
          le = length (asList ∷ [e])

  enumFrom ∷ (a, b, c, d, e) → [(a, b, c, d, e)]
  -- enumFrom t = dropWhile (≠ t)        asList
  enumFrom = boundedEnumFrom

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

instance Finite Fin₁
instance Finite Fin₂
instance Finite Fin₃
instance Finite Fin₄
instance Finite Fin₅
instance Finite Fin₆
instance Finite Fin₇
instance Finite Fin₈
instance Finite Fin₉
instance Finite Fin₁₀
instance Finite Fin₁₁
instance Finite Fin₁₂
instance Finite Fin₁₃
instance Finite Fin₁₄
instance Finite Fin₁₅

-- TODO deleteme
instance (Show a, Finite a) ⇒ Show (Predicate a) where
  show (Predicate p) = unlines (fmap show' graph)
                 where domain = asList ∷ [a]
                       image  = fmap p domain
                       graph  = zip domain image
                       show' (a, b) = show a ++ " ↦ " ++ show b

instance (Finite a) ⇒                                         Eq      (Predicate a) where
  (==) ∷ Predicate a → Predicate a → Bool
  (Predicate p₁) == (Predicate p₂) = all (\a → p₁ a == p₂ a) asList
instance                                                      Bounded (Predicate a) where
  minBound = Predicate (const False)
  maxBound = Predicate (const True)
instance (Finite a) ⇒                                         Ord     (Predicate a) where
  compare ∷ Predicate a → Predicate a → Ordering
  compare (Predicate p₁) (Predicate p₂) = mconcat (fmap (\a → p₁ a `compare` p₂ a) asList)
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
              bits ∷ [[Bool]]
              bits = replicateM (length as) bs
              toFunction ∷ [(a, Bool)] → a → Bool
              -- toFunction list = \a → fromJust (lookup a list) -- TODO I like this better but need to get rid of hlint warning -- {-# ANN asList "HLint: warn Redundant lambda" #-}
              toFunction list a = fromJust (lookup a list)

-- TODO may want to move this code (if keeping it) to testing folder when done implementing `Finite` instance for `Equivalence`.

-- Reflexive
refl ∷ (Finite a) ⇒ Equivalence a → Bool
refl (Equivalence (≡)) = all (\x → x ≡ x) asSet

-- Symmetric
sym ∷ (Finite a) ⇒  Equivalence a → Bool
sym (Equivalence (≡)) = all (\(x, y) → (x ≡ y) == (y ≡ x)) (asSet × asSet)

-- Transitive
trans ∷ (Finite a) ⇒ Equivalence a → Bool
trans (Equivalence (≡)) = all (\(x, y, z) → ((x ≡ y) ∧ (y ≡ z)) `implies` (x ≡ z)) (liftA3 (,,) asList asList asList) -- TODO may be some redundant checks here I can eliminate

-- Check that the equivalence relation is lawful
lawful ∷ (Finite a) ⇒ Equivalence a → Bool
lawful (≡) = refl  (≡)
           ∧ sym   (≡)
           ∧ trans (≡)

-- r₁ is "finer" r₂ iff r₁ ⊆ r₂   i.e. r₁ is a refinement of r₂
-- if r₁ is a refinement of r₂ then each equivalence class of r₂ is
-- a union of some of the equivalence classes of r₁.
-- The finer-than relation reflexive, transitive, and antisymmetric (a partial order)
finer ∷ (Finite a) ⇒ Equivalence a → Equivalence a → Bool
finer (Equivalence r₁) (Equivalence r₂) = all (\(x, y) → r₁ x y `implies` r₂ x y) (liftA2 (,) asList asList)

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
toEquivalence parts = Equivalence (\a₁ a₂ → any (\xs → (a₁ `elem` xs) ∧ (a₂ `elem` xs)) parts)

fromEquivalence ∷ ∀ a . (Finite a) ⇒ Equivalence a → [NonEmpty a]
fromEquivalence (Equivalence r) = unfoldr go asList
      where go ∷ [a] → Maybe (NonEmpty a, [a])
            go []       = Nothing
            go (x : xs) = Just (x :| p, np)
                    where (p, np) = List.partition (r x) xs

toPredicate ∷ (Foldable t, Eq a) ⇒ t a → Predicate a
toPredicate = Predicate . flip elem

-- TODO better name?
-- fromPredicate (Predicate (> 2) ∷ Predicate Fin₁₀) == [[0,1,2],[3,4,5,6,7,8,9]]
-- N.B. information is lost here, we can't distinguish `p` from `(not . p)` anymore
fromPredicate ∷ Predicate a → Equivalence a
fromPredicate (Predicate p) = contramap p defaultEquivalence

-- There is a way to do this safely by generating the NonEmpty list for the equivalence class
-- and then using comonadic extract to guarantee the representative will always be there
-- and thus avoiding the unsafe `head` but that seems like too much overhead for right now
-- The correct type for this should actually be:
-- representative ∷ (Finite a) ⇒ Equivalence a → Maybe (a → a)
-- Because the null relation is (vacuously) a lawful equivalence relation
-- https://proofwiki.org/wiki/Relation_on_Empty_Set_is_Equivalence
representative ∷ (Finite a) ⇒ Equivalence a → a → a
representative (Equivalence (≡)) a = head (List.filter ((≡) a) asList)

representatives ∷ (Finite a) ⇒ Equivalence a → [a]
representatives (Equivalence (≡)) = nubBy (≡) asList

eq' ∷ (Finite a) ⇒ Equivalence a → a → a → Bool
eq' = ((==) `on`) . representative

-- TODO deleteme
instance (Show a, Finite a) ⇒ Show (Equivalence a) where
  show equivalence = show (fmap NE.toList (fromEquivalence equivalence))
  {-
                     unlines (fmap show' graph)
               where domain          = liftA2 (,) asList asList
                     graph           = fmap (\(a, y) → (a, y, (getEquivalence equivalence) a y)) domain
                     show' (a, b, c) = show a ++ ", " ++ show b ++ " ↦ " ++ show c
                     -}

-- TODO probably going to be lots of room for optimization in these instance defs, but for now I want to focus on correctness
instance (Finite a) ⇒                                         Eq      (Equivalence a) where
  (==) ∷ Equivalence a → Equivalence a → Bool
  (Equivalence f) == (Equivalence g) = all (\(x, y) → f x y == g x y) (asSet × asSet)
-- N.B. this is just one possible implementation
instance (Eq a) ⇒                                             Bounded (Equivalence a) where
  -- One big equivalence class (the coarsest, i.e. the universal relation: {(x, y) | x, y ∈ U})
  minBound = Equivalence (const (const True))
  -- Each element is it's own equivalence class (the finest, i.e. the identity relation: {(x, x) | x ∈ U})
  -- N.B. `Equivalence (const (const False))` would violate reflexivity
  maxBound = defaultEquivalence
instance (Finite a) ⇒                                         Ord     (Equivalence a) where
  compare ∷ Equivalence a → Equivalence a → Ordering
  compare (Equivalence f) (Equivalence g) = undefined -- FIXME want to ensure this is consistent with Enum and Finite ordering
  -- mconcat (fmap (\(x, y) → f x y `compare` g x y) (liftA2 (,) asList asList))
instance (Finite a) ⇒                                         Enum    (Equivalence a) where
  toEnum   ∷ Int         → Equivalence a
  toEnum     =                       (asList !!)
  fromEnum ∷ Equivalence a → Int
  fromEnum t = fromJust (elemIndex t  asList)
  enumFrom ∷ Equivalence a → [Equivalence a]
  enumFrom t = dropWhile (≠ t)        asList
instance (Finite a) ⇒                                         Finite  (Equivalence a) where
  asList ∷ [Equivalence a]
  asList = fmap toEquivalence (partitions' asList)

data Alpha = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z deriving (Eq, Ord, Enum, Bounded, Show, Read)
instance                                                       Finite Alpha where
  asList = [A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z]

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
