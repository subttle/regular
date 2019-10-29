{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}

module Common where

import           Data.Maybe as Maybe
import           Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.List as List
import           Data.List.NonEmpty (NonEmpty, NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NE
import qualified Data.Type.Nat as Nat
import           Data.Fin (Fin)
import           Data.Char (digitToInt)
import           Data.Either (lefts, rights, partitionEithers, fromLeft, fromRight, isLeft, isRight)
import           Data.Foldable as Foldable
import           Data.Functor.Foldable (Fix (..), unfix, ListF (..))
import           Control.Applicative (liftA2, getZipList, ZipList (..))
import           Control.Monad
import           Control.Arrow ((|||), (&&&))
import           Numeric.Natural.Unicode

-- type level flip
newtype Flip t b a = Flip { unFlip ∷ t a b }

newtype    Algebra f t =    Algebra (f         t  →                   t)
newtype  CoAlgebra f t =  CoAlgebra (          t  → f                 t)
newtype   RAlgebra f t =   RAlgebra (f (Fix f, t) →                   t)
newtype RCoAlgebra f t = RCoAlgebra (          t  → f (Either (Fix f) t))
-- Mendler-style
newtype   MAlgebra f t =   MAlgebra (∀ a. (a → t) → (f a → t))

-- Mendler-style Catamorphism
mcata :: MAlgebra f c → Fix f → c
mcata (MAlgebra φ) = φ (mcata (MAlgebra φ)) . unfix

-- Catamorphism
cata ∷ (Functor f) ⇒ Algebra f a → Fix f → a
cata (Algebra φ) = φ . fmap (cata (Algebra φ)) . unfix

-- Anamorphism
ana ∷ (Functor f) ⇒ CoAlgebra f a → a → Fix f
ana (CoAlgebra ψ) = Fix . fmap (ana (CoAlgebra ψ)) . ψ

-- Paramorphism
para ∷ (Functor f) ⇒ RAlgebra f a → Fix f → a
para (RAlgebra φ) = φ . fmap (\t → (t, para (RAlgebra φ) t)) . unfix

-- Apomorphism
apo ∷ (Functor f) ⇒ RCoAlgebra f a → a → Fix f
apo (RCoAlgebra ψ) = Fix . fmap (either id (apo (RCoAlgebra ψ))) . ψ

-- Metamorphism (Gibbons')
meta ∷ (Functor f, Functor g) ⇒ Algebra f a → CoAlgebra g b → (a → b) → Fix f → Fix g
meta φ ψ h = ana ψ . h . cata φ

-- Hylomorphism
hylo ∷ (Functor f) ⇒ Algebra f a → CoAlgebra f b → b → a
hylo (Algebra φ) (CoAlgebra ψ) = φ . fmap (hylo (Algebra φ) (CoAlgebra ψ)) . ψ

elgot ∷ (Functor f) ⇒ Algebra f b → (a → Either b (f a)) → a → b
elgot (Algebra φ) ψ = (id ||| φ . fmap (elgot (Algebra φ) ψ)) . ψ                

coelgot ∷ (Functor f) ⇒ ((a, f b) → b) → CoAlgebra f a → a → b
coelgot φ (CoAlgebra ψ) = φ . (id &&& fmap (coelgot φ (CoAlgebra ψ)) . ψ)

andAlg ∷ Algebra (ListF Bool) Bool
andAlg = Algebra φ
  where φ ∷ ListF Bool Bool → Bool
        φ Nil        = True
        φ (Cons x y) = x ∧ y

-- requires containers-0.5.11 or newer
-- TODO deleteme after this is closed: https://github.com/roelvandijk/containers-unicode-symbols/issues/6
(×) ∷ (Ord a, Ord b) ⇒ Set a → Set b → Set (a, b)
(×) = Set.cartesianProduct
{-# INLINE (×) #-}

-- requires containers-0.5.11 or newer
-- TODO deleteme after this is closed: https://github.com/roelvandijk/containers-unicode-symbols/issues/6
(⊎) ∷ Set a → Set b → Set (Either a b)
(⊎) = Set.disjointUnion
{-# INLINE (⊎) #-}

-- TODO something like this for notation? I like that post!
-- https://vynm.github.io/Comutations/posts/2018-05-25-00Introduction.html
infixl 5 <<-
(<<-) ∷ (Ord a) ⇒ a → Set a → Set a
(<<-) = Set.insert

while ∷ (a → Bool) → (a → a) → a → a
while p = until (not . p)

-- Boolean implication.
implies ∷ Bool → Bool → Bool
implies True  = id
implies False = const True

-- exclusive-or
-- The name `xor` is already used by `Data.List.NonEmpty`
xor' ∷ Bool → Bool → Bool
xor' True  = not
xor' False = id

-- Two sets intersect if A ∩ B ≠ ∅
intersects ∷ (Ord a) ⇒ Set a → Set a → Bool
intersects x y = not (Set.disjoint x y)

-- A version of `Set.size` which returns a `ℕ` instead of `Int`
size' ∷ Set a → ℕ
size' = fromIntegral . Set.size

-- Given an endofunction, f, and a starting point,
-- x, iterate f until two in a row are equal.
-- Attempts to find the first fixed point not necessarily the least.
fixedPoint ∷ (Eq a) ⇒ (a → a) → a → a
fixedPoint f x
  | f x == x  = x
  | otherwise = fixedPoint f (f x)

-- `replicateM` with parameter of type ℕ (instead of parameter of type ℤ)
replicateM' ∷ (Applicative m) ⇒ ℕ → m a → m [a]
replicateM' 0 _ = pure []
replicateM' n f = liftA2 (:) f (replicateM' (n - 1) f)

-- Something like free monoid. Lazily generate all possible finite sequences over the given alphabet.
freeMonoid ∷ [a] → [[a]]
freeMonoid []       = [[]]
freeMonoid alphabet = concatMap (`replicateM` alphabet) [0..]

-- FIXME test, comment etc.
freeMonoidFrom ∷ ℕ → [s] → [[s]]
freeMonoidFrom 0 = freeMonoid
freeMonoidFrom n = ([n..] >>=) . flip replicateM'

-- Something like free semigroup over the given alphabet
freeSemigroup ∷ [a] → [[a]]
freeSemigroup = freeMonoidFrom 1

-- A more general version of `partitionEithers` from `Data.Either`
partitionEithers' ∷ (Foldable t) ⇒ t (Either a b) → ([a], [b])
partitionEithers' = partitionEithers . Foldable.toList

-- A more general version of `lefts` from `Data.Either`
lefts' ∷ (Foldable t) ⇒ t (Either a b) → [a]
lefts' = lefts . Foldable.toList

-- A more general version of `rights` from `Data.Either`
rights' ∷ (Foldable t) ⇒ t (Either a b) → [b]
rights' = rights . Foldable.toList

unionLefts ∷ (Ord a) ⇒ Set (Either a b) → Set a
unionLefts  = Set.mapMonotonic (fromLeft  undefined) . Set.filter isRight -- Set.dropWhileAntitone isRight -- TODO can I use `dropWhileAntitone` here to improve efficiency? is ordering needed on `Either a b`?

unionRights ∷ (Ord b) ⇒ Set (Either a b) → Set b
unionRights = Set.mapMonotonic (fromRight undefined) . Set.filter isLeft  -- Set.dropWhileAntitone isLeft -- TODO can I use `dropWhileAntitone` here to improve efficiency? is ordering needed on `Either a b`?

-- partitions of a list
-- partitions [0..2] = [ [[0],[1],[2]]
--                     , [[0],[1,2]]
--                     , [[0,1],[2]]
--                     , [[0,1,2]]
--                     ]
partitions ∷ ∀ a . [a] → [[NonEmpty a]]
partitions []       = [[]]
partitions (x : xs) = go (x :| xs)
      where go ∷ NonEmpty a → [[NonEmpty a]]
            go (a :| [])      = [[a :| []]]
            go (a :| (h : t)) = [((a :| []) :), \(y : z) → (a <| y) : z] <*> go (h :| t)

-- partitions of a set
-- partitions' {0..2} = [ [[2,1,0]]
--                      , [[1,0],[2]]
--                      , [[2,0],[1]]
--                      , [[0],[2,1]]
--                      , [[0],[1],[2]]
--                      ]
partitions' ∷ (Foldable t) ⇒ t a → [[NonEmpty a]]
partitions' = Foldable.foldl (\xs → (xs >>=) . go) [[]]
   where go ∷ a → [NonEmpty a] → [[NonEmpty a]]
         go a []       = [[ a :| [] ]]
         go a (y : ys) = [(a :| Foldable.toList y) : ys] <> fmap (y :) (go a ys)

-- Stirling numbers of the first kind
-- "The Stirling numbers of the first kind s(n, k) count the number of ways to permute a list of `n` items into `k` cycles"
-- http://mathforum.org/advanced/robertd/stirling1.html
stirling₁ ∷ (ℕ, ℕ) → ℕ
stirling₁ (0, 0) = 1
stirling₁ (0, _) = 0
stirling₁ (_, 0) = 0
stirling₁ (n, k) = stirling₁ (n - 1, k - 1) + stirling₁ (n - 1, k) * (n - 1)

-- Stirling numbers of the second kind
-- "The Stirling numbers of the second kind describe the number of ways a set with `n` elements can be partitioned into `k` disjoint, non-empty subsets."
-- http://mathforum.org/advanced/robertd/stirling2.html
-- N.B. requires k ≤ n to ensure each part is nonempty
stirling₂ ∷ (ℕ, ℕ) → ℕ
stirling₂ (0, 0) = 1
stirling₂ (0, _) = 0
stirling₂ (_, 0) = 0
stirling₂ (n, k) = stirling₂ (n - 1, k - 1) + stirling₂ (n - 1, k) * k

-- Bell number
-- Count the possible partitions of a set of the given cardinality
-- bell ∷ ℕ → ℕ
-- bell n = sum (fmap (\k → stirling₂ (n, k)) [0 .. n])
bell ∷ ℕ → ℕ
bell n = NE.head (nth n (\ns → NE.scanl1 (+) (NE.last ns :| Foldable.toList ns)) (1 :| []))

-- Apply a function `n` times
nth ∷ ℕ → (a → a) → a → a
nth n = Foldable.foldr (.) id . genericReplicate n

-- A version of List.findIndex which returns `Maybe ℕ` instead of `Maybe Int`
findIndex' ∷ (a → Bool) → [a] → Maybe ℕ
findIndex' p = fmap fromIntegral . List.findIndex p

indexed ∷ [a] → [(a, ℕ)]
indexed = indexed' 0 -- To use an index starting at 1, change this `0` to `1`
    where indexed' _ []       = []
          indexed' n (x : xs) = (x, n) : indexed' (n + 1) xs

-- impossible ∷ forall (r ∷ RuntimeRep). forall (a ∷ TYPE r). HasCallStack ⇒ [Char] → a
impossible ∷ a
impossible = error "Why, sometimes I've believed as many as six impossible things before breakfast."

hom ∷ (Monoid m) ⇒ (a → m) → [a] → m
hom f = mconcat . fmap f

-- Prepend and append quotation marks to a given `String`.
quotations ∷ String → String
quotations = ("\"" ++) . (++ "\"")

-- DFA q s → [((q, s), q)]
format ∷ (Show c, Show r) ⇒ Map c r → String
format m = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines.
           (mapWithKey (\k v → "  δ " ++ show k ++ " ↦ " ++ show v) m)

format' ∷ (Show c, Show r) ⇒ Map c (Set r) → String
format' = go -- .  Map.filter (not . Set.null)
    where go m | Map.null m = "  δ _ ↦ ∅"
          go m              = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines.
                              (mapWithKey (\k v → "  δ " ++ show k ++ " ↦ " ++ show (Set' v)) m)

format'' ∷ (Show q, Show s, Show r) ⇒ Map (q, Maybe s) (Set r) → String
format'' = go -- .  Map.filter (not . Set.null)
    where go m | Map.null m = "  δ _ ↦ ∅"
          go m              = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines.
                              (mapWithKey (\k v → "  δ " ++ show' k ++ " ↦ " ++ show (Set' v)) m)
          show' (q, Just  σ) = "(" ++ show q ++ "," ++ show σ ++ ")"
          show' (q, Nothing) = "(" ++ show q ++ ",ε)"

-- Some helper functions for nicely displaying languages
toStrings ∷ (Show s) ⇒ [[s]] → [String]
toStrings   = fmap  (>>= show)

toStrings' ∷ (Show s) ⇒ [[Maybe s]] → [String]
toStrings'  = fmap ((>>= show) . Maybe.catMaybes)

toStrings'' ∷ (Show a, Show b) ⇒ [[Either a b]] → [String]
toStrings'' = fmap  (>>= either show show)

-- The type should be `ℕ → [Fin₁₀]` but that alias is defined in Finite.hs which if
-- imported would cause an import cycle, so avoid that by just inlining the type alias
toDigits ∷ ℕ → [Fin ('Nat.S Nat.Nat9)]
toDigits = fmap (toEnum . digitToInt) . show

upToLength ∷ ℕ → [[a]] → [[a]]
upToLength n = takeWhile ((< n) . genericLength)

interleave ∷ [[a]] → [a]
interleave = concat . transpose

-- Sliding window of exactly size n
windowed ∷ (Foldable t) ⇒ ℕ → t a → [[a]]
windowed 0 = const []
windowed n = getZipList . traverse ZipList . genericTake n . tails . Foldable.toList

-- from https://github.com/haskell/containers/issues/346
catMaybes ∷ (Ord a) ⇒ Set (Maybe a) → Set a
catMaybes = Set.mapMonotonic fromJust . Set.dropWhileAntitone isNothing

invert ∷ (Ord k, Ord v) ⇒ Map k v → Map v (Set k)
invert = foldlWithKey (\acc k v → insertWith (∪) v (Set.singleton k) acc) Map.empty

flattenKeys ∷ (Ord k, Ord v, Foldable t) ⇒ Map (t k) v → Map k (Set v)
flattenKeys = foldlWithKey (\acc k v → Map.unionsWith Set.union (acc : fmap (`Map.singleton` Set.singleton v) (Foldable.toList k))) Map.empty

invertBijection ∷ (Ord k, Ord v) ⇒ Map k v → Map v k
invertBijection = foldrWithKey (flip Map.insert) Map.empty

palindrome ∷ (Eq a) ⇒ [a] → Bool
palindrome w = w == reverse w

newtype Set' a = Set' { unSet' ∷ Set a }

instance (Show a) ⇒ Show (Set' a) where
  show = ("{" ++) . (++ "}") . intercalate ", " . (show <$>) . Set.toList . unSet'
