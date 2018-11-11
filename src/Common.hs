{-# LANGUAGE UnicodeSyntax             #-}

module Common where

import           Data.Maybe as Maybe
import           Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Set.Unicode
import           Data.List as List
import           Data.Foldable as Foldable
import           Control.Monad
import           Numeric.Natural

-- TODO deleteme after this is closed: https://github.com/roelvandijk/base-unicode-symbols/issues/18
type ℕ = Natural

-- type level flip
newtype Flip t b a = Flip { unFlip ∷ t a b }

newtype   Algebra f t =   Algebra (f t →   t)
newtype CoAlgebra f t = CoAlgebra (  t → f t)

newtype Fix f = Fix (f (Fix f))

unFix ∷ Fix f → f (Fix f)
unFix (Fix x) = x

-- Catamorphism
cata ∷ Functor f ⇒ Algebra f a → Fix f → a
cata (Algebra alg) = alg . fmap (cata (Algebra alg)) . unFix

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

-- https://mail.haskell.org/pipermail/libraries/2016-January/026565.html
-- Boolean implication.
infix 4 `implies` 
implies ∷ Bool → Bool → Bool
implies True  b = b
implies False _ = True

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

-- Something like free monoid. Lazily generate all possible finite sequences over the given alphabet.
freeMonoid ∷ [a] → [[a]]
freeMonoid []       = [[]]
freeMonoid alphabet = concatMap (`replicateM` alphabet) [0..]

-- FIXME test, comment etc.
freeMonoidFrom ∷ ℕ → [s] → [[s]]
freeMonoidFrom 0 = freeMonoid
freeMonoidFrom n = ([n..] >>=) . flip (replicateM . fromIntegral)

-- Something like free semigroup over the given alphabet
freeSemigroup ∷ [a] → [[a]]
freeSemigroup = freeMonoidFrom 1

-- A version of List.findIndex which returns `Maybe ℕ` instead of `Maybe Int`
findIndex' ∷ (a → Bool) → [a] → Maybe ℕ
findIndex' p xs = fmap fromIntegral (List.findIndex p xs)

indexed ∷ [a] → [(a, ℕ)]
indexed = indexed' 0 -- To use an index starting at 1, change this `0` to `1`
    where indexed' _ []       = []
          indexed' n (x : xs) = (x, n) : indexed' (n + 1) xs

-- impossible ∷ forall (r ∷ RuntimeRep). forall (a ∷ TYPE r). HasCallStack ⇒ [Char] → a
impossible = error "Why, sometimes I've believed as many as six impossible things before breakfast."

hom ∷ (Monoid m) ⇒ (a → m) → [a] → m
hom f = mconcat . fmap f

-- Prepend and append quotation marks to a given `String`.
quotations ∷ String → String
quotations = ("\"" ++) . (++ "\"")

-- DFA q s → [((q, s), q)]
format ∷ (Show c, Show r) ⇒ Map c r → String
format m = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines. -- FIXME make portable
           (mapWithKey (\k v → "  δ " ++ show k ++ " ↦ " ++ show v) m)

format' ∷ (Show c, Show r) ⇒ Map c (Set r) → String
format' = go -- .  Map.filter (not . Set.null)
    where go m | Map.null m = "  δ _ ↦ ∅"
          go m              = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines. -- FIXME make portable
                              (mapWithKey (\k v → "  δ " ++ show k ++ " ↦ " ++ show (Set' v)) m)

format'' ∷ (Show q, Show s, Show r) ⇒ Map (q, Maybe s) (Set r) → String
format'' = go -- .  Map.filter (not . Set.null)
    where go m | Map.null m = "  δ _ ↦ ∅"
          go m              = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines. -- FIXME make portable
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

upToLength ∷ ℕ → [[l]] → [[l]]
upToLength n = takeWhile ((< n) . genericLength)

interleave ∷ [[a]] → [a]
interleave = concat . transpose

-- from https://github.com/haskell/containers/issues/346
catMaybes ∷ Ord a ⇒ Set (Maybe a) → Set a
catMaybes = Set.mapMonotonic fromJust . Set.dropWhileAntitone isNothing

invert ∷ (Ord k, Ord v) ⇒ Map k v → Map v (Set k)
invert = foldlWithKey (\acc k v → insertWith (∪) v (Set.singleton k) acc) Map.empty

flattenKeys ∷ (Ord k, Ord v, Foldable t) ⇒ Map (t k) v → Map k (Set v)
flattenKeys = foldlWithKey (\acc keys v → Map.unionsWith Set.union (acc : fmap (`Map.singleton` Set.singleton v) (Foldable.toList keys))) Map.empty

invertBijection ∷ (Ord k, Ord v) ⇒ Map k v → Map v k
invertBijection = foldrWithKey (flip Map.insert) Map.empty

palindrome ∷ (Eq a) ⇒ [a] → Bool
palindrome w = w == reverse w

newtype Set' a = Set' { unSet' ∷ Set a }

instance (Show a) ⇒ Show (Set' a) where
  show = ("{" ++) . (++ "}") . intercalate ", " . (show <$>) . Set.toList . unSet'
