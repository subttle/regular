{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ConstraintKinds            #-}

module Common where

import           Data.Maybe as Maybe
import           Data.Map as Map (Map, null, empty, unionsWith, singleton, insert, mapWithKey, foldlWithKey, insertWith, foldrWithKey)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Set.Unicode ((∪))
import           Data.Bool.Unicode ((∧))
import           Data.Ord.Unicode ((≤))
import           Data.Eq.Unicode ((≠))
import           Data.List as List
import           Data.List.NonEmpty (NonEmpty, NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NE
import           Data.These
import qualified Data.Type.Nat as Nat
import           Data.Fin (Fin)
import           Data.Char (digitToInt)
import           Data.Either (lefts, rights, partitionEithers, fromLeft, fromRight, isLeft, isRight)
import           Data.Foldable as Foldable
import           Data.Functor.Contravariant.Divisible (Divisible, Decidable, divide, conquer, choose, lose)
import           Data.Functor.Contravariant (Contravariant, Op (..), Predicate (..), Comparison (..), Equivalence (..), defaultComparison, defaultEquivalence, contramap, (>$<), (>$$<))
import           Data.Functor.Foldable (Fix (..), unfix, ListF (..))
import           Data.Function (on)
import           Data.Void
import           Control.Applicative (liftA2, getZipList, ZipList (..))
import           Control.Monad (replicateM)
import           Control.Arrow ((|||), (&&&))
import           Numeric.Natural.Unicode (ℕ)

-- type level flip
newtype Flip t b a = Flip { unFlip ∷ t a b }

newtype    Algebra f t =    Algebra (f         t  →                   t)
newtype  CoAlgebra f t =  CoAlgebra (          t  → f                 t)
newtype   RAlgebra f t =   RAlgebra (f (Fix f, t) →                   t)
newtype RCoAlgebra f t = RCoAlgebra (          t  → f (Either (Fix f) t))
-- Mendler-style
newtype   MAlgebra f t =   MAlgebra (∀ a. (a → t) → (f a → t))

-- Mendler-style Catamorphism
mcata ∷ MAlgebra f c → Fix f → c
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

(⋄) ∷ (Semigroup m) ⇒ m → m → m
(⋄) = (<>)

-- TODO precedence
(…) ∷ (c → d) → (a → b → c) → a → (b → d)
(…) = (.) . (.)

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

(≰) ∷ (Ord a) ⇒ a → a → Bool
(≰) = not … (≤)

while ∷ (a → Bool) → (a → a) → a → a
while p = until (not . p)

comparing' ∷ (Ord b) ⇒ (a → b) → Comparison a
comparing' = (>$$<) defaultComparison

-- ⭀
equating' ∷ (Eq b) ⇒ (a → b) → Equivalence a
equating' = (>$$<) defaultEquivalence

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
intersects = not … Set.disjoint

-- A version of `Set.size` which returns a `ℕ` instead of `Int`
size' ∷ Set a → ℕ
size' = fromIntegral . Set.size

-- Given an endofunction, `f`, and a starting point,
-- `a`, iterate `f` until two in a row are equal.
-- Attempts to find the first fixed point not necessarily the least.
fixedPoint ∷ (Eq a) ⇒ (a → a) → a → a
fixedPoint f a | f a == a = a
fixedPoint f a            = fixedPoint f (f a)

-- pretty mind blowing but subtle observation: Church Nat has type: `∀ a . (a → a) → a → a`
fixedPoint' ∷ Equivalence a → (a → a) → a → a
fixedPoint' (Equivalence (≡)) f a | f a ≡ a = a
fixedPoint' (Equivalence (≡)) f a           = fixedPoint' (Equivalence (≡)) f (f a)

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

toThese   ∷ Either (a, b) (Either a b) → These a b
toThese   (Left  (a, b)  )             = These a b
toThese   (Right (Right b))            = That    b
toThese   (Right (Left  a))            = This  a

fromThese ∷ These a b                  → Either (a, b) (Either a b)
fromThese (These a b)                  = Left  (a, b)
fromThese (That    b)                  = Right (Right b)
fromThese (This  a  )                  = Right (Left  a)

-- Equivalence ((==) `on` (not . (==) GT))
lteq ∷ Equivalence Ordering
lteq = equating' (≠ GT)

-- Equivalence ((==) `on` (not . (==) LT))
gteq ∷ Equivalence Ordering
gteq = equating' (≠ LT)

-- case analysis for `Ordering` type
ordering ∷ a → a → a → Ordering → a
ordering lt _  _  LT = lt
ordering _  eq _  EQ = eq
ordering _  _  gt GT = gt

partitionWith ∷ (a → Either b c) → [a] → ([b], [c])
partitionWith  = partitionEithers … fmap

partitionWith' ∷ (a → These b c) → [a] → ([b], [c], [(b, c)])
partitionWith' = partitionThese   … fmap

unzipWith ∷ (a → (b, c)) → [a] → ([b], [c])
unzipWith      = unzip            … fmap

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
partitions ∷ [a] → [[NonEmpty a]]
partitions []      = [[]]
partitions (h : t) = partitionsNE (h :| t)

partitionsNE ∷ NonEmpty a → [[NonEmpty a]]
partitionsNE (a₁ :| [])        = [[ a₁ :| []]]
partitionsNE (a₁ :| (a₂ : as)) = [((a₁ :| []) :), \(h : t) → (a₁ <| h) : t] <*> partitionsNE (a₂ :| as)

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

-- https://oeis.org/A000108
-- Catalan numbers
catalan ∷ NonEmpty ℕ
catalan = 1 <| NE.unfoldr c (1 :| [])
  where
    c ∷ NonEmpty ℕ → (ℕ, Maybe (NonEmpty ℕ))
    c ns = (n, Just (n <| ns))
      where
        n ∷ ℕ
        n = sum (NE.zipWith (*) ns (NE.reverse ns))

-- Natural numbers
naturals ∷ NonEmpty ℕ
naturals = NE.iterate (+1) 0

factorial ∷ ℕ → ℕ
factorial = product . enumFromTo 1

-- Bell number
-- Count the possible partitions of a set of the given cardinality
-- bell ∷ ℕ → ℕ
-- bell n = sum (fmap (\k → stirling₂ (n, k)) [0 .. n])
bell ∷ ℕ → ℕ
bell n = NE.head (applyN n (\ns → NE.scanl1 (+) (NE.last ns :| Foldable.toList ns)) (1 :| []))

-- Apply a function `n` times
applyN ∷ ℕ → (a → a) → a → a
applyN = Foldable.foldr (.) id … genericReplicate

length' ∷ NonEmpty a → ℕ
length' = fromIntegral . NE.length

-- A version of List.findIndex which returns `Maybe ℕ` instead of `Maybe Int`
findIndex' ∷ (a → Bool) → [a] → Maybe ℕ
findIndex' = fmap fromIntegral … List.findIndex

findIndices' ∷ (a → Bool) → [a] → [ℕ]
findIndices' = fmap fromIntegral … List.findIndices

elemIndex' ∷ (Eq a) ⇒ a → [a] → Maybe ℕ
elemIndex' = fmap fromIntegral … List.elemIndex

elemIndices' ∷ (Eq a) ⇒ a → [a] → [ℕ]
elemIndices' = fmap fromIntegral … List.elemIndices

-- A wrapper for `deleteBy` which uses `Equivalence` type.
deleteBy' ∷ (Foldable f) ⇒ Equivalence a → a → f a → [a]
deleteBy' (Equivalence (≡)) a = deleteBy (≡) a . toList

-- A wrapper for `intersectBy` which uses `Equivalence` type.
intersectBy' ∷ (Foldable f) ⇒ Equivalence a → f a → f a → [a]
intersectBy' (Equivalence (≡)) = intersectBy (≡) `on` toList

-- A wrapper for `deleteFirstsBy` which uses `Equivalence` type.
deleteFirstsBy' ∷ (Foldable f) ⇒ Equivalence a → f a → f a → [a]
deleteFirstsBy' (Equivalence (≡)) = deleteFirstsBy (≡) `on` toList

-- Intuitively this is just like `elem` from `Data.List` but with
-- user supplied equivalence relation.
elemBy ∷ (Foldable f) ⇒ Equivalence a → a → f a → Bool
elemBy (Equivalence (≡)) = any . (≡)

-- A wrapper for `sortBy` which uses `Comparison` type.
sortBy' ∷ Comparison a → [a] → [a]
sortBy' (Comparison cmp) = sortBy cmp

-- A wrapper for `minimumBy` which uses `Comparison` type. -- FIXME: should be `Foldable1`
minimumBy' ∷ (Foldable t) ⇒ Comparison a → t a → a
minimumBy' (Comparison cmp) = Foldable.minimumBy cmp

-- A wrapper for `maximumBy` which uses `Comparison` type. -- FIXME: should be `Foldable1`
maximumBy' ∷ (Foldable t) ⇒ Comparison a → t a → a
maximumBy' (Comparison cmp) = Foldable.maximumBy cmp

-- A version of `fromEnum` which returns a Natural rather than an `Int`
fromEnum' ∷ (Enum a) ⇒ a → ℕ
fromEnum' = fromIntegral . fromEnum

indexed ∷ (Traversable t) ⇒ t a → t (a, ℕ)
indexed = mapWithIndex (flip (,))

skeleton ∷ (Traversable t) ⇒ t a → t ℕ
skeleton = mapWithIndex const

mapWithIndex ∷ (Traversable t) ⇒ (ℕ → a → b) → t a → t b
mapWithIndex f = snd . mapAccumL (((.) . (,) . (1 +)) <*> f) 0

-- If using this, may want to consider using uniform-pair
-- https://github.com/conal/uniform-pair
both ∷ (a → b) → (a, a) → (b, b)
both f (a₁, a₂) = (f a₁, f a₂)

-- impossible ∷ ∀ (r ∷ RuntimeRep). ∀ (a ∷ TYPE r). HasCallStack ⇒ [Char] → a
impossible ∷ a
impossible = error "Why, sometimes I've believed as many as six impossible things before breakfast."

hom ∷ (Monoid m) ⇒ (a → m) → [a] → m
hom = mconcat … fmap

-- Prepend and append quotation marks to a given `String`.
quotations ∷ String → String
quotations = ("\"" ++) . (++ "\"")

-- DFA q s → [((q, s), q)]
format ∷ (Show c, Show r) ⇒ Map c r → String
format m = foldl1 (\a b → a ++ "\n" ++ b)  -- manually intercalate the Map with newlines.
           (mapWithKey (\k v → "  δ " ++ show k ++ " ↦ " ++ show v) m)

format' ∷ ∀ c r . (Show c, Show r) ⇒ Map c (Set r) → String
format' = go -- .  Map.filter (not . Set.null)
  where
    go ∷ Map c (Set r) → String
    go m | Map.null m = "  δ _ ↦ ∅"
    go m              = foldl1 (\a b → a ++ "\n" ++ b)  -- manually intercalate the Map with newlines.
                        (mapWithKey (\k v → "  δ " ++ show k ++ " ↦ " ++ show (Set' v)) m)

format'' ∷ ∀ q s r . (Show q, Show s, Show r) ⇒ Map (q, Maybe s) (Set r) → String
format'' = go -- .  Map.filter (not . Set.null)
  where
    go ∷ Map (q, Maybe s) (Set r) → String
    go m | Map.null m = "  δ _ ↦ ∅"
    go m              = foldl1 (\a b → a ++ "\n" ++ b )  -- manually intercalate the Map with newlines.
                        (mapWithKey (\k v → "  δ " ++ show'' k ++ " ↦ " ++ show (Set' v)) m)
    show'' ∷ (q, Maybe s) → String
    show'' (q, Just  σ) = "(" ++ show q ++ "," ++ show σ ++ ")"
    show'' (q, Nothing) = "(" ++ show q ++ ",ε)"

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

-- Slide a two-element-wide window over a list, one element at a time,
-- generating a list of pairs
windowed' ∷ ∀ t a . (Foldable t) ⇒ t a → [(a, a)]
windowed' = List.unfoldr pairs . Foldable.toList
  where
    pairs ∷ [a] → Maybe ((a, a), [a])
    pairs []            = Nothing
    pairs [_]           = Nothing
    pairs (a₁ : a₂ : t) = Just ((a₁, a₂), a₂ : t)

-- from https://github.com/haskell/containers/issues/346
catMaybes ∷ (Ord a) ⇒ Set (Maybe a) → Set a
catMaybes = Set.mapMonotonic fromJust . Set.dropWhileAntitone isNothing

invertMap ∷ (Ord k, Ord v) ⇒ Map k v → Map v (Set k)
invertMap = foldlWithKey (\acc k v → insertWith (∪) v (Set.singleton k) acc) Map.empty

flattenKeys ∷ (Ord k, Ord v, Foldable t) ⇒ Map (t k) v → Map k (Set v)
flattenKeys = foldlWithKey (\acc k v → Map.unionsWith Set.union (acc : fmap (`Map.singleton` Set.singleton v) (Foldable.toList k))) Map.empty

invertBijection ∷ (Ord k, Ord v) ⇒ Map k v → Map v k
invertBijection = foldrWithKey (flip Map.insert) Map.empty

palindrome ∷ (Eq a) ⇒ [a] → Bool
palindrome w = w == reverse w

newtype Set' a = Set' { unSet' ∷ Set a }

instance (Show a) ⇒ Show (Set' a) where
  show ∷ Set' a → String
  show = ("{" ++) . (++ "}") . intercalate ", " . (show <$>) . Set.toList . unSet'

-- Perhaps improving clarity in some spots
charToString ∷ Char → String
charToString = (: [])

-- TODO change `Black'` to `Black`, `Red'` to `Red` after resolving naming conflict
data DisplayColor where
  Black'  ∷ DisplayColor
  Red'    ∷ DisplayColor
  Green   ∷ DisplayColor
  Yellow  ∷ DisplayColor
  Blue    ∷ DisplayColor
  Magenta ∷ DisplayColor
  Cyan    ∷ DisplayColor
  White   ∷ DisplayColor
  deriving (Eq, Bounded, Enum, Show)

toColor ∷ String → DisplayColor → String
toColor string color = (fgcolor color ++) ((++ reset) string)
  where
    encode ∷ [Int] → String
    encode = ("\ESC[" ++) . (++ "m") . List.intercalate ";" . fmap show
    reset ∷ String
    reset = encode [0]
    -- `30  + _` for normal
    -- `90  + _` for bright
    fgcolor ∷ DisplayColor → String
    fgcolor color' = encode [30 + fromEnum color']
    -- -- `40  + _` for normal
    -- -- `100 + _` for bright
    -- bgcolor ∷ DisplayColor → String
    -- bgcolor color' = encode [40 + fromEnum color']
    -- colorToCode ∷ DisplayColor → Int
    -- colorToCode = fromEnum

class (Show a) ⇒ Fancy a where
  -- assign a unicode character
  unicode  ∷ a → Char
  -- assign an alternative unicode character
  unicode' ∷ a → Char
  unicode' = unicode
  -- the plain version
  plain    ∷ a → String
  show'    ∷ a → String
  show'    = charToString . unicode
  colored ∷ (a, DisplayColor) → String
  colored (s, color) = show' s `toColor` color

class (Divisible f) ⇒ Divisible₃ f where
  divide₃ ∷ (a → (b, c, d)) → f b → f c → f d → f a

class (Divisible f) ⇒ Divisible₄ f where
  divide₄ ∷ (a → (b, c, d, e)) → f b → f c → f d → f e → f a

class (Divisible f) ⇒ Divisible₅ f where
  divide₅ ∷ (a → (b, c, d, e, g)) → f b → f c → f d → f e → f g → f a

class (Divisible f) ⇒ Divisible₆ f where
  divide₆ ∷ (a → (b, c, d, e, g, h)) → f b → f c → f d → f e → f g → f h → f a

-- Non-unicode aliases for convenience
type Divisible3 = Divisible₃
type Divisible4 = Divisible₄
type Divisible5 = Divisible₅
type Divisible6 = Divisible₆
divide3 ∷ (Divisible₃ f) ⇒ (a → (b, c, d)) → f b → f c → f d → f a
divide3 = divide₃
divide4 ∷ (Divisible₄ f) ⇒ (a → (b, c, d, e)) → f b → f c → f d → f e → f a
divide4 = divide₄
divide5 ∷ (Divisible₅ f) ⇒ (a → (b, c, d, e, g)) → f b → f c → f d → f e → f g → f a
divide5 = divide₅
divide6 ∷ (Divisible₆ f) ⇒ (a → (b, c, d, e, g, h)) → f b → f c → f d → f e → f g → f h → f a
divide6 = divide₆

-- TODO change the name :)
class (Decidable f) ⇒ RenameMe f where
  renameme ∷ (a → These b c) → f b → f c → f a

renamed ∷ (RenameMe f) ⇒ f b → f c → f (These b c)
renamed = renameme id

renamedThese ∷ (RenameMe f) ⇒ f a → f a → f a
renamedThese = renameme (\s → These s s)

renamedThis ∷ (RenameMe f) ⇒ f a → f a → f a
renamedThis = renameme This

renamedThat ∷ (RenameMe f) ⇒ f a → f a → f a
renamedThat = renameme That

instance (Monoid m) ⇒ RenameMe (Op m) where
  renameme ∷ ∀ a b c . (a → These b c) → Op m b → Op m c → Op m a
  renameme h (Op opᵇ) (Op opᶜ) = h >$< Op (these opᵇ opᶜ (\b c → opᵇ b <> opᶜ c))

instance RenameMe Predicate where
  renameme ∷ (a → These b c) → Predicate b → Predicate c → Predicate a
  renameme h (Predicate pᵇ) (Predicate pᶜ) = h >$< Predicate (these pᵇ pᶜ (\b c → pᵇ b ∧ pᶜ c))

instance RenameMe Equivalence where
  renameme ∷ ∀ a b c . (a → These b c) → Equivalence b → Equivalence c → Equivalence a
  renameme h (Equivalence (⮀)) (Equivalence (⮂)) = h >$< Equivalence (≡)
    where
      (≡) ∷ These b c → These b c → Bool
      (≡) (This  b₁   ) (This  b₂   ) = b₁ ⮀ b₂
      (≡) (That     c₁) (That     c₂) =           c₁ ⮂ c₂
      (≡) (These b₁ c₁) (These b₂ c₂) = b₁ ⮀ b₂ ∧ c₁ ⮂ c₂
      (≡) _             _             = False

instance RenameMe Comparison where
  renameme ∷ ∀ a b c . (a → These b c) → Comparison b → Comparison c → Comparison a
  renameme h (Comparison (⪋)) (Comparison (⪌)) = h >$< Comparison (⪥)
    where
      (⪥) ∷ These b c → These b c → Ordering
      (⪥) (This  b₁   ) (This  b₂   ) = b₁ ⪋ b₂
      (⪥) (This  _    ) (That     _ ) = LT
      (⪥) (This  _    ) (These _  _ ) = LT
      (⪥) (That     _ ) (This  _    ) = GT
      (⪥) (That     c₁) (That     c₂) = c₁ ⪌ c₂
      (⪥) (That     _ ) (These _  _ ) = LT
      (⪥) (These _  _ ) (This  _    ) = GT
      (⪥) (These _  _ ) (That     _ ) = GT
      (⪥) (These b₁ c₁) (These b₂ c₂) = (b₁ ⪋ b₂) <> (c₁ ⪌ c₂)

-- Partial Equivalence Relation
newtype PER a = PER { getPER ∷ a → a → Maybe Bool }
newtype POR a = POR { getPOR ∷ a → a → Maybe Ordering }

-- newtype Op₁ b a = Op₁ { getOp₁ ∷     a → b }
newtype Op₂ b a = Op₂ { getOp₂ ∷ a → a → b }
-- interesting observation:
-- on ∷ (b → b → c) → (a → b) → (a → a → c)
-- or when flipped:
-- flipOn ∷ (a → b) → (b → b → c) → (a → a → c)

equivalenceToPER ∷ Equivalence a → PER a
equivalenceToPER (Equivalence (≡)) = PER (\a₁ a₂ → Just (a₁ ≡ a₂))

comparisonToPOR ∷ Comparison a → POR a
comparisonToPOR (Comparison c) = POR (\a₁ a₂ → Just (a₁ `c` a₂))

instance Contravariant PER where
  contramap ∷ (a → b) → PER b → PER a
  contramap h (PER p) = PER (p `on` h)

instance Contravariant POR where
  contramap ∷ (a → b) → POR b → POR a
  contramap h (POR p) = POR (p `on` h)

instance Contravariant (Op₂ c) where
  contramap ∷ (a → b) → Op₂ c b → Op₂ c a
  contramap h (Op₂ oᵇ) = Op₂ (oᵇ `on` h)

-- FIXME: warning, this is still experimental
instance (Monoid m) ⇒ Divisible (Op₂ m) where
  divide ∷ ∀ a b c . (a → (b, c)) → Op₂ m b → Op₂ m c → Op₂ m a
  divide h (Op₂ opᵇ) (Op₂ opᶜ) = Op₂ ((\(b₁, c₁) (b₂, c₂) → opᵇ b₁ b₂ <> opᶜ c₁ c₂) `on` h) -- TODO consider reverse order , i.e. `opᶜ c₁ c₂ <> opᵇ b₁ b₂`
  conquer ∷ Op₂ m a
  conquer = Op₂ (const (const mempty))

instance (Monoid m) ⇒ Decidable (Op₂ m) where
  choose ∷ ∀ a b c . (a → Either b c) → Op₂ m b → Op₂ m c → Op₂ m a
  choose h (Op₂ opᵇ) (Op₂ opᶜ) = Op₂ (opᵇᶜ `on` h)
    where
      opᵇᶜ ∷ Either b c → Either b c → m
      opᵇᶜ (Left  b₁) (Left  b₂) = opᵇ b₁ b₂
      opᵇᶜ (Left  _ ) (Right _ ) = mempty
      opᵇᶜ (Right _ ) (Left  _ ) = mempty
      opᵇᶜ (Right c₁) (Right c₂) = opᶜ c₁ c₂
  lose ∷ (a → Void) → Op₂ m a
  lose h = Op₂ (absurd `on` h)

instance (Monoid m) ⇒ RenameMe (Op₂ m) where
  renameme ∷ ∀ a b c . (a → These b c) → Op₂ m b → Op₂ m c → Op₂ m a
  renameme h (Op₂ opᵇ) (Op₂ opᶜ) = Op₂ (opᵇᶜ `on` h)
    where
      opᵇᶜ ∷ These b c → These b c → m
      opᵇᶜ (This  b₁   ) (This  b₂   ) = opᵇ b₁ b₂
      opᵇᶜ (That     c₁) (That     c₂) =              opᶜ c₁ c₂
      opᵇᶜ (These b₁ c₁) (These b₂ c₂) = opᵇ b₁ b₂ <> opᶜ c₁ c₂ -- TODO consider reverse order
      opᵇᶜ _             _             = mempty
      {-
      -- TODO compare with above
      opᵇᶜ ∷ These b c → These b c → m
      opᵇᶜ (This  b₁   ) (This  b₂   ) = opᵇ b₁ b₂
      opᵇᶜ (This  _    ) (That     _ ) = mempty
      opᵇᶜ (This  b₁   ) (These b₂ _ ) = opᵇ b₁ b₂
      opᵇᶜ (That     _ ) (This  _    ) = mempty
      opᵇᶜ (That     c₁) (That     c₂) =             opᶜ c₁ c₂
      opᵇᶜ (That     c₁) (These _  c₂) =             opᶜ c₁ c₂
      opᵇᶜ (These b₁ _ ) (This  b₂   ) = opᵇ b₁ b₂
      opᵇᶜ (These _  c₁) (That     c₂) =             opᶜ c₁ c₂
      opᵇᶜ (These b₁ c₁) (These b₂ c₂) = opᵇ b₁ b₂ ⋄ opᶜ c₁ c₂ -- TODO consider reverse order as above
      -}

-- FIXME need to make sure associativity of `(∧)` matches the correct order here
-- FIXME so as to preserve laziness correctly
-- TODO it may be better to generalize all these so they all just take use `(⋄)`?
instance Divisible₃ Predicate where
  divide₃ ∷ ∀ a b c d . (a → (b, c, d)) → Predicate b → Predicate c → Predicate d → Predicate a
  divide₃ h (Predicate pᵇ) (Predicate pᶜ) (Predicate pᵈ) = Predicate (pᵇᶜᵈ . h)
    where
      pᵇᶜᵈ ∷ (b, c, d) → Bool
      pᵇᶜᵈ   (b, c, d) = pᵇ b
                       ∧ pᶜ c
                       ∧ pᵈ d

instance Divisible₄ Predicate where
  divide₄ ∷ ∀ a b c d e . (a → (b, c, d, e)) → Predicate b → Predicate c → Predicate d → Predicate e → Predicate a
  divide₄ h (Predicate pᵇ) (Predicate pᶜ) (Predicate pᵈ) (Predicate pᵉ) = Predicate (pᵇᶜᵈᵉ . h)
    where
      pᵇᶜᵈᵉ ∷ (b, c, d, e) → Bool
      pᵇᶜᵈᵉ   (b, c, d, e) = pᵇ b
                           ∧ pᶜ c
                           ∧ pᵈ d
                           ∧ pᵉ e

instance Divisible₅ Predicate where
  divide₅ ∷ ∀ a b c d e f . (a → (b, c, d, e, f)) → Predicate b → Predicate c → Predicate d → Predicate e → Predicate f → Predicate a
  divide₅ h (Predicate pᵇ) (Predicate pᶜ) (Predicate pᵈ) (Predicate pᵉ) (Predicate pᶠ) = Predicate (pᵇᶜᵈᵉᶠ . h)
    where
      pᵇᶜᵈᵉᶠ ∷ (b, c, d, e, f) → Bool
      pᵇᶜᵈᵉᶠ   (b, c, d, e, f) = pᵇ b
                               ∧ pᶜ c
                               ∧ pᵈ d
                               ∧ pᵉ e
                               ∧ pᶠ f

instance Divisible₆ Predicate where
  divide₆ ∷ ∀ a b c d e f g . (a → (b, c, d, e, f, g)) → Predicate b → Predicate c → Predicate d → Predicate e → Predicate f → Predicate g → Predicate a
  divide₆ h (Predicate pᵇ) (Predicate pᶜ) (Predicate pᵈ) (Predicate pᵉ) (Predicate pᶠ) (Predicate pᵍ) = Predicate (pᵇᶜᵈᵉᶠᵍ . h)
    where
      pᵇᶜᵈᵉᶠᵍ ∷ (b, c, d, e, f, g) → Bool
      pᵇᶜᵈᵉᶠᵍ   (b, c, d, e, f, g) = pᵇ b
                                   ∧ pᶜ c
                                   ∧ pᵈ d
                                   ∧ pᵉ e
                                   ∧ pᶠ f
                                   ∧ pᵍ g

instance Divisible₃ Equivalence where
  divide₃ ∷ ∀ a b c d . (a → (b, c, d)) → Equivalence b → Equivalence c → Equivalence d → Equivalence a
  divide₃ h (Equivalence eqᵇ) (Equivalence eqᶜ) (Equivalence eqᵈ) = Equivalence (eqᵇᶜᵈ `on` h)
    where
      eqᵇᶜᵈ ∷ (b, c, d) → (b, c, d) → Bool
      eqᵇᶜᵈ (b₁, c₁, d₁) (b₂, c₂, d₂) = eqᵇ b₁ b₂
                                      ∧ eqᶜ c₁ c₂
                                      ∧ eqᵈ d₁ d₂

instance Divisible₄ Equivalence where
  divide₄ ∷ ∀ a b c d e . (a → (b, c, d, e)) → Equivalence b → Equivalence c → Equivalence d → Equivalence e → Equivalence a
  divide₄ h (Equivalence eqᵇ) (Equivalence eqᶜ) (Equivalence eqᵈ) (Equivalence eqᵉ) = Equivalence (eqᵇᶜᵈᵉ `on` h)
    where
      eqᵇᶜᵈᵉ ∷ (b, c, d, e) → (b, c, d, e) → Bool
      eqᵇᶜᵈᵉ (b₁, c₁, d₁, e₁) (b₂, c₂, d₂, e₂) = eqᵇ b₁ b₂
                                               ∧ eqᶜ c₁ c₂
                                               ∧ eqᵈ d₁ d₂
                                               ∧ eqᵉ e₁ e₂

instance Divisible₅ Equivalence where
  divide₅ ∷ ∀ a b c d e f . (a → (b, c, d, e, f)) → Equivalence b → Equivalence c → Equivalence d → Equivalence e → Equivalence f → Equivalence a
  divide₅ h (Equivalence eqᵇ) (Equivalence eqᶜ) (Equivalence eqᵈ) (Equivalence eqᵉ) (Equivalence eqᶠ) = Equivalence (eqᵇᶜᵈᵉᶠ `on` h)
    where
      eqᵇᶜᵈᵉᶠ ∷ (b, c, d, e, f) → (b, c, d, e, f) → Bool
      eqᵇᶜᵈᵉᶠ (b₁, c₁, d₁, e₁, f₁) (b₂, c₂, d₂, e₂, f₂) = eqᵇ b₁ b₂
                                                        ∧ eqᶜ c₁ c₂
                                                        ∧ eqᵈ d₁ d₂
                                                        ∧ eqᵉ e₁ e₂
                                                        ∧ eqᶠ f₁ f₂

instance Divisible₆ Equivalence where
  divide₆ ∷ ∀ a b c d e f g . (a → (b, c, d, e, f, g)) → Equivalence b → Equivalence c → Equivalence d → Equivalence e → Equivalence f → Equivalence g → Equivalence a
  divide₆ h (Equivalence eqᵇ) (Equivalence eqᶜ) (Equivalence eqᵈ) (Equivalence eqᵉ) (Equivalence eqᶠ) (Equivalence eqᵍ) = Equivalence (eqᵇᶜᵈᵉᶠᵍ `on` h)
    where
      eqᵇᶜᵈᵉᶠᵍ ∷ (b, c, d, e, f, g) → (b, c, d, e, f, g) → Bool
      eqᵇᶜᵈᵉᶠᵍ (b₁, c₁, d₁, e₁, f₁, g₁) (b₂, c₂, d₂, e₂, f₂, g₂) = eqᵇ b₁ b₂
                                                                 ∧ eqᶜ c₁ c₂
                                                                 ∧ eqᵈ d₁ d₂
                                                                 ∧ eqᵉ e₁ e₂
                                                                 ∧ eqᶠ f₁ f₂
                                                                 ∧ eqᵍ g₁ g₂

instance Divisible₃ Comparison where
  divide₃ ∷ ∀ a b c d . (a → (b, c, d)) → Comparison b → Comparison c → Comparison d → Comparison a
  divide₃ h (Comparison cmpᵇ) (Comparison cmpᶜ) (Comparison cmpᵈ) = Comparison (cmpᵇᶜᵈ `on` h)
    where
      cmpᵇᶜᵈ ∷ (b, c, d) → (b, c, d) → Ordering
      cmpᵇᶜᵈ (b₁, c₁, d₁) (b₂, c₂, d₂) = cmpᵇ b₁ b₂
                                       ⋄ cmpᶜ c₁ c₂
                                       ⋄ cmpᵈ d₁ d₂

instance Divisible₄ Comparison where
  divide₄ ∷ ∀ a b c d e . (a → (b, c, d, e)) → Comparison b → Comparison c → Comparison d → Comparison e → Comparison a
  divide₄ h (Comparison cmpᵇ) (Comparison cmpᶜ) (Comparison cmpᵈ) (Comparison cmpᵉ) = Comparison (cmpᵇᶜᵈᵉ `on` h)
    where
      cmpᵇᶜᵈᵉ ∷ (b, c, d, e) → (b, c, d, e) → Ordering
      cmpᵇᶜᵈᵉ (b₁, c₁, d₁, e₁) (b₂, c₂, d₂, e₂) = cmpᵇ b₁ b₂
                                                ⋄ cmpᶜ c₁ c₂
                                                ⋄ cmpᵈ d₁ d₂
                                                ⋄ cmpᵉ e₁ e₂

instance Divisible₅ Comparison where
  divide₅ ∷ ∀ a b c d e f . (a → (b, c, d, e, f)) → Comparison b → Comparison c → Comparison d → Comparison e → Comparison f → Comparison a
  divide₅ h (Comparison cmpᵇ) (Comparison cmpᶜ) (Comparison cmpᵈ) (Comparison cmpᵉ) (Comparison cmpᶠ) = Comparison (cmpᵇᶜᵈᵉᶠ `on` h)
    where
      cmpᵇᶜᵈᵉᶠ ∷ (b, c, d, e, f) → (b, c, d, e, f) → Ordering
      cmpᵇᶜᵈᵉᶠ (b₁, c₁, d₁, e₁, f₁) (b₂, c₂, d₂, e₂, f₂) = cmpᵇ b₁ b₂
                                                         ⋄ cmpᶜ c₁ c₂
                                                         ⋄ cmpᵈ d₁ d₂
                                                         ⋄ cmpᵉ e₁ e₂
                                                         ⋄ cmpᶠ f₁ f₂

instance Divisible₆ Comparison where
  divide₆ ∷ ∀ a b c d e f g . (a → (b, c, d, e, f, g)) → Comparison b → Comparison c → Comparison d → Comparison e → Comparison f → Comparison g → Comparison a
  divide₆ h (Comparison cmpᵇ) (Comparison cmpᶜ) (Comparison cmpᵈ) (Comparison cmpᵉ) (Comparison cmpᶠ) (Comparison cmpᵍ) = Comparison (cmpᵇᶜᵈᵉᶠᵍ `on` h)
    where
      cmpᵇᶜᵈᵉᶠᵍ ∷ (b, c, d, e, f, g) → (b, c, d, e, f, g) → Ordering
      cmpᵇᶜᵈᵉᶠᵍ (b₁, c₁, d₁, e₁, f₁, g₁) (b₂, c₂, d₂, e₂, f₂, g₂) = cmpᵇ b₁ b₂
                                                                  ⋄ cmpᶜ c₁ c₂
                                                                  ⋄ cmpᵈ d₁ d₂
                                                                  ⋄ cmpᵉ e₁ e₂
                                                                  ⋄ cmpᶠ f₁ f₂
                                                                  ⋄ cmpᵍ g₁ g₂
