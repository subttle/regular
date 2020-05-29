{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module IntBase where

import           Control.Applicative (empty, (<|>), Alternative)
import           Control.Monad (ap)
import           Data.Functor ((<&>))
import           Data.Functor.Foldable (Fix (..), Recursive, Corecursive, Base, project, embed)
import           Data.Function (on)
import           Data.Group (Group, invert)
import           Data.List (unfoldr)
import           Data.List.NonEmpty (NonEmpty, NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NE
import           GHC.Real (reduce)
import           Common ((‥), ordering)

-- N.B. this entire file is currently experimental/untested/WIP!

data ℤ where
  Prev ∷ ℤ → ℤ
  Zero ∷     ℤ
  Next ∷ ℤ → ℤ

data IntegerF a where
  PrevF ∷ a → IntegerF a
  ZeroF ∷     IntegerF a
  NextF ∷ a → IntegerF a
deriving instance Functor  IntegerF
deriving instance Foldable IntegerF

-- case analysis
int ∷ (a → a) → a → (a → a) → ℤ → a
int prev z next (Prev i) = prev (int prev z next i)
int _    z _     Zero    = z
int prev z next (Next i) = next (int prev z next i)

intf ∷ (a → b) → b → (a → b) → IntegerF a → b
intf prev _ _    (PrevF a) = prev a
intf _    z _     ZeroF    = z
intf _    _ next (NextF a) = next a

instance Num ℤ where
  (+) ∷ ℤ → ℤ → ℤ
  (+)       x   Zero    =             x
  (+)  Zero          y  =                 y
  (+) (Next x) (Next y) = Next (Next (x + y))
  (+) (Prev x) (Prev y) = Prev (Prev (x + y))
  (+) (Next x) (Prev y) =             x + y
  (+) (Prev x) (Next y) =             x + y
  (*) ∷ ℤ → ℤ → ℤ
  (*)       _   Zero    = Zero
  (*)  Zero          _  = Zero
  (*) (Next x) (Next y) = Next (x * y + x + y) -- (x + 1) * (y + 1) = xy + x + y + 1
  (*) (Prev x) (Next y) = Prev (x * y + x - y) -- (x - 1) * (y + 1) = xy + x - y - 1
  (*) (Next x) (Prev y) = Prev (x * y - x + y) -- (x + 1) * (y - 1) = xy - x + y - 1
  (*) (Prev x) (Prev y) = Next (x * y - x - y) -- (x - 1) * (y - 1) = xy - x - y + 1
  (-) ∷ ℤ → ℤ → ℤ
  (-)       x   Zero    =             x
  (-)  Zero          y  =          negate y
  (-) (Next x) (Next y) =             x - y   -- (x + 1) - (y + 1) =  x - y       (monotonicity of addition)
  (-) (Prev x) (Prev y) =             x - y   -- (x - 1) - (y - 1) =  x - y       (monotonicity of subtraction)
  (-) (Next x) (Prev y) = Next (Next (x - y)) -- (x + 1) - (y - 1) = (x - y) + 2
  (-) (Prev x) (Next y) = Prev (Prev (x - y)) -- (x - 1) - (y + 1) = (x - y) - 2
  negate ∷ ℤ → ℤ
  negate = invert
  fromInteger ∷ Integer → ℤ
  fromInteger i | i < 0 = Prev (fromInteger (1 + i    ))
  fromInteger 0         = Zero
  fromInteger i | i > 0 = Next (fromInteger (    i - 1))
  abs ∷ ℤ → ℤ
  abs = undefined    -- FIXME implement
  signum ∷ ℤ → ℤ
  signum = undefined -- FIXME implement

instance Real ℤ where
  toRational ∷ ℤ → Rational
  toRational = (flip reduce `on` toInteger) (Next Zero)
instance Integral ℤ where
  toInteger ∷ ℤ → Integer
  toInteger = int pred 0 succ
  quotRem ∷ ℤ → ℤ → (ℤ, ℤ)
  quotRem = undefined -- FIXME implement

instance Semigroup ℤ where
  (<>) ∷ ℤ → ℤ → ℤ
  (<>) = (+)
instance Monoid ℤ where
  mempty  ∷ ℤ
  mempty  = Zero
instance Group ℤ where
  invert ∷ ℤ → ℤ
  invert = int Next Zero Prev

instance Show ℤ where
  show ∷ ℤ → String
  show = show . toInteger

instance Eq ℤ where
  (==) ∷ ℤ → ℤ → Bool
  (==) = (==) `on` toInteger
instance Ord ℤ where
  compare ∷ ℤ → ℤ → Ordering
  compare = compare `on` toInteger
-- N.B. this is not a bijection!
instance Enum ℤ where
  toEnum ∷ Int → ℤ
  toEnum i | i <  0 = Prev (toEnum (i + 1))
           | i == 0 = Zero
           | i >  0 = Next (toEnum (i - 1))

  fromEnum ∷ ℤ → Int
  fromEnum = int pred 0 succ
  succ ∷ ℤ → ℤ
  succ = Next
  pred ∷ ℤ → ℤ
  pred = Prev

instance Recursive Integer where
  project ∷ Integer → Base Integer Integer
  project i | i <  0 = PrevF (1 + i    )
            | i == 0 = ZeroF
            | i >  0 = NextF (    i - 1)

instance Corecursive Integer where
  embed ∷ Base Integer Integer → Integer
  embed (PrevF i) =     i - 1
  embed  ZeroF    =     0
  embed (NextF i) = 1 + i

type instance Base Integer = IntegerF
-- type Integer' = Fix IntegerF


toOrderings ∷ ℤ → NonEmpty Ordering
toOrderings (Prev i) =      LT <| toOrderings i
toOrderings Zero     = pure EQ
toOrderings (Next i) =      GT <| toOrderings i

toOrdering ∷ ℤ → Ordering
toOrdering = int (const LT) EQ (const GT)

fromOrdering ∷ Ordering → ℤ
fromOrdering = ordering (Prev Zero) Zero (Next Zero)

toBits ∷ ℤ → [Bool]
toBits = unfoldr c
  where
    c ∷ ℤ → Maybe (Bool, ℤ)
    c (Prev i) = Just (False, i)
    c Zero     = Nothing
    c (Next i) = Just (True,  i)

-- TODO better name?
telescope ∷ ℤ → [Either ℤ ℤ]
telescope = unfoldr c
  where
    c ∷ ℤ → Maybe (Either ℤ ℤ, ℤ)
    c (Prev i) = Just (Left  i, i)
    c Zero     = Nothing
    c (Next i) = Just (Right i, i)

{-
-- FIXME untested
-- TODO trying to figure out best way to represent this for fun with transition monoid :)
--
-- TODO https://planetmath.org/freegroup
-}
data FreeGroup a where
  Zer ∷ FreeGroup a
  Neg ∷ a → (FreeGroup a → FreeGroup a)
  Pos ∷ a → (FreeGroup a → FreeGroup a)

-- case analysis
freegroup ∷ b → (a → (b → b)) → (a → (b → b)) → (FreeGroup a → b)
-- freegroup ∷ b → (a → b → b) → (a → b → b) → FreeGroup a → b
freegroup z _ _ Zer        = z
freegroup z n p (Neg a ga) = n a (freegroup z n p ga)
freegroup z n p (Pos a ga) = p a (freegroup z n p ga)

instance (Show a) ⇒ Show (FreeGroup a) where
  -- FIXME best way to show entire thing (symbols, etc)
  show ∷ FreeGroup a → String
  show Zer        = "0"
  show (Neg a ga) = "(-" <> show a <> "TODO" <> ")" -- FIXME
  show (Pos a ga) = "(+" <> show a <> "TODO" <> ")" -- FIXME

instance Semigroup (FreeGroup a) where
  (<>) ∷ FreeGroup a → FreeGroup a → FreeGroup a
  (<>) Zer        r  =             r
  (<>)        l  Zer =        l
  (<>) (Pos a l) r   = Pos a (l <> r)
  (<>) (Neg a l) r   = Neg a (l <> r)
instance Monoid (FreeGroup a) where
  mempty ∷ FreeGroup a
  mempty = Zer
instance Group (FreeGroup a) where
  -- FIXME: untested
  invert ∷ FreeGroup a → FreeGroup a
  invert = freegroup Zer Pos Neg

instance Functor FreeGroup where
  fmap ∷ (a → b) → FreeGroup a → FreeGroup b
  fmap _ Zer        = Zer
  fmap f (Neg a ga) = Neg (f a) (fmap f ga)
  fmap f (Pos a ga) = Pos (f a) (fmap f ga)

instance Foldable FreeGroup where
  -- TODO
  foldMap ∷ (Monoid m) ⇒ (a → m) → FreeGroup a → m
  foldMap _ Zer        = mempty
  foldMap f (Neg a ga) = f a <> foldMap f ga
  foldMap f (Pos a ga) = f a <> foldMap f ga

instance Traversable FreeGroup where
  -- TODO
  traverse ∷ (Applicative f) ⇒ (a → f b) → FreeGroup a → f (FreeGroup b)
  traverse _ Zer        = pure Zer
  traverse f (Neg a ga) = Neg <$> f a <*> traverse f ga
  traverse f (Pos a ga) = Pos <$> f a <*> traverse f ga

instance Applicative FreeGroup where
  -- FIMXE may also want to newtype
  {-
  -- https://en.wikibooks.org/wiki/Haskell/Applicative_functors#Applicative_functor_laws
  pure id <*> v = v                            -- Identity
  pure f <*> pure x = pure (f x)               -- Homomorphism
  u <*> pure y = pure ($ y) <*> u              -- Interchange
  pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
  -}
  pure ∷ a → FreeGroup a
  -- pure a = Pos a Zer
  pure = flip Pos Zer -- TODO

  (<*>) ∷ FreeGroup (a → b) → FreeGroup a → FreeGroup b
  (<*>) = ap

instance Monad FreeGroup where
  (>>=) ∷ FreeGroup a → (a → FreeGroup b) → FreeGroup b
  (>>=) = join ‥ (<&>)
    where
      join ∷ FreeGroup (FreeGroup a) → FreeGroup a
      join Zer          = Zer
      join (Neg ga gga) = invert ga <> join gga
      join (Pos ga gga) =        ga <> join gga

instance Alternative FreeGroup where
  empty ∷ FreeGroup a
  empty = Zer
  (<|>) ∷ FreeGroup a → FreeGroup a → FreeGroup a
  (<|>) = undefined -- TODO
