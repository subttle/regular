{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module NotEmpty where

import           Control.Applicative (Const (Const))
import           Data.Can (Can (Non))
import           Data.Functor.Identity (Identity (Identity))
import           Data.Set (Set)
import qualified Data.Set.Ordered as OSet
import           Data.Set.Ordered (OSet)
import           Data.Set.Unicode ((∅))
import           Data.Smash (Smash (Nada))
import           Data.Wedge (Wedge (Nowhere))
import           Numeric.Natural.Unicode (ℕ)
import           Prelude.Unicode (ℤ)
import           Finite (Fin₁, Fin₂, Fin₃, Fin₄, Fin₅, Fin₆, Fin₇, Fin₈, Fin₉, Fin₁₀, Fin₁₁, Fin₁₂, Fin₁₃, Fin₁₄, Fin₁₅,
                         Quadrant (Q₁), Octant (O₁), Alpha (A), DNA (Adenine), Month (January),
                         Card (Card), Rank (Two), Suit (Spade),
                         type (🁢), (🁣), type (🀰), (🀱), type (:🎲), (⚀), Checker, (⛀),
                         Init (..), Final (..))

-- TODO experimental
-- A wrapper for some type `a` which is known to be not empty (the proof of
-- which is witnessed by `wit`).
-- TODO there are some practices/laws for this class which I should formalize
class NotEmpty a where
  wit ∷ a

instance NotEmpty () where
  wit  ∷ ()
  wit  = ()
instance NotEmpty Init where
  wit  ∷ Init
  wit  = Init ()
instance NotEmpty Final where
  wit  ∷ Final
  wit  = Final ()
instance NotEmpty Bool where
  wit  ∷ Bool
  wit  = False
instance NotEmpty Ordering where
  wit  ∷ Ordering
  wit  = LT
instance NotEmpty Quadrant where
  wit  ∷ Quadrant
  wit  = Q₁
instance NotEmpty Octant where
  wit  ∷ Octant
  wit  = O₁
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

instance NotEmpty Char where
  wit ∷ Char
  wit = '\NUL'
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
instance NotEmpty (:🎲) where
  wit ∷ (:🎲)
  wit = (⚀)
instance NotEmpty (🁢) where
  wit ∷ (🁢)
  wit = (🁣)
instance NotEmpty (🀰) where
  wit ∷ (🀰)
  wit = (🀱)
instance NotEmpty Checker where
  wit ∷ Checker
  wit = (⛀)
instance NotEmpty Month where
  wit ∷ Month
  wit = January

instance NotEmpty [a] where
  wit ∷ [a]
  wit = []
instance NotEmpty (Maybe a) where
  wit ∷ Maybe a
  wit = Nothing
instance NotEmpty (Smash a b) where
  wit ∷ Smash a b
  wit = Nada
instance NotEmpty (Wedge a b) where
  wit ∷ Wedge a b
  wit = Nowhere
instance NotEmpty (Can a b) where
  wit ∷ Can a b
  wit = Non
instance NotEmpty (Set a) where
  wit ∷ Set a
  wit = (∅)
instance NotEmpty (OSet a) where
  wit ∷ OSet a
  wit = OSet.empty
instance (NotEmpty a) ⇒ NotEmpty (Const a b) where
  wit ∷ Const a b
  wit = Const wit
instance (NotEmpty a) ⇒ NotEmpty (Identity a) where
  wit ∷ Identity a
  wit = Identity wit
instance (NotEmpty a, NotEmpty b) ⇒ NotEmpty (a, b) where
  wit ∷ (a, b)
  wit = (wit, wit)
instance (NotEmpty a, NotEmpty b, NotEmpty c) ⇒ NotEmpty (a, b, c) where
  wit ∷ (a, b, c)
  wit = (wit, wit, wit)
instance (NotEmpty a, NotEmpty b, NotEmpty c, NotEmpty d) ⇒ NotEmpty (a, b, c, d) where
  wit ∷ (a, b, c, d)
  wit = (wit, wit, wit, wit)
instance (NotEmpty a, NotEmpty b, NotEmpty c, NotEmpty d, NotEmpty e) ⇒ NotEmpty (a, b, c, d, e) where
  wit ∷ (a, b, c, d, e)
  wit = (wit, wit, wit, wit, wit)
instance (NotEmpty a, NotEmpty b, NotEmpty c, NotEmpty d, NotEmpty e, NotEmpty f) ⇒ NotEmpty (a, b, c, d, e, f) where
  wit ∷ (a, b, c, d, e, f)
  wit = (wit, wit, wit, wit, wit, wit)
instance (NotEmpty a, NotEmpty b, NotEmpty c, NotEmpty d, NotEmpty e, NotEmpty f, NotEmpty g) ⇒ NotEmpty (a, b, c, d, e, f, g) where
  wit ∷ (a, b, c, d, e, f, g)
  wit = (wit, wit, wit, wit, wit, wit, wit)
instance (NotEmpty a, NotEmpty b, NotEmpty c, NotEmpty d, NotEmpty e, NotEmpty f, NotEmpty g, NotEmpty h) ⇒ NotEmpty (a, b, c, d, e, f, g, h) where
  wit ∷ (a, b, c, d, e, f, g, h)
  wit = (wit, wit, wit, wit, wit, wit, wit, wit)
