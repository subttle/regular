{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Rose where

import           Control.Comonad (Comonad (..))
import           Data.Bool (bool)
import           Data.Foldable (fold)
import           Data.Function ((&))
import           Data.Functor.Identity (Identity (..))
import           Data.Maybe (fromMaybe)
import           Data.Traversable.TreeLike (printTree)
import qualified Data.Tree as Tree
import           Common ((‥))

-- Experiments based on "Higher Dimensional Trees, Algebraically"

data Rose f a = Rose a (Maybe (f (Rose f a)))
type Tree f a = Maybe (Rose f a)
type Rose0 a = Identity a
type Rose1 = Rose Identity
type Rose2 = Rose Rose1
type Rose3 = Rose Rose2
type RoseTree = Rose []

-- TODO cata but consider Mendler style?
rose ∷ (Functor f)
     ⇒ (a → Maybe (f b) → b)
     → (       Rose f a → b)
rose g (Rose a f) = g a (fmap (fmap (rose g)) f)

toTree ∷ Rose [] a → Tree.Tree a
toTree = rose (flip (.) (fromMaybe []) . Tree.Node)

fromTree ∷ Tree.Tree a → Rose [] a
fromTree = Tree.foldTree (\a f → bool (Rose a (Just f)) (Rose a Nothing) (null f))

forest ∷ (Functor f) ⇒ Rose f a → Maybe (f (Rose f a))
forest (Rose _ f) = f

instance (Functor f) ⇒ Functor (Rose f) where
  fmap ∷ (a → b) → Rose f a → Rose f b
  fmap = rose . (Rose ‥ ($))

instance (Functor f, Foldable f) ⇒ Foldable (Rose f) where
  foldMap ∷ (Monoid m) ⇒ (a → m) → Rose f a → m
  foldMap = rose . (flip (.) (maybe mempty fold) ‥ (mappend ‥ ($)))

instance (Functor f) ⇒ Comonad (Rose f) where
  extract ∷ Rose f a → a
  extract = rose const
  duplicate ∷ Rose f a → Rose f (Rose f a)
  duplicate (Rose a f) = Rose (Rose a f) (fmap (fmap duplicate) f)
