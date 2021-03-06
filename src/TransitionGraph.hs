{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module TransitionGraph where

import           Algebra.Graph.Relation as Relation (Relation, gmap, transpose)
import           Data.Foldable (Foldable (toList))
import           Data.Functor.Contravariant (Contravariant (..))
import           Common (quoteWith)
import           Finite (Finite (..), Q (..), Σ (..))

-- Transition Graph of an automaton
newtype  TG q s =  TG (      s → Relation q)
-- Transition Graph of an automaton with ε-transitions
newtype ETG q s = ETG (Maybe s → Relation q)

instance (Finite q) ⇒ Q (TG q s) q
instance (Finite s) ⇒ Σ (TG q s) s

instance (Finite q) ⇒ Q (ETG q s) q
instance (Finite s) ⇒ Σ (ETG q s) s

instance Contravariant (TG q) where
  contramap ∷ (a → b) → TG q b → TG q a
  contramap f (TG g) = TG (g . f)

instance Contravariant (ETG q) where
  contramap ∷ (a → b) → ETG q b → ETG q a
  contramap f (ETG g) = ETG (g . fmap f)

instance (Show q, Show s, Finite q, Finite s) ⇒ Show (TG q s) where
  show ∷ TG q s → String
  show (TG m) = unlines (fmap (\s → quoteWith (show s) (show (m s)) " → ") (toList (sigma (TG m))))

instance (Show q, Show s, Finite q, Finite s) ⇒ Show (ETG q s) where
  show ∷ ETG q s → String
  show (ETG m) = unlines (fmap (\s → quoteWith (show s) (show (m s)) " → ") (toList (sigma_ε (ETG m))))

reverse ∷ (Ord q) ⇒ TG q s → TG q s
reverse (TG g) = TG (Relation.transpose . g)

map ∷ (Ord p) ⇒ (q → p) → TG q s → TG p s
map f (TG g) = TG (gmap f . g)
