{-# LANGUAGE InstanceSigs, GADTs, PostfixOperators, UnicodeSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module ERE where

import           Common
import           Data.Set.Unicode
import           Data.Pointed
import           Finite (Finite, Σ)

-- α, β ⩴ ∅ | ε | σ | α|β | α·β | α&β | ¬α | α★
-- where σ ∈ Σ
data ExRE s where
  Zero ∷     ExRE s                    -- The empty language         -- ℒ(Zero)  = ∅
  One  ∷     ExRE s                    -- The empty string, epsilon  -- ℒ(One)   = {ε}
  Lit  ∷ s → ExRE s                    -- Literal, single symbol     -- ℒ(σ)     = {σ}, for σ ∈ Σ
  (:.) ∷     ExRE s → ExRE s → ExRE s  -- Concatenation              -- ℒ(α · β) = ℒ(α) · ℒ(β)
  (:|) ∷     ExRE s → ExRE s → ExRE s  -- Union, plus, or            -- ℒ(α | β) = ℒ(α) ∪ ℒ(β)
  (:&) ∷     ExRE s → ExRE s → ExRE s  -- logical and                -- ℒ(α & β) = ℒ(α) ∩ ℒ(β)
  Star ∷     ExRE s → ExRE s           -- Kleene star, repetition    -- ℒ(α★)    = ℒ(α)★
  Comp ∷     ExRE s → ExRE s           -- complement ¬               -- ℒ(¬α)    = Σ★ \ ℒ(α)
  deriving (Eq, Ord, Functor, Foldable, Traversable)

data ExREF s a where
  ZeroF   ∷         ExREF s a
  OneF    ∷         ExREF s a
  LitF    ∷     s → ExREF s a
  UnionF  ∷ a → a → ExREF s a
  ConcatF ∷ a → a → ExREF s a
  InterF  ∷ a → a → ExREF s a
  StarF   ∷     a → ExREF s a
  CompF   ∷     a → ExREF s a
  deriving (Eq, Functor)

instance (Finite s) ⇒ Σ (ExRE  s  ) s
instance (Finite s) ⇒ Σ (ExREF s a) s

instance (Show s) ⇒ Show (ExRE s) where
   show Zero     = "∅"
   show One      = "ε"
   show (Lit  σ) = show σ
   show (α :| β) =  "(" ++ show α ++ "∣" ++ show β ++ ")"
   show (α :. β) =  "(" ++ show α ++ "·" ++ show β ++ ")"
   show (α :& β) =  "(" ++ show α ++ "&" ++ show β ++ ")"
   show (Star α) =  "(" ++ show α ++ ")★"
   show (Comp α) = "¬(" ++ show α ++ ")"

instance Pointed ExRE where
  point = Lit

instance Applicative ExRE where
  pure ∷ s → ExRE s
  pure = point

  (<*>) ∷ ExRE (a → b) → ExRE a → ExRE b
  (<*>) Zero     _ = Zero
  (<*>) One      _ = One
  (<*>) (Lit  f) γ = fmap f γ
  (<*>) (α :| β) γ = (α <*> γ) :| (β <*> γ)
  (<*>) (α :. β) γ = (α <*> γ) :. (β <*> γ)
  (<*>) (α :& β) γ = (α <*> γ) :& (β <*> γ)
  (<*>) (Comp α) γ = Comp (α <*> γ)
  (<*>) (Star α) γ = Star (α <*> γ)

instance Monad ExRE where
  (>>=) ∷ ExRE a → (a → ExRE b) → ExRE b
  (>>=) Zero     _ = Zero
  (>>=) One      _ = One
  (>>=) (Lit  s) f = f s
  (>>=) (α :| β) f = (α >>= f) :| (β >>= f)
  (>>=) (α :. β) f = (α >>= f) :. (β >>= f)
  (>>=) (α :& β) f = (α >>= f) :& (β >>= f)
  (>>=) (Star α) f = Star (α >>= f)
  (>>=) (Comp α) f = Comp (α >>= f)

-- "star height"
height ∷ ExRE s → ℕ
height Zero     = 0
height One      = 0
height (Lit  _) = 0
height (α :| β) = max (height α) (height β)
height (α :. β) = max (height α) (height β)
height (α :& β) = max (height α) (height β)
height (Star α) = 1 + height α
height (Comp α) = height α