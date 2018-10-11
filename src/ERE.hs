{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PostfixOperators      #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}

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

-- TODO once the algebraic `(+)`, `(*)`, `(&)`, `star`, `comp` operators are properly defined
-- these functions can then be used:
{-
normalize ∷ (Ord s) ⇒ ExRE s → ExRE s
normalize Zero        = zero
normalize One         = one
normalize (Lit  σ)    = literal σ
normalize (α :| β)    = normalize α + normalize β
normalize (α :. β)    = normalize α * normalize β
normalize (α :& β)    = normalize α & normalize β
normalize (Star α)    = star (normalize α)
normalize (Comp α)    = comp (normalize α)

-- Brzozowski ∂ with respect to σ ∈ Σ
derivative ∷ (Ord s) ⇒ ExRE s → s → ExRE s
derivative Zero     _ = zero
derivative One      _ = zero
derivative (Lit σ') σ = if σ' == σ then one else zero
derivative (α :| β) σ = derivative α σ + derivative β σ
derivative (α :. β) σ = (derivative α σ * β) + (constant α * derivative β σ)
derivative (α :& β) σ = derivative α σ & derivative β σ
derivative (Star α) σ = derivative α σ * star α
derivative (Comp α) σ = comp (derivative α σ)

-- Brzozowski ∂ extended to strings
derivative' ∷ (Ord s) ⇒ ExRE s → [s] → ExRE s
derivative' = List.foldl derivative

matches ∷ (Ord s) ⇒ ExRE s → [s] → Bool
matches Zero       _ = False
matches α         [] = constant α == One
matches α    (a : w) = matches (derivative α a) w

nullable ∷ (Ord s) ⇒ ExRE s → Bool
nullable = nullable' . normalize
  where nullable' Zero     = False
        nullable' One      = True
        nullable' (Lit  _) = False
        nullable' (α :| β) = nullable' α ∨ nullable' β
        nullable' (α :. β) = nullable' α ∧ nullable' β
        nullable' (α :& β) = nullable' α ∧ nullable' β
        nullable' (Star _) = True
        nullable' (Comp α) = not (nullable' α)

constant ∷ (Ord s) ⇒ ExRE s → ExRE s
constant α | nullable α = One
           | otherwise  = Zero

difference ∷ ExRE s → ExRE s → ExRE s
difference α β =  α & comp β

-}
