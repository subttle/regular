{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wall                  #-}

module EFA where

import           Data.Functor.Contravariant
import           Data.Map            as Map (Map, fromList)
import qualified Data.Map            as Map (fromSet, toAscList)
import           Prelude             hiding (map)
import           Data.Set            as Set hiding (foldl)
import           Data.Set.Unicode
import qualified Data.List           as List
import qualified Data.List.NonEmpty  as NE
import           Finite
import           Common
import qualified TransitionGraph as TG
import qualified FA
import qualified RegExp as RE
import qualified ERE as Ex
import           Config

-- Nondeterministic Finite Automaton with ε-transitions
data EFA q s =
     EFA { delta ∷ (q, Maybe s) → Set q  -- δ : Q × (Σ ∪ {ε}) → P(Q)
         ,    q0 ∷ q                     -- The initial state
         ,    fs ∷ Set q                 -- The final states
         }

-- TODO Coend? http://www.staff.city.ac.uk/~ross/papers/Constructors.pdf
data SomeEFA s where
 SomeEFA ∷ (Show q, Finite q) ⇒ EFA q s → SomeEFA s

instance (Finite q) ⇒ Q (EFA q s) q
instance (Finite s) ⇒ Σ (EFA q s) s

instance (Finite s) ⇒ Σ (SomeEFA s) s

instance Contravariant (EFA q) where
  contramap ∷ (g → s) → EFA q s → EFA q g
  contramap h (EFA δ q₀ f) = EFA (\(q, γ) → δ (q, fmap h γ)) q₀ f

instance Contravariant SomeEFA where
  contramap ∷ (g → s) → SomeEFA s → SomeEFA g
  contramap h (SomeEFA m) = SomeEFA (contramap h m)

instance (Show q, Finite q, Show s, Finite s) ⇒ Show (EFA q s) where
  show ∷ EFA q s → String
  show m = quoteWith "( " " )" $ List.intercalate "\n, "
           [ equation "Q "                         ((show     . Set'         . qs     ) m)
           , equation "Σ "                         ((show     . Set'         . sigma  ) m)
           , quoteWith "δ  : Q × (Σ ∪ {ε}) → P(Q)" ((format'' . Map.fromList . table  ) m) "\n"
           , equation "q₀"                         ((show     . q0                    ) m)
           , equation "F "                         ((show     . Set'         . final  ) m)
           ]

instance (Show s, Finite s) ⇒ Show (SomeEFA s) where
  show ∷ SomeEFA s → String
  show (SomeEFA m) = show m

instance (Finite q, Finite s) ⇒ Configuration EFA q s (Set q) where
  complete ∷ EFA q s → Bool
  complete = undefined -- FIXME implement when I restructure to allow conversions

  deterministic ∷ EFA q s → Bool -- FIXME implement when I restructure to allow conversions
  deterministic = undefined -- FIXME should I use the noEpsilonClosures ?

  codeterministic ∷ EFA q s → Bool
  codeterministic = undefined  -- FIXME

  occupied ∷ EFA q s → Set q → Set q
  occupied = const id

  initial  ∷ EFA q s → Set q
  initial  = eclosure <*> (singleton . q0)

  final    ∷ EFA q s → Set q
  final    = fs

  -- Given an EFA, m, and a configuration, return what it yields in one step
  (⊢) ∷ EFA q s → (Set q, [s]) → (Set q, [s])
  (⊢) _             (states,    []) = (states,                                                [])
  (⊢) m@(EFA δ _ _) (states, σ : w) = (eclosure m (foldMap δ (states × singleton (Just σ))),  w )

  accessible ∷ EFA q s → Set q
  accessible m@(EFA _ q₀ _) = reachable m q₀

  -- FIXME untested, also, consider characteristics of eclosure placement
  deltaD ∷ EFA q s → (Set q, s) → Set q
  deltaD m@(EFA δ _ _) (states, s) = eclosure m (foldMap (\q → δ (q, Just s)) states)

  -- δ★ : Q × (Σ ∪ {ε})★ → P(Q)
  -- "Extended delta"
  -- Extend the δ function to accept strings of symbols
  -- TODO random untested/unclear design thought: might be able to define a morphism on Q which involves eclosure?
  delta' ∷ EFA q s → (q, [s]) → Set q
  delta' m (q, w) = delta'' m (singleton q, w)

  -- δ′′ : P(Q) × (Σ ∪ {ε})★ → P(Q)
  -- TODO untested, but if keeping then rewrite (⊢★) to use `= (delta'' ..., [])`?
  delta'' ∷ EFA q s → (Set q, [s]) → Set q
  delta'' m@(EFA δ _ _) (states, w) = foldl (\occupied' σ → eclosure m (foldMap δ (occupied' × singleton (Just σ))))
                                            (eclosure m states)
                                            w

  -- Take an EFA, m, and a string, and then compute the resulting states, which may be an empty set
  eval ∷ EFA q s → [s] → Set q
  eval m@(EFA _ q₀ _) w = delta' m (q₀, w)

  toGraph ∷ EFA q s → TG.TG q s
  toGraph = undefined  -- TODO epsilon elimination
  -- toGraph ∷ EFA q s → TG.ETG q s
  -- toGraph (EFA δ _ _) = TG.ETG (\s → stars (fmap (\q → (q, Set.toList (δ (q, s)))) asList))


-- Convert the transition function to a Map
deltaToMap ∷ (Finite q, Finite s) ⇒ EFA q s → Map (q, Maybe s) (Set q)
deltaToMap m@(EFA δ _ _) = Map.fromSet δ (domain m)

domain ∷ (Finite q, Finite s) ⇒ EFA q s → Set (q, Maybe s)
domain m = qs m × sigma_ε m

-- The image of the transition function
image ∷ (Finite q, Finite s) ⇒ EFA q s → Set (Set q)
image m@(EFA δ _ _) = Set.map δ (domain m)

-- The transition table of the EFA
table ∷ (Finite q, Finite s) ⇒ EFA q s → [((q, Maybe s), Set q)]
table = Map.toAscList . deltaToMap

-- ε-closure of a set of states
-- Computes the set of states accessible from given state when no input can be consumed (0 or more ε-transitions)
-- Always contains at least the original state
eclosure ∷ ∀ q s . (Ord q) ⇒ EFA q s → Set q → Set q
eclosure (EFA δ _ _) = fixedPoint closure
  where
    closure ∷ Set q → Set q
    closure = foldMap (\q → q `Set.insert` δ (q, Nothing))

-- The EFA, empty, such that
-- ℒ(empty) = ∅
-- while adhering to Thompson's construction constraints
empty ∷ EFA Bool s
empty = EFA (const (∅)) False (singleton True)

-- The EFA, epsilon, such that
-- ℒ(epsilon) = {ε}
-- while adhering to Thompson's construction constraints
epsilon ∷ EFA Bool s
epsilon = EFA δ False (singleton True)
  where
    δ ∷ (Bool, Maybe s) → Set Bool
    δ (False, Nothing) = singleton True
    δ _                = (∅)

-- Given a symbol, construct an EFA which recognizes exactly that symbol and nothing else
literal ∷ ∀ s . (Eq s) ⇒ s → EFA Bool s
literal σ' = EFA δ False (singleton True)
  where
    δ ∷ (Bool, Maybe s) → Set Bool
    δ (False, Just σ) | σ == σ' = singleton True
    δ _                         = (∅)

-- Treat the given set as a set of literals to define a language
fromSet ∷ ∀ s . (Ord s) ⇒ Set s → EFA Bool s
fromSet s = EFA δ False (singleton True)
  where
    δ ∷ (Bool, Maybe s) → Set Bool
    δ (False, Just σ) | σ ∈ s = singleton True
    δ _                       = (∅)

-- Avoid using `foldl` because the base case may introduce extra states
fromList ∷ (Eq s) ⇒ [s] → SomeEFA s
fromList []      = SomeEFA epsilon
fromList (σ : w) = fromNE (σ NE.:| w)

fromNE ∷ (Eq s) ⇒ NE.NonEmpty s → SomeEFA s
fromNE = foldl1 (\(SomeEFA acc) (SomeEFA σ) → SomeEFA (concatenate acc σ)) . fmap (SomeEFA . literal)

-- TODO not really tested
fromLang ∷ (Eq s) ⇒ [[s]] → SomeEFA s
fromLang [] = SomeEFA EFA.empty
fromLang ws = foldl1 (\(SomeEFA m₁) (SomeEFA m₂) → SomeEFA (EFA.union m₁ m₂)) (fmap EFA.fromList ws)

-- TODO deleteme
lang ∷ (Finite s) ⇒ SomeEFA s → [[s]]
lang (SomeEFA m) = language m

-- Thompson's construction
fromRE ∷ (Eq s) ⇒ RE.RegExp s → SomeEFA s
fromRE RE.Zero     = SomeEFA EFA.empty
fromRE RE.One      = SomeEFA epsilon
fromRE (RE.Lit  σ) = SomeEFA (literal σ)
fromRE (α RE.:| β) = union'       (fromRE α) (fromRE β)
               where union'       ∷ SomeEFA s → SomeEFA s → SomeEFA s
                     union'       (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.union       m₁ m₂)
fromRE (α RE.:. β) = concatenate' (fromRE α) (fromRE β)
               where concatenate' ∷ SomeEFA s → SomeEFA s → SomeEFA s
                     concatenate' (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.concatenate m₁ m₂)
fromRE (RE.Star α) = star'        (fromRE α)
               where star'        ∷             SomeEFA s → SomeEFA s
                     star'                     (SomeEFA m)  = SomeEFA (EFA.star m)

-- Thompson's construction on regular expressions extended with intersection
fromERE ∷ ∀ s . (Eq s) ⇒ Ex.ExRE s → SomeEFA s
fromERE Ex.Zero     = SomeEFA EFA.empty
fromERE Ex.One      = SomeEFA epsilon
fromERE (Ex.Lit  σ) = SomeEFA (literal σ)
fromERE (α Ex.:| β) = union'       (fromERE α) (fromERE β)
                where union'       ∷ SomeEFA s → SomeEFA s → SomeEFA s
                      union'       (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.union       m₁ m₂)
fromERE (α Ex.:. β) = concatenate' (fromERE α) (fromERE β)
                where concatenate' ∷ SomeEFA s → SomeEFA s → SomeEFA s
                      concatenate' (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.concatenate m₁ m₂)
fromERE (α Ex.:& β) = intersect'   (fromERE α) (fromERE β)
                where intersect'   ∷ SomeEFA s → SomeEFA s → SomeEFA s
                      intersect'   (SomeEFA m₁) (SomeEFA m₂) = SomeEFA (EFA.synchronous m₁ m₂)
fromERE (Ex.Star α) = star'        (fromERE α)
                where star'        ∷             SomeEFA s → SomeEFA s
                      star'                     (SomeEFA m)  = SomeEFA (EFA.star m)

-- Intersection via the synchronous product automaton
-- TODO I haven't yet verified that this follows the same McNaughton-Yamada-Thompson constraints used
-- TODO in all the other functions (noted with "for Thompson's construction") but the preliminary
-- TODO testing I've done so far seems to indicate that it works
-- Pg 58. http://www.dcc.fc.up.pt/~nam/web/resources/rafaelamsc.pdf
synchronous ∷ ∀ q p s . (Ord q, Ord p) ⇒ EFA q s → EFA p s → EFA (q, p) s
synchronous (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) = EFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Maybe s) → Set (q, p)
    δ ((q, p), Nothing) = (δ₁ (q, Nothing) × δ₂ (p, Nothing))
                        ∪  δ₁ (q, Nothing) × singleton p
                        ∪ singleton q      × δ₂ (p, Nothing)
    δ ((q, p), σ)       =  δ₁ (q, σ)       × δ₂ (p, σ)

-- Union for Thompson's construction
union ∷ ∀ q p s . (Ord q, Ord p) ⇒ EFA q s → EFA p s → EFA (Either Bool (Either q p)) s
union (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) = EFA δ (Left False) (Set.singleton (Left True))
  where
    δ ∷ (Either Bool (Either q p), Maybe s) → Set (Either Bool (Either q p))
    δ (Left      False, Nothing)          = Set.fromList [Right (Left q₀), Right (Right p₀)]
    δ (Left          _,       _)          = (∅)
    -- connect the "old" final states of m₁ to the new final state
    δ (Right (Left  q), Nothing) | q ∈ f₁ = Left True `Set.insert` Set.map (Right . Left)  (δ₁ (q, Nothing))
    δ (Right (Left  q),       σ)          =                        Set.map (Right . Left)  (δ₁ (q,       σ))
    δ (Right (Right p), Nothing) | p ∈ f₂ = Left True `Set.insert` Set.map (Right . Right) (δ₂ (p, Nothing))
    δ (Right (Right p),       σ)          =                        Set.map (Right . Right) (δ₂ (p,       σ))

-- Concatenation for Thompson's construction
concatenate ∷ ∀ q p s . (Ord q, Ord p) ⇒ EFA q s → EFA p s → EFA (Either q p) s
concatenate (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) = EFA δ (Left q₀) (map Right f₂)
  where
    δ ∷ (Either q p, Maybe s) → Set (Either q p)
    -- if this state, q, is a final state, merge q's transitions with p₀'s transitions
    δ (Left  q, σ) | q ∈ f₁ = δ₁ (q, σ) ⊎ δ₂ (p₀, σ)
    δ (Left  q, σ)          = δ₁ (q, σ) ⊎ (∅)
    δ (Right p, σ)          = (∅)       ⊎ δ₂ (p,  σ)

-- Kleene Star for Thompson's construction
star ∷ ∀ q s . (Ord q) ⇒ EFA q s → EFA (Either Bool q) s
star (EFA δ q₀ f) = EFA δ₁ (Left False) (singleton (Left True))
  where
    δ₁ ∷ (Either Bool q, Maybe s) → Set (Either Bool q)
    δ₁ (Left False, Nothing)         =                              Set.fromList [Right q₀, Left True]
    δ₁ (Left     _,       _)         = (∅)
    δ₁ (Right    q, Nothing) | q ∈ f = map Right (δ (q, Nothing)) ∪ Set.fromList [Right q₀, Left True]
    δ₁ (Right    q,       σ)         = map Right (δ (q,       σ))

-- FIXME test me, I wrote this when tired
-- The asynchronous product of two EFA
-- Essentially this runs two EFAs with different alphabets "in parallel" independently
asynchronous ∷ ∀ q p s g . (Ord q, Ord p) ⇒ EFA q s → EFA p g → EFA (q, p) (Either s g)
asynchronous (EFA δ₁ q₀ f₁) (EFA δ₂ p₀ f₂) = EFA δ (q₀, p₀) (f₁ × f₂)
  where
    δ ∷ ((q, p), Maybe (Either s g)) → Set (q, p)
    δ ((q, p), Nothing)        = δ₁ (q, Nothing) × δ₂ (p, Nothing)
    δ ((q, p), Just (Left  σ)) = δ₁ (q, Just  σ) × singleton p
    δ ((q, p), Just (Right γ)) = singleton q     × δ₂ (p, Just  γ)

-- TODO version which determinizes instead of adding an extra state
fromFA ∷ ∀ q s . (Ord q) ⇒ FA.FA q s → EFA (Either () q) s
fromFA (FA.FA δ i f) = EFA (Set.map Right . δ₁) (Left ()) (Set.map Right f)
  where
    δ₁ ∷ (Either () q, Maybe s) → Set q
    δ₁ (Left (), Nothing) = i
    δ₁ (Right q, Just  σ) = δ (q, σ)
    δ₁ _                  = (∅)
