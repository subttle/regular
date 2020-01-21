{-# OPTIONS_GHC -Wall                   #-}
-- Unfortunately, using Fin types breaks the warnings for incomplete patterns at this time
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE OverloadedStrings          #-}

import           DFA
-- import qualified NFA
-- import qualified EFA
-- import qualified GFA
import           RegExp (RegExp (..))
import qualified RegExp as RE hiding (RegExp (..))
import           Language (ℒ)
import qualified Language
import           Common
import           Finite
import           Examples
import           Data.Set (singleton)
import           Config
import           Numeric.Natural.Unicode (ℕ)
import           Data.Eq.Unicode ((≠))
import           Data.Functor.Contravariant (Equivalence (..))
import           EasyTest
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE (NonEmpty(..))
import           Data.Either (isRight, isLeft, lefts)

main ∷ IO ()
main = run suite

suite ∷ Test ()
suite = tests [ testFizzBuzz
              , scope "DFA.empty"     . expect $ Config.language DFA.empty          == ([]   ∷ [[Bool]])
              , scope "DFA.epsilon"   . expect $ Config.language DFA.epsilon        == ([[]] ∷ [[Bool]])
              , scope "DFA.literal"   . expect $ Config.language (DFA.literal True) == [[True]]
              , scope "DFA.quotient"  . expect $ minimal `DFA.equal` quotient minimal && size' (useful (quotient minimal)) < size' (useful minimal)
              , scope "DFA.toRE"      . expect $ toRE by5 `RE.equivalent` by5'
              , testDFArquotient
              , testDFAinvhomimage
              , testRESubstitution
              , testBisimSubset (by5, DFA.toLanguage by5) (List.take 101 (freeMonoid asList))
              -- "For example, the restricted growth function 0,1,1,2,0,3,1 defines the set partition {{1,5}, {2,3,7}, {4}, {6}}"
              -- https://www8.cs.umu.se/kurser/TDBAfl/VT06/algorithms/BOOK/BOOK4/NODE153.HTM
              , scope "toRGS"         . expect $ (toRGS ∷ Equivalence Fin₇ → [ℕ]) (toEquivalence ([0 NE.:| [4], 1 NE.:| [2, 6], 3 NE.:| [], 5 NE.:| []])) == [0, 1, 1, 2, 0, 3, 1]
              -- FIXME: if using a newtype for `RGS` instead of `[ℕ]` type, then this can be strengthened to `bijection`
              , scope "RGS"           . expect $ retraction (toRGS ∷ Equivalence Suit → [ℕ]) (fromRGS ∷ [ℕ] → Equivalence Suit)
              ]

-- Test that ordinary FizzBuzz has the same output as the FizzBuzz which uses DFA
testFizzBuzz ∷ Test ()
testFizzBuzz = scope "main.FizzBuzz" . expect $ woDFA == wDFA
  where
    -- FizzBuzz (without DFA)
    woDFA ∷ [String]
    woDFA = fmap fizzbuzz [1 .. 100]
      where
        fizz ∷ ℕ → Bool
        fizz n = n `mod` 3 == 0
        buzz ∷ ℕ → Bool
        buzz n = n `mod` 5 == 0
        fbzz ∷ ℕ → Bool
        fbzz n = fizz n && buzz n
        fizzbuzz ∷ ℕ → String
        fizzbuzz n | fbzz n    = "FizzBuzz"
                   | fizz n    = "Fizz"
                   | buzz n    = "Buzz"
                   | otherwise = show n
    -- FizzBuzz (with DFA)
    wDFA ∷ [String]
    wDFA = fmap fizzbuzz [1 .. 100]
      where
        fizz ∷ ℕ → Bool
        fizz n = accepts  by3                         (toDigits n)
        buzz ∷ ℕ → Bool
        buzz n = accepts                         by5  (toDigits n)
        fbzz ∷ ℕ → Bool
        fbzz n = accepts (by3 `DFA.intersection` by5) (toDigits n)
        fizzbuzz ∷ ℕ → String
        fizzbuzz n | fbzz n    = "FizzBuzz"
                   | fizz n    = "Fizz"
                   | buzz n    = "Buzz"
                   | otherwise = show n

-- https://math.stackexchange.com/questions/871662/finding-right-quotient-of-languages
testDFArquotient ∷ Test ()
testDFArquotient = scope "DFA.rquotient" . expect $ and [ Config.accepts e₃L₁   [C, A, R, R, O, T]
                                                        , Config.accepts e₃L₂   [T]
                                                        , Config.accepts e₃L₂   [O, T]
                                                        , Config.accepts e₃L₁L₂ [C, A, R, R, O]
                                                        , Config.accepts e₃L₁L₂ [C, A, R, R]
                                                        , Prelude.take 2 (Config.language e₃L₁L₂) == [[C, A, R, R], [C, A, R, R, O]]
                                                        ]
  where
    e₃L₁ ∷ DFA Fin₈ Alpha
    e₃L₁   = DFA δ 0 (singleton 6)
      where
        δ ∷ (Fin₈, Alpha) → Fin₈
        δ (0, C) = 1
        δ (1, A) = 2
        δ (2, R) = 3
        δ (3, R) = 4
        δ (4, O) = 5
        δ (5, T) = 6
        δ _      = 7
    e₃L₂ ∷ DFA (Fin₈, Ordering) Alpha
    e₃L₂   = DFA.union (right e₃L₁ 4) (DFA.literal T)
    -- e₃L₂ = DFA.union (right e₃L₁ 4) (right e₃L₁ 5)
    e₃L₁L₂ ∷ DFA Fin₈ Alpha
    e₃L₁L₂ = DFA.rquotient e₃L₁ e₃L₂

testDFAinvhomimage ∷ Test ()
testDFAinvhomimage = scope "DFA.invhomimage" . expect $ same
  where
    same ∷ Bool
    same = DFA.invhomimage h slide22 `DFA.equal` expected
      where
        -- slide 22 http://infolab.stanford.edu/~ullman/ialc/spr10/slides/rs2.pdf
        slide22 ∷ DFA Fin₃ Fin₂
        slide22 = DFA δ 0 (singleton 2)
          where
            δ (0, 0) = 1
            δ (0, 1) = 2
            δ (1, 0) = 0
            δ (1, 1) = 2
            δ (2, 0) = 0
            δ (2, 1) = 1        
        h ∷ Bool → [Fin₂]
        h False = [0,1]
        h True  = []
        expected ∷ DFA Fin₃ Bool 
        expected = DFA δ 0 (singleton 2)
          where
            δ ∷ (Fin₃, Bool) → Fin₃
            δ (0, False) = 2
            δ (0, True ) = 0
            δ (1, False) = 2
            δ (1, True ) = 1
            δ (2, False) = 2
            δ (2, True ) = 2

-- Substitution
-- A Second Course in Formal Languages and Automata Theory (Pg 55, Example 3.3.4)
-- s(101) = (cd)*(a+ab)*(cd)*
testRESubstitution ∷ Test ()
testRESubstitution = scope "RE.>>=" . expect $ result == expected -- N.B. the use of structural equality is intentional here
  where
    original ∷ RegExp Fin₂
    original = RE.fromList [1, 0, 1]
    -- h(0) = {a, ab}*
    -- h(1) = (cd)*
    h ∷ Fin₂ → RegExp Fin₄
    h 0 = Star (Lit 0 :| RE.fromList [0,1])
    h 1 = Star (RE.fromList [2, 3])
    result ∷ RegExp Fin₄
    result = original >>= h
    -- (cd)*(a+ab)*(cd)*
    expected ∷ RegExp Fin₄
    expected =  Star (         RE.fromList [2, 3])
            :. (Star (Lit 0 :| RE.fromList [0, 1])
            :.  Star (         RE.fromList [2, 3]))

-- An involution is a mapping, f, that coincides with its own inverse, i.e.,
-- f x ≡ f⁻¹ x
-- or, equivalently,
-- f (f x) ≡ x
involution
  ∷ ∀ a b . (Eq a, Eq b)
  ⇒ [Either a b] → (a → b) → (b → a) → Bool
involution x ab ba = fmap (f . f) x == x
  where
    -- Turn an `a` into a `b` or
    -- turn a `b` into an `a`
    f ∷ Either a b → Either a b
    f = either (Right . ab) (Left . ba)

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses
-- A retraction, aka "left inverse", 
retraction
  ∷ ∀ a b . (Finite a, Eq b)
  ⇒ (a → b) → (b → a) → Bool
retraction = involution (fmap Left (asList ∷ [a]))

-- A section, aka "right inverse"
section
  ∷ ∀ a b . (Eq a, Finite b)
  ⇒ (a → b) → (b → a) → Bool
section = involution (fmap Right (asList ∷ [b]))

bijection
  ∷ ∀ a b . (Finite a, Finite b)
  ⇒ (a → b) → (b → a) → Bool
bijection = involution (asList ∷ [Either a b])

-- Coinductive bisimulation (partial)
-- Either the bisimulation will succeed (on the given subset) or
-- it will produce a counter-example to the bisimulation
-- (i.e. a witness to the proof of its negation)
-- basically we take some subset of Σ⋆ to be sampled for
-- "observational equality", here meaning both `m` and `ℓ`
-- are in agreeance of which words to accept and reject.
testBisimSubset ∷ forall q s automaton p
                . (Finite q, Finite s, Configuration automaton q s p)
                ⇒ (automaton q s, ℒ s)
                → [[s]]
                → Test ()
testBisimSubset (m, ℓ) subset = scope "bisim" . expect $ isBisim
  where
    -- try to partition, into two parts, (a subset/sample of) Σ⋆:
    -- words tagged with `Right` (ℒ₁ ≡ ℒ₂)
    -- words tagged with `Left`  (ℒ₁ ≢ ℒ₂)
    witnesses ∷ [Either [s] [s]]
    witnesses = List.unfoldr bisim subset
      where
        accepts₁ ∷ [s] → Bool
        accepts₁ = Config.accepts   m
        accepts₂ ∷ [s] → Bool
        accepts₂ = Language.accepts ℓ
        bisim ∷ [[s]] → Maybe (Either [s] [s], [[s]])
        bisim []                                    = Nothing
        bisim (w : todo) | accepts₁ w == accepts₂ w = Just (Right w, todo)
        bisim (w : todo) | accepts₁ w ≠  accepts₂ w = Just (Left  w, todo)
    isBisim ∷ Bool
    isBisim = all isRight witnesses
    _isNotBisim ∷ Bool
    _isNotBisim = any isLeft witnesses
    -- The list of words on which `m` and `ℓ` did not agree
    -- i.e. a list of counter examples
    _negationProof ∷ [[s]]
    _negationProof = lefts witnesses

