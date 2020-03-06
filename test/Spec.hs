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
import           Data.Functor.Contravariant (contramap, Equivalence (..), Comparison (..), Predicate (..))
import qualified Data.Group as G
import           EasyTest (Test, tests, scope, expect, run)
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
              , scope "toRGS"         . expect $ toRGS (toEquivalence [0 NE.:| [4], 1 NE.:| [2, 6], 3 NE.:| [], 5 NE.:| []]) == (RGS [0, 1, 1, 2, 0, 3, 1] ∷ RGS Fin₇)
              , scope "RGS"           . expect $ bijection (toRGS ∷ Equivalence Suit → RGS Suit) (fromRGS ∷ RGS Suit → Equivalence Suit)
              , testComposeC
              , testGroupInvert
              , testCycles
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
testDFArquotient = scope "DFA.rquotient" . expect $ and e₃Tests
  where
    -- L₁ = {"carrot"}
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
    -- L₂ = {"t"} ∪ {"ot"} = {"t", "ot"}
    e₃L₂ ∷ DFA (Fin₈, Fin₈) Alpha
    e₃L₂   = DFA.union (right e₃L₁ 5) (right e₃L₁ 4)
    -- L₁/L₂ = {"carro", "carr"}
    e₃L₁L₂ ∷ DFA Fin₈ Alpha
    e₃L₁L₂ = DFA.rquotient e₃L₁ e₃L₂
    -- {"carrot"} / {"t", "ot"} = {"carro", "carr"}
    e₃Tests ∷ [Bool]
    e₃Tests = [ Config.accepts e₃L₁   [C, A, R, R, O, T]                  -- test that "carrot" ∈ L₁
              , Config.accepts e₃L₂   [O, T]                              -- test that     "ot" ∈    L₂
              , Config.accepts e₃L₂   [T]                                 -- test that      "t" ∈    L₂
              , Config.accepts e₃L₁L₂ [C, A, R, R, O]                     -- test that "carro"  ∈ L₁/L₂
              , Config.accepts e₃L₁L₂ [C, A, R, R]                        -- test that "carr"   ∈ L₁/L₂
              , Prelude.take 2 (Config.language e₃L₁L₂) == [[C, A, R, R], [C, A, R, R, O]]
              ]

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

-- TODO
-- Shuffle
-- A Second Course in Formal Languages and Automata Theory (Pg 57, Example 3.3.8)
testNFAshuffle ∷ Test ()
testNFAshuffle = scope "NFA.shuffle" . expect $ and [test]
  where
    ab_cd ∷ [[Alpha]]
    ab_cd = fmap (fmap abcdh) (Config.language abcd')
      where
        abh ∷ Bool → Alpha
        abh False = A
        abh True  = B
        cdh ∷ Bool → Alpha
        cdh False = C
        cdh True  = D
        abcdh ∷ Either Bool Bool → Alpha
        abcdh = either abh cdh
        abcd' ∷ NFA.NFA (Fin₃, Fin₃) (Either Bool Bool)
        abcd' = NFA.asynchronous ab' cd'
          where
            ab' ∷ NFA.NFA Fin₃ Bool
            ab' = contramap abh ab
            cd' ∷ NFA.NFA Fin₃ Bool
            cd' = contramap cdh cd
    shuffled ∷ [[Alpha]]
    shuffled = [ [A, B, C, D]
               , [A, C, B, D]
               , [A, C, D, B]
               , [C, A, B, D]
               , [C, A, D, B]
               , [C, D, A, B]
               ]
    test ∷ Bool
    test = ab_cd == shuffled

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

-- Composition of permutations
testComposeC ∷ Test ()
testComposeC = scope "Comparison.Compose" . expect $ and [test₁, test₂, test₃]
  where
    -- https://en.wikipedia.org/wiki/Permutation_group#Composition_of_permutations%E2%80%93the_group_product
    (p, q) = (listToComparison [1, 3, 0, 2, 4], listToComparison [4, 3, 2, 1, 0]) ∷ (Comparison Fin₅, Comparison Fin₅)

    -- https://youtu.be/3aNeCWRjh8I?t=211
    c₁ ∷ Comparison Fin₄ -- 1 3 4 2
    c₁ = listToComparison [0, 2, 3, 1]
    c₂ ∷ Comparison Fin₄ -- 4 3 2 1
    c₂ = listToComparison [3, 2, 1, 0]
    c₃ ∷ Comparison Fin₄ -- 2 4 3 1
    c₃ = c₁ `composeC` c₂
    c₄ ∷ Comparison Fin₄ -- 4 2 1 3
    c₄ = c₂ `composeC` c₁

    test₁ ∷ Bool
    test₁ = q `composeC` p == listToComparison [3, 1, 4, 2, 0] -- 4 2 5 3 1

    test₂ ∷ Bool
    test₂ = comparisonToList c₃ == [1, 3, 2, 0]
    test₃ ∷ Bool
    test₃ = comparisonToList c₄ == [3, 1, 0, 2]

-- test laws of group invert function
testGroupInvert ∷ Test ()
testGroupInvert = scope "Comparison.Invert" . expect $ and [test₁, test₂]
  where
    comparisons ∷ [Comparison Fin₅]
    comparisons = asList
    test₁ ∷ Bool
    test₁ = all (\c → (         c) `composeC` (G.invert c) == mempty) comparisons
    test₂ ∷ Bool
    test₂ = all (\c → (G.invert c) `composeC` (         c) == mempty) comparisons

-- test to check that `cycles` function gives back a lawful equivalence relation
testCycles ∷ Test ()
testCycles = scope "Comparison.Cycles" . expect $ and [test₁, test₂, test₃]
  where
    -- https://www.youtube.com/watch?v=MpKG6FmcIHk
    c₁ ∷ Comparison Fin₅ -- 3 5 4 1 2
    c₁ = listToComparison [2, 4, 3, 0, 1]
    test₁ ∷ Bool
    test₁ = getPredicate lawfulComparison c₁
    test₂ ∷ Bool
    test₂ = getPredicate lawful (cycles c₁)
    test₃ ∷ Bool
    test₃ = (cycles c₁) == toEquivalence ([0 NE.:| [2, 3], 1 NE.:| [4]])
