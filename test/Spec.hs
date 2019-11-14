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
import           EasyTest
import qualified Data.List as List

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
              , testByBisim 101 (by5, DFA.toLanguage by5)
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
testDFAinvhomimage = scope "DFA.invhomimage" . expect $ DFA.invhomimage h slide22 `DFA.equal` expected
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

-- Coinductive bisimulation (partial)
-- Think "observational equality"
-- Either the bisimulation will succeed (up to `n` steps) or
-- it will produce a counter-example to the bisimulation
-- (i.e. a witness to the proof of its negation)
-- basically we take advantage of the fact that both `m` and `l` utilize
-- the same alphabet and we lazily generate the free monoid to be
-- sampled for the first `n` values to be fed in synch
-- to both `m` and `l` to check for acceptance.
testByBisim ∷ forall q s automaton p
            . (Finite q, Finite s, Configuration automaton q s p)
            ⇒ ℕ
            → (automaton q s, ℒ s)
            → Test ()
testByBisim n (m, l) = scope "bisim" . expect $ bisimulates
  where
    bisimulates ∷ Bool
    bisimulates = all snd bisimulation
    bisimulation ∷ [(([s], [s]), Bool)]
    bisimulation = List.unfoldr c bisimulate
      where
        c ∷ [([s], [s])] → Maybe ((([s], [s]), Bool), [([s], [s])])
        c []                = Nothing
        c ((w₁, w₂) : todo) = Just (((w₁, w₂), w₁ == w₂), todo)
    -- FIXME I should check to make sure 
    bisimulate ∷ [([s], [s])]
    bisimulate = List.genericTake n (zip (Config.language m) (Language.language l))

