{-# OPTIONS_GHC -Wall                   #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE OverloadedStrings          #-}

import           DFA
-- import qualified NFA
-- import qualified EFA
-- import qualified GFA
-- import qualified RegExp as RE
import           Common
import           Finite
import           Examples
import           Data.Set
import           Config
import           EasyTest

main ∷ IO ()
main = run suite

suite ∷ Test ()
suite = tests [ scope "DFA.empty"     . expect $ Config.language DFA.empty          == ([]   ∷ [[Bool]])
              , scope "DFA.epsilon"   . expect $ Config.language DFA.epsilon        == ([[]] ∷ [[Bool]])
              , scope "DFA.literal"   . expect $ Config.language (DFA.literal True) == [[True]]
              -- https://math.stackexchange.com/questions/871662/finding-right-quotient-of-languages
              , scope "DFA.rquotient" . expect $ and [ Config.accepts e3L1 [C, A, R, R, O, T]
                                                     , Config.accepts e3L2 [T]
                                                     , Config.accepts e3L2 [O, T]
                                                     , Config.accepts e3L1L2 [C, A, R, R, O]
                                                     , Config.accepts e3L1L2 [C, A, R, R]
                                                     , Prelude.take 2 (Config.language e3L1L2) == [[C, A, R, R], [C, A, R, R, O]]
                                                     ]
              , scope "DFA.quotient"  . expect $ minimal `DFA.equal` (quotient minimal) && size' (useful (quotient minimal)) < size' (useful (minimal))
              ]
    where e3L1 ∷ DFA Fin₈ Alpha
          e3L1   = DFA { delta = δ
                        , q0 = 0
                        , fs = singleton 6
                        } where δ (0, C) = 1
                                δ (1, A) = 2
                                δ (2, R) = 3
                                δ (3, R) = 4
                                δ (4, O) = 5
                                δ (5, T) = 6
                                δ _      = 7
          e3L2   = DFA.union (right e3L1 4) (DFA.literal T)
          -- e3L2 = DFA.union (right e3L1 4) (right e3L1 5)
          e3L1L2 = DFA.rquotient e3L1 e3L2
