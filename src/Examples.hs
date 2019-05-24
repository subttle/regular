{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Examples where

import           DFA
import qualified NFA
import qualified EFA
import qualified GFA
import qualified RegExp as RE
-- import qualified PDA
-- import qualified TM
import           Common
import           Finite
import           Data.Set
import           Data.Set.Unicode
import           Data.Bool.Unicode
import           Data.Eq.Unicode
import           Data.Void
import           Data.Maybe
import           Data.Either
import           Data.Functor.Contravariant
import           Data.Fin
import           Data.Type.Nat

-- A DFA which accepts all binary strings ending in 1
endsWith1 ∷ DFA Bool Fin₂
endsWith1 = DFA { delta = delta
                , q0    = False
                , fs    = singleton True
                } where delta (False, 0) = False
                        delta (False, 1) = True
                        delta (True,  0) = False
                        delta (True,  1) = True

-- The set of strings which end in [0, 1]
endsWith01 ∷ NFA.NFA Fin₄ Fin₂
endsWith01 = NFA.NFA { NFA.delta = delta
                     , NFA.q0    = 0
                     , NFA.fs    = singleton 2
                     } where delta ∷ (Fin₄, Fin₂) → Set Fin₄
                             delta (0, 0) = fromList  [0, 1]
                             delta (0, 1) = singleton 0
                             delta (1, 1) = singleton 2
                             delta _      = (∅)

-- https://en.wikipedia.org/wiki/File:NFAexample.svg
-- Generates the language where w has an even number of 0s or an even number of 1s
even0or1 ∷ EFA.EFA Fin₅ Fin₂
even0or1 = EFA.EFA { EFA.delta = delta
                   , EFA.q0    = 0
                   , EFA.fs    = fromList [1, 3]
                   } where delta (0, Nothing) = fromList  [1, 3]
                           delta (1, Just  0) = singleton 2
                           delta (1, Just  1) = singleton 1
                           delta (2, Just  0) = singleton 1
                           delta (2, Just  1) = singleton 2
                           delta (3, Just  0) = singleton 3
                           delta (3, Just  1) = singleton 4
                           delta (4, Just  0) = singleton 4
                           delta (4, Just  1) = singleton 3
                           delta (_, _      ) = (∅)

-- A number is divisible by 5 iff its last digit is 0 or 5
by5 ∷ DFA Bool Fin₁₀
by5 = DFA { delta = delta
          , q0    = False
          , fs    = singleton True
          } where delta (_, 0) = True
                  delta (_, 5) = True
                  delta _      = False

-- A regular expression to match the language of the `by5` DFA
-- [0-9]★[0+5]
-- ((0+(1+(2+(3+(4+(5+(6+(7+(8+9))))))))))★·(0+5)
by5' ∷ RE.RegExp Fin₁₀
by5' = RE.star RE.dot RE.* RE.fromSet (fromList [0, 5])

-- A number is divisible by 3 iff the sum of its digits is divisible by 3
-- The state we are in is the (running total % 3)
-- (We add a single starting state `Left ()` to avoid accepting the empty string.)
by3 ∷ DFA (Either () Fin₃) Fin₁₀
by3 = DFA { delta = Right . toEnum . (`mod` 3) . \(q, digit) → fromEnum (fromRight 0 q) + fromEnum digit
          , q0    = Left ()
          , fs    = singleton (Right 0)
          }

{-          Ross Ashby's "ghost taming" automaton [1]
 (example from "Synchronizing automata and the Černý conjecture" [2])
 "In each minute, each noise is either sounding or silent—
they show no degrees. What each will do during the ensuing
minute depends, in the following exact way, on what
has been happening during the preceding minute:

The Singing, in the succeeding minute, will go on as it was
during the preceding minute (sounding or silent) unless there
was organ-playing with no Laughter, in which case it will
change to the opposite (sounding to silent, or vice versa).

As for the Laughter, if there was incense burning, then it
will sound or not according as the Singing was sounding or
not (so that the Laughter copies the Singing a minute later).
If however there was no incense burning, the Laughter will
do the opposite of what the Singing did.
At this minute of writing, the Laughter and Singing are
troth sounding. Please tell me what manipulations of
incense and organ I should make to get the house quiet, and
to keep it so"
[1] An Introduction to Cybernetics, W. Ross Ashby, 1956, pg 60-61
[2] http://csseminar.kadm.usu.ru/tarragona_volkov2008.pdf                      -}

-- Ghosts:  Singing and Laughing
newtype Sing    = Sing    Bool deriving (Eq, Ord, Enum, Bounded)
newtype Laugh   = Laugh   Bool deriving (Eq, Ord, Enum, Bounded)
-- Actions: play organ, light incense
newtype Organ   = Organ   Bool deriving (Eq, Ord, Enum, Bounded)
newtype Incense = Incense Bool deriving (Eq, Ord, Enum, Bounded)
instance Finite Sing
instance Finite Laugh
instance Finite Organ
instance Finite Incense
instance Show Sing where
  show (Sing      True) = "Singing"
  show (Sing     False) = "Not Singing"
instance Show Laugh where
  show (Laugh     True) = "Laughing"
  show (Laugh    False) = "Not Laughing"
instance Show Organ where
  show (Organ     True) = "Playing organ"
  show (Organ    False) = "Not playing organ"
instance Show Incense where
  show (Incense   True) = "Burning incense"
  show (Incense  False) = "Not burning incense"

haunted ∷ DFA (Sing, Laugh) (Organ, Incense)
haunted = DFA { delta = delta
              , q0    =           (Sing  True, Laugh  True)
              , fs    = singleton (Sing False, Laugh False)
              } where delta ((Sing singing, Laugh laughing), (Organ organ, Incense incense)) = (left, right)
                                                         where left  = Sing  ((if not laughing ∧ organ then not else  id) singing)
                                                               right = Laugh ((if incense              then id  else not) singing)

-- Farmer's problem
-- The goal of the problem is to get all the items safely and efficiently to the opposite
-- side of the river. The farmer may carry at most one item across at a time.
-- ...
-- Each type wraps a Bool which when True stands for "is across the river" and
-- when False stands for "is not across the river".
-- The states are the locations of the person, the fox, the hen, and the bag. Each one may be either across or not across the river.
-- The symbols are transitions across the river, either the person by themself, or one of fox, hen, or bag (accompanied by the person).
data Objects = Per | Fox | Hen | Bag deriving (Eq, Ord, Enum, Bounded, Show)
instance Finite Objects where
  asList = [Per, Fox, Hen, Bag]

-- The states are the locations of the person, the fox, the hen, and the bag. Each one may be either left of the river or right of the river.
-- The symbols are transitions, either the person by themself, or one of animals, accompanied by the person
farmer ∷ DFA (Bool, Bool, Bool, Bool) Objects
farmer = DFA { delta = δ
             , q0    =           (False, False, False, False)  -- Everything starts not across the river
             , fs    = singleton (True,  True,  True,  True )  -- We are finished when everything is safely across the river
             } where -- foxEatsHen = p ≠ f ∧ f == h -- If the fox and the hen are on the same side and the person isn't watching the fox, then the hen gets eaten.
                     -- henEatsBag = p ≠ h ∧ h == b -- If the hen and the bag are on the same side and the person isn't watching the hen, then the bag gets eaten.
                     -- illegal x  = p ≠ x          -- only allow x to transition with the farmer
                     δ ((p, f, h, b), Per) = if         (p ≠ f ∧ f == h) ∨ (p ≠ h ∧ h == b) then (p, f, h, b) else (not p,     f,     h,     b)
                     δ ((p, f, h, b), Fox) = if p ≠ f ∨                    (p ≠ h ∧ h == b) then (p, f, h, b) else (not p, not f,     h,     b)
                     δ ((p, f, h, b), Hen) = if p ≠ h ∨ (p ≠ f ∧ f == h)                    then (p, f, h, b) else (not p,     f, not h,     b)
                     δ ((p, f, h, b), Bag) = if p ≠ b ∨ (p ≠ f ∧ f == h) ∨ (p ≠ h ∧ h == b) then (p, f, h, b) else (not p,     f,     h, not b)

-- Wikipedia version of the riddle
-- https://en.wikipedia.org/wiki/Fox,_goose_and_bag_of_beans_puzzle
-- https://en.wikipedia.org/wiki/File:Fox_goose_beans_puzzle_visualisation.svg
farmerw ∷ NFA.NFA (Bool, Bool, Bool) Objects
farmerw = NFA.NFA { NFA.delta = δ
                  , NFA.q0    =           (False, False, False)  -- Everything starts not across the river
                  , NFA.fs    = singleton (True,  True,  True )  -- We are finished when everything is safely across the river
                  } where
                          -- fgb
                          δ ((False, False, False), Hen) = singleton (False, True,  False)
                          -- fGb
                          δ ((False, True,  False), Fox) = singleton (True,  True,  False)
                          δ ((False, True,  False), Bag) = singleton (False, True,  True)
                          -- FGb
                          δ ((True,  True,  False), Hen) = singleton (True,  False, False)
                          -- Fgb
                          δ ((True,  False, False), Bag) = singleton (True,  False, True)
                          -- FgB
                          δ ((True,  False, True),  Bag) = singleton (True,  False, False)
                          δ ((True,  False, True),  Hen) = singleton (True,  True,  True)
                          δ ((True,  False, True),  Fox) = singleton (False, False, True)
                          -- fGB
                          δ ((False, True,  True),  Hen) = singleton (False, False, True)
                          -- fgB
                          δ ((False, False, True),  Fox) = singleton (True,  False, True)
                          δ _                            = (∅)

-- https://www.researchgate.net/publication/269628569_DNA_Pattern_Analysis_using_Finite_Automata
figure2 ∷ NFA.NFA Fin₈ DNA
figure2 = NFA.NFA { NFA.delta = δ
                  , NFA.q0    = 0
                  , NFA.fs    = singleton 7
                  } where δ (0, Adenine)  = singleton  6
                          δ (0, Cytosine) = singleton  3
                          δ (0, Thymine)  = singleton  3
                          δ (0, Guanine)  = fromList  [1, 3, 6]
                          δ (1, Adenine)  = fromList  [2, 5]
                          δ (1, Cytosine) = fromList  [1, 3]
                          δ (1, Thymine)  = singleton  5
                          δ (1, Guanine)  = fromList  [2, 5]
                          δ (2, Guanine)  = (∅)
                          δ (2, _)        = singleton  7
                          δ (3, Cytosine) = fromList  [3, 7]
                          δ (3, Thymine)  = fromList  [3, 4, 7, 1]
                          δ (3, _)        = fromList  [4, 7]
                          δ (4, Guanine)  = singleton  7
                          δ (4, _)        = fromList  [2, 7]
                          δ (5, _)        = singleton  7
                          δ (6, Thymine)  = fromList  [2, 7]
                          δ (6, Guanine)  = singleton  7
                          δ (6, _)        = fromList  [6, 7]
                          δ (7, _)        = (∅)

-- Generates the language [[1], [2], [3]]
oneTwoThree ∷ EFA.EFA Bool Fin₄
oneTwoThree = EFA.EFA { EFA.delta = delta
                      , EFA.q0    = False
                      , EFA.fs    = singleton True
                      } where delta (False, Just 1) = singleton True
                              delta (False, Just 2) = singleton True
                              delta (False, Just 3) = singleton True
                              delta _               = (∅)

-- An EFA which accepts only strings which start with 0 and end with 1
-- A similar example is given in this video lecture https://youtu.be/yzb4J7oSyLA
startsWith0endsWith1 ∷ EFA.EFA Fin₄ Fin₂
startsWith0endsWith1 = EFA.EFA { EFA.delta = delta
                               , EFA.q0    = 0
                               , EFA.fs    = singleton 2
                               } where delta (0, Just  0) = singleton 1
                                       delta (0, Just  1) = singleton 3

                                       delta (1, Just  0) = singleton 1
                                       delta (1, Just  1) = singleton 2

                                       delta (2, Just  0) = singleton 1
                                       delta (2, Just  1) = singleton 2

                                       delta (3, Just  0) = singleton 3
                                       delta (3, Just  1) = singleton 3
                                       delta (_, Nothing) = (∅)

-- A DFA which accepts all binary strings starting with 0
startsWith0 ∷ DFA Fin₃ Fin₂
startsWith0 = DFA { delta = delta
                  , q0    = 0
                  , fs    = singleton 1
                  } where delta (0, 0) = 1
                          delta (0, 1) = 2

                          delta (1, 0) = 1
                          delta (1, 1) = 1

                          delta (2, 0) = 2
                          delta (2, 1) = 2

-- Coursera Stanford Automata, NFA lecture
-- http://spark-public.s3.amazonaws.com/automata/slides/4_fa3.pdf
data RB = Red | Black deriving (Eq, Enum, Ord, Bounded, Show)
instance Finite RB
board ∷ NFA.NFA Fin₉ RB
board = NFA.NFA { NFA.delta = delta
                , NFA.q0    = 0
                , NFA.fs    = singleton 8
                } where delta (0,   Red) = fromList  [1, 3]
                        delta (0, Black) = singleton  4
                        delta (1,   Red) = fromList  [3, 5]
                        delta (1, Black) = fromList  [0, 2, 4]
                        delta (2,   Red) = fromList  [1, 5]
                        delta (2, Black) = singleton  4
                        delta (3,   Red) = fromList  [1, 7]
                        delta (3, Black) = fromList  [0, 4, 6]
                        delta (4,   Red) = fromList  [1, 3, 5, 7]
                        delta (4, Black) = fromList  [0, 2, 6, 8]
                        delta (5,   Red) = fromList  [1, 7]
                        delta (5, Black) = fromList  [2, 4, 8]
                        delta (6,   Red) = fromList  [3, 7]
                        delta (6, Black) = singleton  4
                        delta (7,   Red) = fromList  [3, 5]
                        delta (7, Black) = fromList  [4, 6, 8]
                        delta (8,   Red) = fromList  [5, 7]
                        delta (8, Black) = singleton  4

data Decimal = Plus | Minus | Period deriving (Eq, Ord, Enum, Bounded)
instance Finite Decimal
instance Show Decimal where
  show Plus   = "+"
  show Minus  = "-"
  show Period = "."

-- HMU Figure 2.18 Pg.73
hmu218 ∷ EFA.EFA Fin₆ (Either Decimal Fin₁₀)
hmu218 = EFA.EFA { EFA.delta = delta
                 , EFA.q0    = 0
                 , EFA.fs    = singleton 5
                 } where delta (0, Just (Left   Plus)) = singleton 1
                         delta (0, Just (Left  Minus)) = singleton 1
                         delta (0,            Nothing) = singleton 1
                         delta (1, Just (Left Period)) = singleton 2
                         delta (1, Just (Right     _)) = fromList  [1, 4]
                         delta (2, Just (Right     _)) = singleton 3
                         delta (3, Just (Right     _)) = singleton 3
                         delta (3,            Nothing) = singleton 5
                         delta (4, Just (Left Period)) = singleton 3
                         delta  _                      = (∅)

-- [[0],[1],[0,1],[0,0,0],[0,1,1],[1,1,1]
ex144 ∷ EFA.EFA Fin₆ Fin₂
ex144 = EFA.EFA { EFA.delta = delta
                , EFA.q0    = 0
                , EFA.fs    = singleton 3
                } where delta (0, Just  0) = singleton 4
                        delta (0, Just  1) = singleton 1
                        delta (1, Just  1) = singleton 2
                        delta (1, Nothing) = singleton 3
                        delta (2, Just  1) = singleton 3
                        delta (4, Just  0) = singleton 5
                        delta (4, Nothing) = fromList  [1, 2]
                        delta (5, Just  0) = singleton 3
                        delta _            = (∅)

closuresExample ∷ EFA.EFA Fin₇ Fin₂
closuresExample = EFA.EFA { EFA.delta = delta
                          , EFA.q0 = 0
                          , EFA.fs = singleton 3
                          } where delta (0, Nothing) = fromList  [1, 2]
                                  delta (1, Just  1) = singleton 4
                                  delta (1, Nothing) = singleton 3
                                  delta (2, Just  0) = singleton 6
                                  delta (2, Nothing) = singleton 5
                                  delta (5, Nothing) = singleton 0
                                  delta _            = (∅)

-- https://youtu.be/1GZOzTJOBuM
minimal ∷ DFA Fin₅ Fin₂
minimal = DFA { delta = delta
              , q0    = 0
              , fs    = singleton 4
              } where delta (0, 0) = 1
                      delta (0, 1) = 2
                      delta (1, 0) = 1
                      delta (1, 1) = 3
                      delta (2, 0) = 1
                      delta (2, 1) = 2
                      delta (3, 0) = 1
                      delta (3, 1) = 4
                      delta (4, 0) = 1
                      delta (4, 1) = 2

-- https://youtu.be/TvMEX2htBYw
minimal' ∷ DFA Fin₁₀ Fin₂
minimal' = DFA { delta = delta
               , q0    = 0
               , fs    = fromList [5, 6]
               } where delta (0, 0) = 7
                       delta (0, 1) = 1
                       delta (1, 0) = 7
                       delta (1, 1) = 0
                       delta (2, 0) = 4
                       delta (2, 1) = 5
                       delta (3, 0) = 4
                       delta (3, 1) = 5
                       delta (4, 0) = 6
                       delta (4, 1) = 6
                       delta (5, 0) = 5
                       delta (5, 1) = 5
                       delta (6, 0) = 6
                       delta (6, 1) = 5
                       delta (7, 0) = 2
                       delta (7, 1) = 2
                       delta _      = 9

-- http://i.stack.imgur.com/AD6WJ.png
exactly20s ∷ DFA Fin₄ Fin₂
exactly20s = DFA { delta = delta
                 , q0    = 0
                 , fs    = singleton 2
                 } where delta (0, 0) = 1
                         delta (0, 1) = 0

                         delta (1, 0) = 2
                         delta (1, 1) = 1

                         delta (2, 0) = 3
                         delta (2, 1) = 2

                         delta (3, 0) = 3
                         delta (3, 1) = 3

-- http://i.stack.imgur.com/AD6WJ.png
atleast21s ∷ DFA Fin₃ Fin₂
atleast21s = DFA { delta = delta
                 , q0    = 0
                 , fs    = singleton 2
                 } where delta (0, 0) = 0
                         delta (0, 1) = 1

                         delta (1, 0) = 1
                         delta (1, 1) = 2

                         delta (2, 0) = 2
                         delta (2, 1) = 2

exactly20sANDatleast21s ∷ DFA (Fin₄, Fin₃) Fin₂
exactly20sANDatleast21s  = exactly20s `DFA.intersection` atleast21s

-- The language ["123456789"]
digitsNFA ∷ NFA.NFA Fin₁₀ Fin₁₀
digitsNFA = NFA.NFA { NFA.delta = delta
                    , NFA.q0 = 0
                    , NFA.fs = singleton 9
                    } where delta (0, 1) = singleton 1
                            delta (1, 2) = singleton 2
                            delta (2, 3) = singleton 3
                            delta (3, 4) = singleton 4
                            delta (4, 5) = singleton 5
                            delta (5, 6) = singleton 6
                            delta (6, 7) = singleton 7
                            delta (7, 8) = singleton 8
                            delta (8, 9) = singleton 9
                            delta _      = (∅)

{-
data StackSym = X0 | Y0 deriving (Eq, Ord, Enum, Bounded, Show)

-- The standard PDA example language {L : 0ⁿ1ⁿ for n > 0 }
-- {"01","0011","000111","00001111","0000011111","000000111111","00000001111111","0000000011111111", ...}
example ∷ PDA.PDA Fin₃ (Either () StackSym) Fin₂
example = PDA.PDA { PDA.delta = delta
                  , PDA.q0    = Fin₃ 0
                  , PDA.z0    = Left ()
                  , PDA.fs    = singleton (Fin₃ 2)
                  } where delta (Fin₃ 0, Just 0,  Left  ()) = singleton (Fin₃ 0, [Right X0, Left  ()])
                          delta (Fin₃ 0, Just 0,  Right X0) = singleton (Fin₃ 0, [Right X0, Right X0])
                          delta (Fin₃ 0, Just 1,  Right X0) = singleton (Fin₃ 1, [                  ])
                          delta (Fin₃ 1, Just 1,  Right X0) = singleton (Fin₃ 1, [                  ])
                          delta (Fin₃ 1, Nothing, Left  ()) = singleton (Fin₃ 2, [           Left ()])
                          delta _                           = (∅)

-- https://en.wikipedia.org/wiki/Pushdown_automaton#Example
-- https://en.wikipedia.org/wiki/Pushdown_automaton#/media/File:Pda-example.svg
-- The standard PDA example language {L : 0ⁿ1ⁿ | n ≥ 0 }
-- "", "01","0011","000111","00001111","0000011111","000000111111","00000001111111","0000000011111111", ...
wiki ∷ PDA.PDA Fin₃ Fin₂ Fin₂
wiki = PDA.PDA { PDA.delta = delta
               , PDA.q0 = 0
               , PDA.z0 = 1
               , PDA.fs = singleton 2
               } where delta (0, Just  0, 1) = singleton (0, [0, 1])
                       delta (0, Just  0, 0) = singleton (0, [0, 0])
                       delta (0, Nothing, 1) = singleton (1, [   1])
                       delta (0, Nothing, 0) = singleton (1, [   0])
                       delta (1, Just  1, 0) = singleton (1, [    ])
                       delta (1, Nothing, 1) = singleton (2, [   1])
                       delta _               = (∅)

-- wwʳ (or "w then w-reversed"), even length palindromes
-- 62, Page 230, HMU 3rd Edition
wwʳ ∷ PDA.PDA Fin₃ (Either () Bool) Fin₂
wwʳ = PDA.PDA { PDA.delta = δ
              , PDA.q0    = 0
              , PDA.z0    = Left ()
              , PDA.fs    = singleton 2
              } where δ (0, Just  0, Left     ()) = singleton (0, [Right False, Left     ()])
                      δ (0, Just  0, Right False) = singleton (0, [Right False, Right False])
                      δ (0, Just  0, Right  True) = singleton (0, [Right False, Right  True])
                      δ (0, Just  1, Left     ()) = singleton (0, [Right  True, Left     ()])
                      δ (0, Just  1, Right False) = singleton (0, [Right  True, Right False])
                      δ (0, Just  1, Right  True) = singleton (0, [Right  True, Right  True])
                      δ (0, Nothing, Left     ()) = singleton (1, [             Left     ()])
                      δ (0, Nothing, Right False) = singleton (1, [             Right False])
                      δ (0, Nothing, Right  True) = singleton (1, [             Right  True])
                      δ (1, Just  0, Right False) = singleton (1, [                        ])
                      δ (1, Just  1, Right  True) = singleton (1, [                        ])
                      δ (1, Nothing, Left     ()) = singleton (2, [             Left     ()])
                      δ _                         = (∅) -- otherwise kill the computation

data LP = LParen deriving (Enum, Eq, Ord, Bounded)
instance Show LP where
  show _ = "("
data RP = RParen deriving (Enum, Eq, Ord, Bounded)
instance Show RP where
  show _ = ")"
instance Finite LP
instance Finite RP
-- http://www.eecs.wsu.edu/~ananth/CptS317/Lectures/PDA.pdf
-- Accepts by empty stack, still works accepting by final state, but includes epsilon
-- fmap (>>= (either show show)) (take 10 $ PDA.language balanced)
-- ["","()","(())","()()","((()))","(()())","(())()","()(())","()()()","(((())))"]
balanced ∷ PDA.PDA Bool (Either () LP) (Either LP RP)
balanced = PDA.PDA { PDA.delta = delta
                   , PDA.q0    = False
                   , PDA.z0    = Left ()
                   , PDA.fs    = singleton True
                   } where delta (False, Just (Left  LParen), Left      ()) = singleton (False, [Right LParen, Left      ()])
                           delta (False, Just (Left  LParen), Right LParen) = singleton (False, [Right LParen, Right LParen])
                           delta (False, Just (Right RParen), Right LParen) = singleton (False, [                          ])
                           delta (False,             Nothing, Left      ()) = singleton (True,  [              Left      ()])
                           delta _                                          = (∅)
-}
{-
-- Example from Stanford Automata course, the "Turing Machines" lecture
-- Stanford Automata lecture 4 - 4 - 16, "Turing Machines"
exampleTM ∷ TM.TM Bool Fin₂ Void
exampleTM = TM.TM { TM.delta = delta
                  , TM.q0    = False
                  , TM.fs    = singleton True
                  } where delta (False, Left  0      ) = Just (False, Left 0, TM.R')
                          delta (False, Left  1      ) = Just ( True, Left 0, TM.R')
                          delta (False, Right Nothing) = Just (False, Left 1, TM.L')
                          delta _                      = Nothing  -- Halt

-- HMU pg 329, Figure 8.9
-- { 0ⁿ1ⁿ | n ≥ 1 }
hmu89 ∷ TM.TM Fin₆ Fin₂ StackSym
hmu89 = TM.TM { TM.delta = delta
              , TM.q0    = 0
              , TM.fs    = singleton 4
              } where delta (0, Left  0        ) = Just (1, Right (Just X0), TM.R')
                      delta (0, Right (Just Y0)) = Just (3, Right (Just Y0), TM.R')
                      delta (1, Left  0        ) = Just (1, Left  0,         TM.R')
                      delta (1, Left  1        ) = Just (2, Right (Just Y0), TM.L')
                      delta (1, Right (Just Y0)) = Just (1, Right (Just Y0), TM.R')
                      delta (2, Left  0        ) = Just (2, Left  0,         TM.L')
                      delta (2, Right (Just X0)) = Just (0, Right (Just X0), TM.R')
                      delta (2, Right (Just Y0)) = Just (2, Right (Just Y0), TM.L')
                      delta (3, Right (Just Y0)) = Just (3, Right (Just Y0), TM.R')
                      delta (3, Right Nothing  ) = Just (4, Right Nothing,   TM.R')
                      delta _                    = Nothing


-- TODO accepts by halting, create a new data type without fs?
{-
So the successor’s output on 111101 was 000011 which is the reverse binary representation of 48.
www.cs.columbia.edu/~zeph/3261/L14/TuringMachine.pdf   L14
-}
successor ∷ TM.TM Bool Fin₂ Void
successor = TM.TM { TM.delta = delta
                  , TM.q0    = False
                  , TM.fs    = singleton True
                  } where delta (False, Left  0      ) = Just ( True, Left  1, TM.R')
                          delta (False, Left  1      ) = Just (False, Left 0, TM.R')
                          delta (False, Right Nothing) = Just ( True, Left  1, TM.R')
                          delta _                      = Nothing
-}
