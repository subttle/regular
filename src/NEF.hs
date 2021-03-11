{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeOperators        #-}

module NEF where

import           Data.Functor.Contravariant (Contravariant (..), Op (..))
import           Data.List (genericDrop)
import           Data.List.NonEmpty as NE (NonEmpty (..))
import           Numeric.Natural.Unicode (ℕ)
import           Common ((⋄))
import           Finite (Finite (..),
                 Fin₁, Fin₂, Fin₃, Fin₄, Fin₅, Fin₆, Fin₇, Fin₈, Fin₉, Fin₁₀, Fin₁₁, Fin₁₂, Fin₁₃, Fin₁₄, Fin₁₅,
                 Quadrant (..), Octant (..), Month (..), DNA (..), Alpha (..),
                 (:🎲),
                 (⚀), (⚁), (⚂), (⚃), (⚄), (⚅),
                 type (🀰),
                 (🀱), (🀲), (🀳), (🀴), (🀵), (🀶), (🀷),
                 (🀸), (🀹), (🀺), (🀻), (🀼), (🀽), (🀾),
                 (🀿), (🁀), (🁁), (🁂), (🁃), (🁄), (🁅),
                 (🁆), (🁇), (🁈), (🁉), (🁊), (🁋), (🁌),
                 (🁍), (🁎), (🁏), (🁐), (🁑), (🁒), (🁓),
                 (🁔), (🁕), (🁖), (🁗), (🁘), (🁙), (🁚),
                 (🁛), (🁜), (🁝), (🁞), (🁟), (🁠), (🁡),
                 type (🁢),
                 (🁣), (🁤), (🁥), (🁦), (🁧), (🁨), (🁩),
                 (🁪), (🁫), (🁬), (🁭), (🁮), (🁯), (🁰),
                 (🁱), (🁲), (🁳), (🁴), (🁵), (🁶), (🁷),
                 (🁸), (🁹), (🁺), (🁻), (🁼), (🁽), (🁾),
                 (🁿), (🂀), (🂁), (🂂), (🂃), (🂄), (🂅),
                 (🂆), (🂇), (🂈), (🂉), (🂊), (🂋), (🂌),
                 (🂍), (🂎), (🂏), (🂐), (🂑), (🂒), (🂓),
                 Card (..), Rank (..), Suit (..),
                 (🂢), (🂲), (🃂), (🃒),
                 (🂣), (🂳), (🃃), (🃓),
                 (🂤), (🂴), (🃄), (🃔),
                 (🂥), (🂵), (🃅), (🃕),
                 (🂦), (🂶), (🃆), (🃖),
                 (🂧), (🂷), (🃇), (🃗),
                 (🂨), (🂸), (🃈), (🃘),
                 (🂩), (🂹), (🃉), (🃙),
                 (🂪), (🂺), (🃊), (🃚),
                 (🂫), (🂻), (🃋), (🃛),
                 (🂭), (🂽), (🃍), (🃝),
                 (🂮), (🂾), (🃎), (🃞),
                 (🂡), (🂱), (🃁), (🃑),
                 Checker (..),
                 (⛀), (⛁), (⛂), (⛃),
                 Init (..), Final (..))
import           NotEmpty (NotEmpty)

-- TODO experimental type class for types which are finite and not empty
class (NotEmpty a, Finite a) ⇒ NEF a where
  asNE ∷ NonEmpty a
  -- FIXME For convenience this can be defined but it is certainly not recommended
  -- FIXME `asNE = NE.fromList asList`
  -- FIXME or something like:
  -- FIMXE `asNE = wit :| genericDrop (1 ∷ ℕ) asList`

instance NEF () where
  asNE ∷ NonEmpty ()
  asNE = () :| []

instance NEF Init where
  asNE = Init () :| []

instance NEF Final where
  asNE = Final () :| []

instance NEF Bool where
  asNE ∷ NonEmpty Bool
  asNE = False :| [True]

instance NEF Ordering where
  asNE ∷ NonEmpty Ordering
  asNE = LT :| [EQ, GT]

instance NEF Quadrant where
  asNE ∷ NonEmpty Quadrant
  asNE = Q₁ :| [Q₂, Q₃, Q₄]

instance NEF Octant where
  asNE ∷ NonEmpty Octant
  asNE = O₁ :| [O₂, O₃, O₄, O₅, O₆, O₇, O₈]

instance NEF Char where
  asNE ∷ NonEmpty Char
  asNE = '\NUL' :| genericDrop (1 ∷ ℕ) (asList @ Char)

instance NEF (:🎲) where
  asNE ∷ NonEmpty (:🎲)
  asNE = (⚀) :| [(⚁), (⚂), (⚃), (⚄), (⚅)]

instance NEF (🁢) where
  asNE ∷ NonEmpty (🁢)
  asNE = (🁣) :| [       (🁤), (🁥), (🁦), (🁧), (🁨), (🁩)
                 , (🁪), (🁫), (🁬), (🁭), (🁮), (🁯), (🁰)
                 , (🁱), (🁲), (🁳), (🁴), (🁵), (🁶), (🁷)
                 , (🁸), (🁹), (🁺), (🁻), (🁼), (🁽), (🁾)
                 , (🁿), (🂀), (🂁), (🂂), (🂃), (🂄), (🂅)
                 , (🂆), (🂇), (🂈), (🂉), (🂊), (🂋), (🂌)
                 , (🂍), (🂎), (🂏), (🂐), (🂑), (🂒), (🂓)
                 ]
instance NEF (🀰) where
  asNE ∷ NonEmpty (🀰)
  asNE = (🀱) :| [        (🀲), (🀳), (🀴), (🀵), (🀶), (🀷)
                  , (🀸), (🀹), (🀺), (🀻), (🀼), (🀽), (🀾)
                  , (🀿), (🁀), (🁁), (🁂), (🁃), (🁄), (🁅)
                  , (🁆), (🁇), (🁈), (🁉), (🁊), (🁋), (🁌)
                  , (🁍), (🁎), (🁏), (🁐), (🁑), (🁒), (🁓)
                  , (🁔), (🁕), (🁖), (🁗), (🁘), (🁙), (🁚)
                  , (🁛), (🁜), (🁝), (🁞), (🁟), (🁠), (🁡)
                  ]
instance NEF Checker where
  asNE ∷ NonEmpty Checker
  asNE = (⛀) :| [(⛁), (⛂), (⛃)]
instance NEF Card where
  asNE ∷ NonEmpty Card
  asNE = (🂢) :| [      (🂲), (🃂), (🃒)
                , (🂣), (🂳), (🃃), (🃓)
                , (🂤), (🂴), (🃄), (🃔)
                , (🂥), (🂵), (🃅), (🃕)
                , (🂦), (🂶), (🃆), (🃖)
                , (🂧), (🂷), (🃇), (🃗)
                , (🂨), (🂸), (🃈), (🃘)
                , (🂩), (🂹), (🃉), (🃙)
                , (🂪), (🂺), (🃊), (🃚)
                , (🂫), (🂻), (🃋), (🃛)
                , (🂭), (🂽), (🃍), (🃝)
                , (🂮), (🂾), (🃎), (🃞)
                , (🂡), (🂱), (🃁), (🃑)
                ]

instance NEF Rank where
  asNE ∷ NonEmpty Rank
  asNE = Two :| [Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace]

instance NEF Suit where
  asNE ∷ NonEmpty Suit
  asNE = Spade :| [Heart, Diamond, Club]

instance NEF DNA where
  asNE ∷ NonEmpty DNA
  asNE = Adenine :| [Cytosine, Guanine, Thymine]

instance NEF Alpha where
  asNE ∷ NonEmpty Alpha
  asNE = A :| [B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z]

instance NEF Month where
  asNE ∷ NonEmpty Month
  asNE = January :| [February, March, April, May, June, July, August, September, October, November, December]

instance NEF Fin₁ where
  asNE ∷ NonEmpty Fin₁
  -- asNE = 0 :| []
  asNE =                                                                pure 0
instance NEF Fin₂ where
  asNE ∷ NonEmpty Fin₂
  -- asNE = 0 :| [1]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₁)  ⋄ pure 1
instance NEF Fin₃ where
  asNE ∷ NonEmpty Fin₃
  -- asNE = 0 :| [1, 2]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₂)  ⋄ pure 2
instance NEF Fin₄ where
  asNE ∷ NonEmpty Fin₄
  -- asNE = 0 :| [1, 2, 3]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₃)  ⋄ pure 3
instance NEF Fin₅ where
  asNE ∷ NonEmpty Fin₅
  -- asNE = 0 :| [1, 2, 3, 4]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₄)  ⋄ pure 4
instance NEF Fin₆ where
  asNE ∷ NonEmpty Fin₆
  -- asNE = 0 :| [1, 2, 3, 4, 5]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₅)  ⋄ pure 5
instance NEF Fin₇ where
  asNE ∷ NonEmpty Fin₇
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₆)  ⋄ pure 6
instance NEF Fin₈ where
  asNE ∷ NonEmpty Fin₈
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₇)  ⋄ pure 7
instance NEF Fin₉ where
  asNE ∷ NonEmpty Fin₉
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₈)  ⋄ pure 8
instance NEF Fin₁₀ where
  asNE ∷ NonEmpty Fin₁₀
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8, 9]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₉)  ⋄ pure 9
instance NEF Fin₁₁ where
  asNE ∷ NonEmpty Fin₁₁
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₁₀) ⋄ pure 10
instance NEF Fin₁₂ where
  asNE ∷ NonEmpty Fin₁₂
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₁₁) ⋄ pure 11
instance NEF Fin₁₃ where
  asNE ∷ NonEmpty Fin₁₃
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₁₂) ⋄ pure 12
instance NEF Fin₁₄ where
  asNE ∷ NonEmpty Fin₁₄
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₁₃) ⋄ pure 13
instance NEF Fin₁₅ where
  asNE ∷ NonEmpty Fin₁₅
  -- asNE = 0 :| [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  asNE = fmap (getOp (contramap fromEnum (Op toEnum))) (asNE @ Fin₁₄) ⋄ pure 14

-- >>> asNE @ (Maybe Void)
-- Nothing :| []
instance (Finite a) ⇒ NEF (Maybe a) where
  asNE ∷ NonEmpty (Maybe a)
  asNE = Nothing :| genericDrop (1 ∷ ℕ) asList

{-
-- FIXME

instance (NEF a, NEF b) ⇒ NEF (a, b) where
  asNE ∷ NonEmpty (a, b)
  asNE = NE.zip (asNE ∷ NonEmpty a) (asNE ∷ NonEmpty b)

instance (NEF a, NEF b, NEF c) ⇒ NEF (a, b, c) where
  asNE ∷ NonEmpty (a, b, c)
  asNE = zip3   (asNE ∷ NonEmpty a) (asNE ∷ NonEmpty b) (asNE ∷ NonEmpty c)
    where
      zip3 ∷ NonEmpty a → NonEmpty b → NonEmpty c → NonEmpty (a, b, c)
      zip3 ~(a :| as) ~(b :| bs) ~(c :| cs) = (a, b, c) :| List.zip3 as bs cs

instance (NEF a, NEF b, NEF c, NEF d) ⇒ NEF (a, b, c, d) where
  asNE ∷ NonEmpty (a, b, c, d)
  asNE = zip4   (asNE ∷ NonEmpty a) (asNE ∷ NonEmpty b) (asNE ∷ NonEmpty c) (asNE ∷ NonEmpty d)
    where
      zip4 ∷ NonEmpty a → NonEmpty b → NonEmpty c → NonEmpty d → NonEmpty (a, b, c, d)
      zip4 ~(a :| as) ~(b :| bs) ~(c :| cs) ~(d :| ds) = (a, b, c, d) :| List.zip4 as bs cs ds

instance (NEF a, NEF b, NEF c, NEF d, NEF e) ⇒ NEF (a, b, c, d, e) where
  asNE ∷ NonEmpty (a, b, c, d, e)
  asNE = zip5   (asNE ∷ NonEmpty a) (asNE ∷ NonEmpty b) (asNE ∷ NonEmpty c) (asNE ∷ NonEmpty d) (asNE ∷ NonEmpty e)
    where
      zip5 ∷ NonEmpty a → NonEmpty b → NonEmpty c → NonEmpty d → NonEmpty e → NonEmpty (a, b, c, d, e)
      zip5 ~(a :| as) ~(b :| bs) ~(c :| cs) ~(d :| ds) ~(e :| es) = (a, b, c, d, e) :| List.zip5 as bs cs ds es
-}
