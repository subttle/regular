module Impossible where

import           Control.Applicative                  (Applicative (..))
import           Control.Comonad
import           Control.Monad                        (ap)
import           Data.Bool                            (bool)
import           Data.Bool.Unicode                    ((∧), (∨))
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible (Divisible (..))
import           Data.Functor                         ((<&>))
import           Data.Function                        (on)
import           Data.Eq.Unicode                      ((≠))
import           Data.Ord.Unicode                     ((≤), (≥))
import           Data.Pointed                         (Pointed (..))
import           Common                               (DisplayColor, implies, (‥), toColor)
import           Finite
import           NatBase  -- import           Numeric.Natural.Unicode        (ℕ)

-- experiments with heavy inspiration from group theory and:
-- http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/
-- http://math.andrej.com/2008/11/21/a-haskell-monad-for-infinite-search-in-finite-time/

newtype Search a = Search { find ∷ Predicate a → a }

-- TODO a lot of this can probably be moved to src/Common.hs

