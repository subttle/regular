import DFA (intersection)
import Common (toDigits)
import Config (accepts)
import Examples (by3, by5)
import Finite (Fin₁₀)

-- FizzBuzz using DFA
main ∷ IO ()
main = mapM_ (putStrLn . fizzbuzz . toDigits) [1 .. 100]
  where
    fizz ∷ [Fin₁₀] → Bool
    fizz = accepts  by3
    buzz ∷ [Fin₁₀] → Bool
    buzz = accepts                         by5
    fbzz ∷ [Fin₁₀] → Bool
    fbzz = accepts (by3 `DFA.intersection` by5)
    fizzbuzz ∷ [Fin₁₀] → String
    fizzbuzz n | fbzz n    = "FizzBuzz"
               | fizz n    = "Fizz"
               | buzz n    = "Buzz"
               | otherwise = n >>= show
