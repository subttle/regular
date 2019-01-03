import DFA
import Examples
import Common
import Finite
import Config
import Numeric.Natural.Unicode

main'' ∷ IO ()
main'' = mapM_ (\n → putStrLn (fizzbuzz n)) [1 .. 100]
  where fizz ∷ ℕ → Bool
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

main' ∷ IO ()
main' = mapM_ (\n → putStrLn (fizzbuzz n)) [1 .. 100]
      where fizz ∷ ℕ → Bool
            fizz n = accepts  by3                         (toDigits n)
            buzz ∷ ℕ → Bool
            buzz n = accepts                         by5  (toDigits n)
            fbzz ∷ ℕ → Bool
            fbzz n = accepts (by3 `DFA.intersection` by5) (toDigits n)
            fizzbuzz ∷ ℕ → String
            fizzbuzz n
              | fbzz n    = "FizzBuzz"
              | fizz n    = "Fizz"
              | buzz n    = "Buzz"
              | otherwise = show n

main ∷ IO ()
main = mapM_ (putStrLn . fizzbuzz . toDigits) [1 .. 100]
       where fizz = accepts  by3
             buzz = accepts                         by5
             fbzz = accepts (by3 `DFA.intersection` by5)
             fizzbuzz n
               | fbzz n    = "FizzBuzz"
               | fizz n    = "Fizz"
               | buzz n    = "Buzz"
               | otherwise = n >>= show
