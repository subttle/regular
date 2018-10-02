# regular (WIP)

For this particular project my priority has been learning Haskell and exploring some formal language theory. It is currently useful for building small automata and regexp, e.g. as a companion for reading papers, doing homework problems, etc.. For now it should be clear that I value correctness and simplicity over speed.

Note well:

The code is not yet structured properly, so expect major refactoring and restructuring. Once I have everything correct I can start to worry about speed. For now this code is SLOW.

I'm patiently (and gratefully!) waiting on a few things from some of the best projects out there right now:

- Labelled graphs in alga
- Easytest from Unison
- Linear types in Haskell
- Better dependent type support in Haskell

I haven't proven all class instances to be lawful yet.

## Example

Here is a small example of what FizzBuzz looks like with DFA:

```Haskell

-- A number, n, either ends in 5 or 0 (when n % 5 = 0), or it doesn't (n % 5 ≠ 0).
by5 ∷ DFA Bool (Fin Nat10)
by5 = DFA { delta = delta
          , q0    = False
          , fs    = singleton True
          } where delta (_, 0) = True
                  delta (_, 5) = True
                  delta _      = False

-- A number is divisible by 3 if and only if the sum of its digits is divisible by 3
-- The state we are in is the (running total % 3)
-- (We add a single starting state `Left ()` to avoid accepting the empty string.)
by3 ∷ DFA (Either () (Fin Nat3)) (Fin Nat10)
by3 = DFA { delta = Right . toEnum . delta
          , q0    = Left ()
          , fs    = singleton (Right 0)
          } where delta (Left  (), digit) = (0          + fromEnum digit) `mod` 3
                  delta (Right  q, digit) = (fromEnum q + fromEnum digit) `mod` 3

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
```
