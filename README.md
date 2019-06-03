# regular (WIP)

Type-safe formalisms for representing Regular Languages (Deterministic Finite Automata, Nondeterministic Finite Automata, Regular Expressions, etc.) in Haskell.

## Example

Here is a small example of what FizzBuzz looks like with DFA:

```Haskell

-- A DFA which accepts numbers (as a string of digits) only when
-- they are evenly divisible by 5.
-- Theorem: A number is divisible by 5 iff its last digit is 0 or 5.
by5 ∷ DFA Bool Fin₁₀
by5 = DFA { delta = δ
          , q0    = False
          , fs    = singleton True
          } where δ (_, 0) = True
                  δ (_, 5) = True
                  δ _      = False

-- A DFA which accepts numbers (as a string of digits) only when
-- they are evenly divisible by 3.
-- Theorem: A number is divisible by 3 iff the sum of its digits is divisible by 3.
-- The transition function effectively keeps a running total modulo three by 
-- totaling the numeric value of its current state and the numeric value of the
-- incoming digit, performing the modulo, and then converting that value back to a state.
-- There is a bit of overhead complexity added by the fact that an extra state, `Left ()`,
-- is introduced only to avoid accepting the empty string.
by3 ∷ DFA (Either () Fin₃) Fin₁₀
by3 = DFA { delta = Right . toEnum . (`mod` 3) . \(q, digit) → fromEnum (fromRight 0 q) + fromEnum digit
          , q0    = Left ()
          , fs    = singleton (Right 0)
          }

-- FizzBuzz using DFA
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

## Try

This project currently uses [stack](https://docs.haskellstack.org/en/stable/README/stack) to build. Try out some of the code in the REPL:

```shell

git clone https://github.com/subttle/regular
cd regular
stack build
stack ghci

```

For now it should be clear that I value correctness and simplicity over speed. This is my first ever project in Haskell and it is not yet complete.

The code is not yet structured properly, so expect major refactoring and restructuring. Once I have everything correct I can start to worry about speed. For now this code is slow.

I'm patiently (and gratefully!) waiting on a few things from some of the best projects out there right now:

- Labelled graphs in [alga](https://github.com/snowleopard/alga)
- Linear types in Haskell
- Better dependent type support in Haskell

I haven't proven all class instances to be lawful yet.
