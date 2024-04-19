/-
Copyright (c) 2024 Benedikt Peterseim. All rights reserved.
Author: Benedikt Peterseim
-/
import BabyGiry.Basic

open BabyGiry

/-!
# A Probability Puzzle.

I flip a fair coin.
If it comes up heads,
I roll two dice and tell you their total value.
Else, I roll one die and tell you its value.
The value I report to you is 5.
What's the probability that the coin came up tails?
-/

/- _First formalisation:_ We first define the joint distribution
of the coin flip and the reported value as the result of the
following trial. -/
def Trial : Random (ℕ × String) := do
  -- I flip a fair coin.
  let coin <- Unif {"heads", "tails"}
  -- If it comes up heads,
  if coin = "heads" then
    -- I roll two dice.
    let x <- Unif {1,..,6}
    let y <- Unif {1,..,6}
    -- In this case, the result of the trial is their total value,
    -- and the result of the coin flip.
    return (x + y, coin)
  -- Else,
  else
    -- I roll one die.
    let x <- Unif {1,..,6}
    -- In this case, the result of the trial is the value of the die,
    -- and the result of the coin flip.
    return (x, coin)

-- We then compute the _conditional probability_.
-- The probability that the coin came up tails,
-- given that the reported value is 5, is:
-- #eval ℙ[coin = "tails" | total = 5, (total, coin) ~ Trial]
-- >> (3 : Rat)/5
example : ℙ[coin = "tails" | total = 5, (total, coin) ~ Trial] = 3/5 := by rfl


/- _Second formalisation:_ We directly define the "conditional event"
using a probabilistic-programming-style `randomly do` notation that
enables us to directly record information using the `observe` statement.-/
def CoinTails : Random Bool := randomly do
  -- I flip a fair coin.
  let coin <-~ Unif {"heads", "tails"}
  -- If it comes up heads,
  if coin = "heads" then
    -- I roll two dice and tell you their total value.
    let x <-~ Unif {1,..,6}
    let y <-~ Unif {1,..,6}
    -- The value I report to you is 5.
    observe (x + y = 5)
  -- Else, I roll one die and tell you its value.
  else
    let x <-~ Unif {1,..,6}
    -- The value I report to you is 5.
    observe (x = 5)
  -- What's the probability that the coin came up tails?
  return coin = "tails"

-- #eval ℙ[tails | tails ~ CoinTails]
-- >> (3 : Rat)/5
example : ℙ[tails | tails ~ CoinTails] = 3/5 := by rfl
