/-
Copyright (c) 2024 Benedikt Peterseim. All rights reserved.
Author: Benedikt Peterseim
-/
import BabyGiry.Basic

open BabyGiry

-- *First Example: Rolling Dice*

/-! Roll two dice. What's the probability that their total value is nine,
given that the value of the second one is at least two? We can find the answer using:

#eval ℙ[x + y = 9 | x ≥ 2,
  (x, y) ~ (Unif {1, 2, 3, 4, 5, 6}) ⊗ (Unif {1, 2, 3, 4, 5, 6})]
Output: (2 : Rat)/15

The corresponding theorem is now proved "by rfl":
-/
example : ℙ[x + y = 9 | x ≥ 2,
  (x, y) ~ (Unif {1, 2, 3, 4, 5, 6}) ⊗ (Unif {1, 2, 3, 4, 5, 6})]
  = 2/15 := by rfl

-- We can also write this using do notation.
def totalValueIsNine : Random Bool := conditionally do -- Define event "totalValueIsNine" conditionally.
  let x <- Unif {1, 2, 3, 4, 5, 6} -- Roll a die.
  let y <- Unif {1, 2, 3, 4, 5, 6} -- Roll another one.
  return x + y = 9 | x ≥ 2 -- Their total value is nine, given that x is at least two.

example : Probability totalValueIsNine = 2/15 := by rfl

-- *Coprimality of Random Numbers*

def randomNumbersCoprime (n : ℕ) : Random Bool := do
  let x <- Unif (Finset.range n) -- Let x be uniformly distributed on {0, ..., n-1}.
  let y <- Unif (Finset.range n) -- Let y be uniformly distributed on {0, ..., n-1} (independently).
  return Nat.gcd x y = 1 -- The event that x and y are coprime.

-- #eval Probability (randomNumbersCoprime 10)
-- Output: (57 : Rat)/100

-- Draw two numbers between 1 and 100 uniformly at random. The Probability that they are coprime is exactly 57%!
example : Probability (randomNumbersCoprime 10) = 57/100 := by rfl

-- *Birthday Paradox*

-- What's the probability that among three people, two of them were born in the same quarter of the year?
def twoPeopleWithSameQuarterOfBirth : Random Bool := do
  let l <- IID (Unif {1, 2, 3, 4}) 3
  return ∃ i j : (Fin 3), l[i]! = l[j]! ∧ i ≠ j

-- #eval Probability twoPeopleWithSameQuarterOfBirth

theorem BirthdayParadox : Probability twoPeopleWithSameQuarterOfBirth = 5/8 := by rfl

-- *Monty Hall Prolem*

def winCar : Random Bool := conditionally do -- Define event "winCar" conditionally.
  let carDoor <- Unif {1, 2, 3} -- A car is placed uniformly at random behind one of three doors.
  let initialDoor <- Unif {1, 2, 3} -- You choose a door, uniformly at random.
  let montysDoor <- Unif ({1, 2, 3} \ {carDoor, initialDoor}) -- Monty Hall picks a door (neither your initially chosen door, nor the one with the car).
  return carDoor = 2 | initialDoor = 1 ∧ montysDoor = 3 -- The event that the car is behind Door 2 (switching), given that you chose Door 1, and Monty Door 3.

theorem MontyHallProblem : Probability winCar = 2/3 := by rfl

-- *GMAT Example Problem*

/-!
The following problem is taken from a GMAT Quant problem list:

"Theresa is a basketball player practicing her free throws.
On her first free throw, she has a 60% chance of making the basket.
If she has just made a basket on her previous throw,
she has a 80% of making the next basket.
If she has just failed to make a basket on her previous throw,
she has a 40% of making the next basket.
What is the probability that, in five throws,
she will make at least four baskets?"
-/

-- Event that she makes her next throw given that she succeeded/failed on her previous one.
def nextThrow (lastThrowSuccess : Bool) : Random Bool := do
  -- "If she has just made a basket on her previous throw, she has a 80% of making the next basket."
  let nextThrowIfSuccess <- Bernoulli ((8 : ℚ)/10)
  -- "If she has just failed to make a basket on her previous throw, she has a 40% of making the next basket."
  let nextThrowIfFail <- Bernoulli ((4 : ℚ)/10)
  return if lastThrowSuccess then nextThrowIfSuccess else nextThrowIfFail

def FourBasketsInFiveThrows : Random Bool := do
  let firstThrowSuccess <- Bernoulli ((6 : ℚ)/10) -- 6/10 chance on the first free throw.
  let mut numberOfSuccesses := if firstThrowSuccess then 1 else 0 -- Initialise number of baskets.
  let mut CurrentThrowSuccess := firstThrowSuccess
  for _ in [0:4] do -- After her first free throw, there are four more.
    CurrentThrowSuccess <- nextThrow CurrentThrowSuccess
    numberOfSuccesses := if CurrentThrowSuccess then numberOfSuccesses + 1 else numberOfSuccesses
  return numberOfSuccesses ≥ 4 -- Player makes at least four baskets.

-- #eval Probability FourBasketsInFiveThrows
-- Output: (1504 : Rat)/3125
-- This is indeed the correct answer!

-- *Bayesian Inference*

def coinFair : Random Bool := conditionally do
  let p <- Unif {((0 : ℚ)/4), ((1 : ℚ)/4), ((2 : ℚ)/4), ((3 : ℚ)/4), ((4 : ℚ)/4)}
  let observations <- IID (Bernoulli p) 3
  return p = 1/2 | observations = [true, false, false]

-- #eval Probability coinFair
-- 2/5
