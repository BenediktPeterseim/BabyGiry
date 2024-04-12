/-
Copyright (c) 2024 Benedikt Peterseim. All rights reserved.
Author: Benedikt Peterseim
-/
import BabyGiry.Basic

open BabyGiry

-- *First Example: Rolling Dice*

-- Roll two dice:
def TwoDice := (Unif {1,..,6}) ⊗ (Unif {1,..,6})

/-! What's the probability that their total value is nine, given that the value of the second one is at least two?
 We can find the answer using:

#eval ℙ[n + m = 9 | n ≥ 2, (n, m) ~ TwoDice]
.>> (2 : Rat)/15

This even gives us a proof:
-/
example : ℙ[n + m = 9 | n ≥ 2, (n, m) ~ TwoDice] = 2/15 := by rfl

-- We can also write this using do notation.
def TotalValue : Random ℕ := randomly do
  let x <-~ Unif {1,..,6} -- Roll a die.
  let y <-~ Unif {1,..,6} -- Roll another one.
  observe <| x ≥ 2
  return x + y

example : ℙ[s = 9 | s ~ TotalValue] = 2/15 := by rfl

-- *Bayesian Inference*

def Posterior : Random ℚ := randomly do
  let p <-~ Unif (Linspace 0 1)
  let k <-~ Binomial 5 p
  observe <| k = 3
  return p

-- #eval ℙ[p ≥ 4/10 ∧ p ≤ 6/10 | p ~ Posterior]
-- >> (1777 : Rat)/3333
-- #eval (1777 : Float)/3333
-- >> 0.533153

example : ℙ[p ≥ 4/10 ∧ p ≤ 6/10 | p ~ Posterior] = 1777/3333 := by rfl

-- *Coprimality of Random Numbers*

-- Draw two numbers between 1 and N uniformly at random.
def TwoNumbers (N := 100):= (Unif {1,..,N}) ⊗ (Unif {1,..,N})

-- The Probability that they are coprime is close to 6/π²!
-- #eval ℙ[gcd n m = 1 | (n, m) ~ TwoNumbers]
-- >> (6087 : Rat)/10000
-- #eval ℙ[gcd n m = 1 | (n, m) ~ TwoNumbers 10]
-- >> (63 : Rat)/100
example : ℙ[gcd n m = 1 | (n, m) ~ TwoNumbers 10] = 63/100 := by rfl

-- *Birthday Paradox*

-- What's the probability that among three people, two of them were born in the same quarter of the year?
-- #eval ℙ[∃ i j : (Fin 3), l[ i ]! = l[ j ]! ∧ i ≠ j | l ~ IID (Unif {1,..,4}) 3]
-- >> (5 : Rat)/8

example : ℙ[∃ i j : (Fin 3), l[i]! = l[j]! ∧ i ≠ j | l ~ IID (Unif {1,..,4}) 3] = 5/8 := by rfl

-- *Monty Hall Prolem*

def Car : Random ℕ := randomly do
  let car <-~ Unif {1, 2, 3}
  let pick := 1
  let goat <-~ Unif ({1, 2, 3} \ {car, pick})
  observe <| goat = 3
  return car

-- #eval ℙ[n = 2 | n ~ Car]
-- >> (2 : Rat)/3

example : ℙ[n = 2 | n ~ Car] = 2/3 := by rfl

-- *GMAT Example Problems*

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

-- Event that she makes her next basket after making her previous one.
def makes_next_basket_after (makes_basket : Bool) : Random Bool := do
  -- "If she has just made a basket on her previous throw, she has a 80% of making the next basket."
  let x <- Bernoulli ((8 : ℚ)/10)
  -- "If she has just failed to make a basket on her previous throw, she has a 40% of making the next basket."
  let y <- Bernoulli ((4 : ℚ)/10)
  return if makes_basket then x else y

def n_baskets : Random ℕ := do
  -- "On her first free throw, she has a 60% chance of making the basket."
  let makes_first_basket <- Bernoulli ((6 : ℚ)/10)
  -- Initialise number of baskets:
  let mut n := if makes_first_basket then 1 else 0
  let mut makes_basket := makes_first_basket
  for _ in [0:4] do -- After her first free throw, she has four more.
    makes_basket <- makes_next_basket_after makes_basket
    n := if makes_basket then n + 1 else n
  return n

-- #eval ℙ[n ≥ 4 | n ~ n_baskets]
-- >> (1504 : Rat)/3125
-- This is the correct answer!

-- If the probability of rain on any given day in City X is 50 percent,
-- what is the probability that it rains on exactly 3 days in a 5-day period?
def RainOnThreeDays : Random Bool := do
  -- The probability of rain is uniform over 5 consecutive days.
  let RainyDays <- IID (Unif {0,1}) 5
  let NumberOfRainyDays := RainyDays.sum -- total number of rainy days.
  return NumberOfRainyDays = 3 -- event that there are exactly 3 rainy days.

-- A fair coin is tossed 4 times. What is the probability of getting at least 2 tails?
def AtLeastTwoTails : Random Bool := do
  let Tails <- IID (Unif {0,1}) 4 -- A fair coin is tossed 4 times.
  let NumberOfTails := Tails.sum -- total numer of tails.
  return NumberOfTails ≥ 2 -- event of getting at least 2 tails.

-- An integer n between 1 and 99, inclusive, is to be chosen at random.
-- What is the probability that n(n+1) will be divisible by 3 ?
def DivisibleByThree : Random Bool := do
  let n <- Unif {1,..,99} -- Pick an integer n between 1 and 99, inclusive, uniformly at random.
  return n * (n+1) % 3 = 0 -- event that n * (n+1) is divisible by 3.

-- A small company employs 3 men and 5 women.
-- If a team of 4 employees is to be randomly selected to organize the company retreat,
-- what is the probability that the team will have exactly 2 women?
def ExactlyThreeWomen : Random Bool := do
  -- There are 3 + 5 = 8 employees. Employees 0,1,2 are men; employees 3,4,5,6,7 are women.
  let Employees := List.range 8
  let Organisers <- Pick 4 Employees -- Four employees are selected at random.
  let WomenOrganisers := Organisers.filter (fun x => x ≥ 3) -- Filter for those which are women.
  return WomenOrganisers.length = 2 -- event that there are exactly two of them.

-- A fair coin is tossed 5 times.
-- What is the probability of getting at least three heads on consecutive tosses?
def AtLeastThreeHeadsOnConsecutiveTosses : Random Bool := do
  let Tosses <- IID (Unif {"heads", "tails"}) 5 -- 0 means tails, 1 means heads.
  let mut NumberOfConsecutiveHeads := 0
  for toss in Tosses do
    if toss = "heads" then
      NumberOfConsecutiveHeads := NumberOfConsecutiveHeads + 1
      if NumberOfConsecutiveHeads = 3 then
        return true
    else
      NumberOfConsecutiveHeads := 0
  return false

-- #eval ℙ[E | E ~ AtLeastThreeHeadsOnConsecutiveTosses]
-- >> 1/4

-- Two dice are tossed once.
-- What is the probability of getting an even number at the first die or a total of 8?
-- (The following code was generated by ChatGPT.)
def TestProblem : Random Bool := do
  let x <- Unif {1,..,6} -- Roll the first die.
  let y <- Unif {1,..,6} -- Roll the second die.
  return x % 2 = 0 || x + y = 8 -- event that either the first die is even or the total is 8.

-- #eval ℙ[E | E ~ TestProblem]
-- >> 5/9
-- Works!

-- The probability is 1/2 that a certain coin will turn up heads on any given toss.
-- If the coin is to be tossed three times,
-- what is the probability that on at least one of the tosses the coin will turn up tails?
-- (This one was also generated using ChatGPT.)
def AtLeastOneTails : Random Bool := do
  let Tosses <- IID (Unif {0,1}) 3 -- Toss the coin three times.
  return Tosses.any (fun toss => toss = 0) -- Event that at least one toss turns up tails.

-- #eval ℙ[E | E ~ AtLeastOneTails]
-- >> 7/8

-- A number cube has six faces numbered 1 through 6.
-- If the cube is rolled twice,
-- what is the probability that at least one of the rolls will result in a number greater than 4?
-- Also generated by GPT.
def AtLeastOneGreaterThanFour : Random Bool := do
  let Roll1 <- Unif {1,..,6} -- Roll the number cube for the first time.
  let Roll2 <- Unif {1,..,6} -- Roll the number cube for the second time.
  return Roll1 > 4 ∨ Roll2 > 4 -- event that at least one roll results in a number greater than 4.

-- #eval ℙ[E | E ~ AtLeastOneGreaterThanFour]
