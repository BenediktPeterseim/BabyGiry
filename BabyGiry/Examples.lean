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
