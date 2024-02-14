import BabyGiry.Basic

-- *Coprimality of Random Numbers*

def randomNumbersCoprime (numberRange : ℕ) : random Bool := do
  let x <- UniformDist (Finset.range numberRange) -- Let x be uniformly distributed on {0, ..., numberRange-1}.
  let y <- UniformDist (Finset.range numberRange) -- Let y be uniformly distributed on {0, ..., numberRange-1} (independently).
  return Nat.gcd x y = 1 -- The event that x and y are coprime.

-- #eval Probability (randomNumbersCoprime 10)

-- Draw two numbers between 1 and 100 uniformly at random. The Probability that they are coprime is exactly 57%!
theorem coprimeProbability : Probability (randomNumbersCoprime 10) = 57/100 := by rfl

-- *Birthday Paradox*

-- What's the probability that among three people, two of them were born in the same quarter of the year?
def twoPeopleWithSameQuarterOfBirth : random Bool := do
  let l <- IID (UniformDist (Finset.range 4)) 3
  return ∃ i j : (Fin 3), l[i]! = l[j]! ∧ i ≠ j

-- #eval Probability twoPeopleWithSameMonthOfBirth

theorem BirthdayParadox : Probability twoPeopleWithSameQuarterOfBirth = 5/8 := by rfl

-- *Rolling Dice*

def totalValueIsThree : random Bool := conditionally do -- Define event "totalValueIs3" conditionally.
  let x <- UniformDist (Finset.range 6) -- Roll a die.
  let y <- UniformDist (Finset.range 6) -- Roll another one.
  return x + y = 3 | x % 2 = 1 ∧ y < 5 -- Their total value is three, given that x is odd, and y less than five.

theorem rollingDice : Probability totalValueIsThree = 2/15 := by rfl

-- *Monty Hall Prolem*

def winCar : random Bool := conditionally do -- Define event "winCar" conditionally.
  let carDoor <- UniformDist (Finset.range 3) -- A car is placed uniformly at random behind one of three doors.
  let initialDoor <- UniformDist (Finset.range 3) -- You choose a door, uniformly at random.
  let montysDoor <- UniformDist ((Finset.range 3) \ {carDoor, initialDoor}) -- Monty Hall picks a door (neither your initially chosen door, nor the one with the car).
  return carDoor = 1 | initialDoor = 0 ∧ montysDoor = 2 -- The event that the car is behind Door 1, given that you chose Door 0, and Monty Door 2.

theorem MontyHallProblem : Probability winCar = 2/3 := by rfl
