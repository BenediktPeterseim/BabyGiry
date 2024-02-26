import BabyGiry.Basic

-- *Coprimality of Random Numbers*

def randomNumbersCoprime (n : ℕ) : random Bool := do
  let x <- UniformDist (Finset.range n) -- Let x be uniformly distributed on {0, ..., n-1}.
  let y <- UniformDist (Finset.range n) -- Let y be uniformly distributed on {0, ..., n-1} (independently).
  return Nat.gcd x y = 1 -- The event that x and y are coprime.

-- #eval Probability (randomNumbersCoprime 10)

-- Draw two numbers between 1 and 100 uniformly at random. The Probability that they are coprime is exactly 57%!
theorem coprimeProbability : Probability (randomNumbersCoprime 10) = 57/100 := by rfl

-- *Birthday Paradox*

-- What's the probability that among three people, two of them were born in the same quarter of the year?
def twoPeopleWithSameQuarterOfBirth : random Bool := do
  let l <- IID (UniformDist {1, 2, 3, 4}) 3
  return ∃ i j : (Fin 3), l[i]! = l[j]! ∧ i ≠ j

-- #eval Probability twoPeopleWithSameQuarterOfBirth

theorem BirthdayParadox : Probability twoPeopleWithSameQuarterOfBirth = 5/8 := by rfl

-- *Rolling Dice*

def totalValueIsThree : random Bool := conditionally do -- Define event "totalValueIs3" conditionally.
  let x <- UniformDist {1, 2, 3, 4, 5, 6} -- Roll a die.
  let y <- UniformDist {1, 2, 3, 4, 5, 6} -- Roll another one.
  return x + y = 3 | x % 2 = 1 ∧ y < 5 -- Their total value is three, given that x is odd, and y less than five.

theorem rollingDice : Probability totalValueIsThree = 1/12 := by rfl

-- *Monty Hall Prolem*

def winCar : random Bool := conditionally do -- Define event "winCar" conditionally.
  let carDoor <- UniformDist {1, 2, 3} -- A car is placed uniformly at random behind one of three doors.
  let initialDoor <- UniformDist {1, 2, 3} -- You choose a door, uniformly at random.
  let montysDoor <- UniformDist ({1, 2, 3} \ {carDoor, initialDoor}) -- Monty Hall picks a door (neither your initially chosen door, nor the one with the car).
  return carDoor = 2 | initialDoor = 1 ∧ montysDoor = 3 -- The event that the car is behind Door 2 (switching), given that you chose Door 1, and Monty Door 3.

theorem MontyHallProblem : Probability winCar = 2/3 := by rfl

-- *GMAT Example Problem*

def nextThrow (lastThrowSuccess : Bool) : random Bool := do
  let nextThrowIfSuccess <- Bernoulli ((8 : ℚ)/10)
  let nextThrowIfFail <- Bernoulli ((4 : ℚ)/10)
  return if lastThrowSuccess then nextThrowIfSuccess else nextThrowIfFail

def FourBasketsInFiveThrows : random Bool := do
  let firstThrowSuccess <- Bernoulli ((6 : ℚ)/10) -- 6/10 chance on the first free throw.
  let mut numberOfSuccesses := if firstThrowSuccess then 1 else 0 -- Initialise number of baskets.
  let mut CurrentThrowSuccess := firstThrowSuccess
  for _ in [0:4] do -- After her first free throw, there are four more.
    CurrentThrowSuccess <- nextThrow CurrentThrowSuccess
    numberOfSuccesses := if CurrentThrowSuccess then numberOfSuccesses + 1 else numberOfSuccesses
  return numberOfSuccesses ≥ 4 -- Player makes at least four baskets.

-- #eval (Probability FourBasketsInFiveThrows)
-- 1504/3125
