import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic


open Finset BigOperators

structure FinProb (α : Type) where
  support : Finset α
  mass : support → ℚ  -- probability mass function
  nonnegative : ∀ x : support, mass x ≥ 0
  normalized : ∑ x, mass x = 1


def Coinflip : FinProb Bool where
  support := {true, false}
  mass := fun _ => 1/2
  nonnegative := by
    intro
    simp only [one_div, ge_iff_le, inv_nonneg]
    norm_num
  normalized := by rfl


def BernoulliOld (p : ℚ) (nonneg : 0 ≤ p) (lt_one : p ≤ 1): FinProb Bool where
  support := {true, false}
  mass := fun x => if x then p else 1 - p
  nonnegative := by
    intro x
    fin_cases x
    simp only [ite_true, ge_iff_le]
    exact nonneg
    simp only [ite_false, ge_iff_le, sub_nonneg]
    exact lt_one
  normalized := by
    simp only [univ_eq_attach, attach_insert, mem_image, mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, mem_singleton, exists_prop, exists_eq_left, not_false_eq_true, sum_insert,
      ite_true, forall_true_left, Subtype.forall, Bool.forall_bool, IsEmpty.forall_iff, and_true,
      imp_self, implies_true, and_self, sum_image]
    have h1 : (∑ x in {false}, if x = true then p else 1 - p) = (∑ x in attach {false}, if ↑x = true then p else 1 - p) := rfl
    have h2 : (∑ x in attach {false}, if ↑x = true then p else 1 - p) = 1 - p := by
      rw [←h1]
      simp
    rw [h2]
    simp


-- Observation: For Finset, >>= requires decidable equality.
-- Hence, my definition of FinProb is not well-behaved constructively!
-- Let's try again!

structure random (α : Type) where
  expectation : (α → ℚ) → ℚ  -- expectation functional
  nonnegative : ∀ f : (α → ℚ), f ≥ 0 → expectation f ≥ 0
  additive : ∀ f g : (α → ℚ), expectation (f + g) = expectation f + expectation g
  normalized : expectation (fun _ ↦ 1) = 1

-- Let's try to create a monad instance directly

instance : Monad random where
  pure x := {
    expectation := fun f ↦ f x
    nonnegative := by
      intros f h
      exact h x
    additive := by
      intros f g
      simp
    normalized := rfl
  }
  bind μ f := {
    expectation := fun g ↦ μ.expectation (fun x ↦ (f x).expectation g)
    nonnegative := by
      intros g h
      apply μ.nonnegative
      intro y
      apply (f y).nonnegative
      exact h
    additive := by
      intros g h
      simp only [random.additive]
      apply μ.additive
    normalized := by
      conv =>
        dsimp only
        lhs
        pattern random.expectation (f _) fun _ ↦ 1
        rw [(f x).normalized]
      apply μ.normalized
  }


def UniformDist (support : Finset α) : random α where
  expectation (f : _) := ∑ x in support, (f x) / support.card
  nonnegative := by
    sorry
  additive := by
    sorry
  normalized := by
    sorry


def Bernoulli (p : ℚ) (nonneg : 0 ≤ p) (lt_one : p ≤ 1) : random Bool where
  expectation (f : Bool → ℚ):= p * (f True) + (1-p) * (f False)
  nonnegative := by sorry
  additive := by sorry
  normalized := by sorry


def IID (μ : random α) (n : ℕ) : random (List α) :=
  if n = 0 then
    pure []
  else do
    let l <- IID μ (n -1)
    let x <- μ
    return l.append [x]


def Probability (event : random Bool) : ℚ := event.expectation (fun x ↦ if x then 1 else 0)



-- *-- Examples -----------------------------------------*
-- *-----------------------------------------------------*
-- *A. Probability of one random number dividing another.*

def numberRange : ℕ := 100

def RandomNumberDividesAnother : random Bool := do
  let x <- UniformDist (Finset.range numberRange)
  let y <- UniformDist (Finset.range numberRange)
  return x % y = 0


-- #eval ProbabilityOf RandomNumberDividesAnother

-- *B. Probability that out of 4 people, two have the same month of birth.*

def numberOfPeople := 3

-- What's the probability that among three people, two of them were born in the same quarter of the year?
def twoPeopleWithSameQuarterOfBirth : random Bool := do
  let l <- IID (UniformDist (Finset.range 4)) numberOfPeople
  return ∃ i j : (Fin numberOfPeople), l[i]! = l[j]! ∧ i ≠ j

-- #eval Probability twoPeopleWithSameMonthOfBirth

theorem BirthdayParadox : Probability twoPeopleWithSameQuarterOfBirth = 5/8 := by rfl



-- *Conditionals*


def RandomBoolPairAnd (μ : random (Bool × Bool)) : random Bool := do
  let (p, q) <- μ
  return p ∧ q

def RandomBoolPairSecond (μ : random (Bool × Bool)) : random Bool := do
  let (_ , q) <- μ
  return q

def condProb (μ : random (Bool × Bool)) : ℚ := Probability (RandomBoolPairAnd μ) / Probability (RandomBoolPairSecond μ)

lemma nonneg_of_prob (μ : random Bool) : Probability μ ≥ 0 := by
  apply μ.nonnegative
  simp only [ge_iff_le]
  refine Pi.le_def.mpr ?_
  intro x
  positivity

lemma prob_and_le_prob_second (μ : random (Bool × Bool)) : Probability (RandomBoolPairAnd μ) ≤ Probability (RandomBoolPairSecond μ) := by
  -- apply?
  sorry

lemma nonnegative_of_condProb (μ : random (Bool × Bool)) : condProb μ ≥ 0 := by
  refine LE.le.ge ?h
  apply div_nonneg
  apply nonneg_of_prob
  apply nonneg_of_prob

lemma lt_one_of_condProb (μ : random (Bool × Bool)) : condProb μ ≤ 1 := by
  let a := Probability (RandomBoolPairAnd μ)
  let b := Probability (RandomBoolPairSecond μ)
  have h1 : condProb μ = a / b := rfl
  rw [h1, div_le_one_iff]
  have h2 : a ≤ b := by apply prob_and_le_prob_second
  have h3 : ¬(b < 0) := by simp [nonneg_of_prob]
  simp only [h2, and_true, h3, false_and, or_false]
  refine LE.le.gt_or_eq ?h
  simp only [nonneg_of_prob]


def conditionally (μ : random (Bool × Bool)) : random Bool :=
  Bernoulli (condProb μ) (nonnegative_of_condProb μ) (lt_one_of_condProb μ)


notation:10 lhs:10 "|" rhs:11 => (lhs, rhs)

def Test3 : random Bool := conditionally do
  let x <- UniformDist (Finset.range 6)
  return x = 3 | x % 2 = 1 ∧ x < 5


-- #eval ProbabilityOf Test3

def winCar : random Bool := conditionally do -- Define event "winCar" conditionally.
  let carDoor <- UniformDist (Finset.range 3) -- A car is placed uniformly at random behind one of three doors.
  let initialDoor <- UniformDist (Finset.range 3) -- You choose a door, uniformly at random.
  let montysDoor <- UniformDist ((Finset.range 3) \ {carDoor, initialDoor}) -- Monty Hall picks a door (neither your initially chosen door, nor the one with the car).
  return carDoor = 1 | initialDoor = 0 ∧ montysDoor = 2 -- The event that the car is behind Door 1, given that you chose Door 0, and Monty Door 2.

theorem MontyHallProblem : Probability winCar = 2/3 := by rfl


def tests := random
-- #eval ProbabilityOf winCadillac

-- TODO :
-- 0. Clean up.
-- 1. finish proofs
-- 2. maybe change example A. to ask for coprime-ness?
-- 3. conditioning
-- 3.5 Make abbrev QProb Bool := Event? Rename QProb to Random?
-- 4. implement Bernoulii distribution, random choice, and other "standard examples"
-- 5. Bayesian updating example
