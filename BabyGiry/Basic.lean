import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic


open Finset BigOperators

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
      intros _ h
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
  nonnegative := by sorry
  additive := by sorry
  normalized := by sorry

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

lemma prob_and_le_prob_second (μ : random (Bool × Bool)) : Probability (RandomBoolPairAnd μ) ≤ Probability (RandomBoolPairSecond μ) := by sorry

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

notation:10 lhs:10 "|" rhs:11 => (lhs, rhs)  -- notation used for conditional probability (see Examples.lean)
