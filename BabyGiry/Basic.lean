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

def UniformDist -- Thanks to Matt Diamond for adding nonemptyness assumption and filling in sorries.
  [Inhabited α]
  (support : Finset α)
  : random α
where
  expectation (f : _) := if support.Nonempty then ∑ x in support, (f x) / support.card else f default
  nonnegative := by
    intros f hf
    refine ite_nonneg ?ha (hf default)
    apply sum_nonneg
    intros i _
    exact div_nonneg (hf i) (Nat.cast_nonneg _)
  additive := by
    intros f g
    simp_all
    split_ifs with support_nonempty
    · have : (support.card : ℚ) ≠ 0 :=
      by simpa using support_nonempty.card_pos.ne'
      simp_rw [← sum_div, div_add_div_same, div_left_inj' this]
      exact sum_add_distrib
    · simp only
  normalized := by
    beta_reduce
    split_ifs with support_nonempty
    · have : (support.card : ℚ) ≠ 0 :=
      by simpa using support_nonempty.card_pos.ne'
      rw [one_div, sum_const, nsmul_eq_mul]
      exact Rat.mul_inv_cancel _ this
    · simp only

def Bernoulli (p : ℚ) (nonneg : 0 ≤ p) (lt_one : p ≤ 1) : random Bool where
  expectation (f : Bool → ℚ):= p * (f True) + (1-p) * (f False)
  nonnegative := by
    intro f hf
    simp only [decide_True, decide_False, ge_iff_le]
    have h1 : 0 ≤ (1-p) := by linarith
    have h2 : 0 ≤ f true := by apply hf
    have h3 : 0 ≤ f false := by apply hf
    positivity
  additive := by
    intros f g
    simp only [decide_True, Pi.add_apply, decide_False]
    ring
  normalized := by ring

def IID (μ : random α) (n : ℕ) : random (List α) :=
  if n = 0 then
    pure []
  else do
    let l <- IID μ (n - 1)
    let x <- μ
    return l.append [x]

def Probability (event : random Bool) : ℚ := event.expectation (fun x ↦ if x then 1 else 0)

noncomputable
def indicator (A : Set α) (x : α) : ℚ :=
  --have : Decidable (A x) := Classical.dec (A x)
  --if A x then 1 else 0
  Set.indicator (M := ℚ) A (fun _ ↦ 1) x

-- #check Set.indicator (M := ℚ)

lemma indicator_of_disjoint_union
  (A B : Set α)
  (disjoint : A ∩ B = ∅)
  : indicator (A ∪ B) = indicator A + indicator B :=
by
  unfold indicator
  rw [Set.indicator_union_of_disjoint]
  · simp_all only
    apply Eq.refl
  · exact Set.disjoint_iff_inter_eq_empty.mpr disjoint

def Law (μ : random α) (p : α → Bool) : ℚ := μ.expectation (fun x ↦ if p x then 1 else 0)

-- A version of Law ignoring decidability.
noncomputable
def Law' (μ : random α) (A : Set α) : ℚ :=
  -- have (x : α) : Decidable (A x) := Classical.dec (A x)
  μ.expectation (Set.indicator (M := ℚ) A (fun _ ↦ 1))

lemma Law'_eq_Law (μ : random α) (p : α → Bool) : Law μ p = Law' μ {x | p x} := by
  have h : (fun x ↦ if p x then 1 else 0) = (Set.indicator (M := ℚ) {x | p x} (fun _ ↦ 1)) := by aesop
  unfold Law
  rw [h]
  rfl

lemma Law'_nonneg (μ : random α) (A : Set α) : 0 ≤ Law' μ A := by
  apply μ.nonnegative
  simp
  have h0 (x : α) : Set.indicator (M := ℚ) A (fun _ ↦ 1) x = 0 ∨ Set.indicator (M := ℚ) A (fun _ ↦ 1) x = (fun _ ↦ 1) x := by
    apply Set.indicator_eq_zero_or_self
  change ∀ x : α, 0 ≤ Set.indicator A (fun _ ↦ 1) x
  intro x
  have h1 : Set.indicator (M := ℚ) A (fun _ ↦ 1) x = 0 ∨ Set.indicator (M := ℚ) A (fun _ ↦ 1) x = 1 := by apply h0
  cases h1 with
  | inl h => positivity
  | inr h => positivity

lemma Law'_additive
  (μ : random α)
  (A B : Set α)
  (disjoint : A ∩ B = ∅)
  : Law' μ (A ∪ B) = Law' μ A + Law' μ B :=
by
  change μ.expectation (indicator (A ∪ B)) = Law' μ A + Law' μ B
  rw [indicator_of_disjoint_union, μ.additive]
  rfl
  exact disjoint

lemma Law'_monotone
  (μ : random α)
  (A B : Set α)
  (A_subseteq_B : A ⊆ B)
  : Law' μ A ≤ Law' μ B :=
by
  have h : A ∪ (B \ A) = B := by
    simp only [Set.union_diff_self, Set.union_eq_right]
    exact A_subseteq_B
  rw [←h]
  have disjoint : A ∩ (B \ A) = ∅ := by simp
  rw [Law'_additive]
  simp
  apply Law'_nonneg
  exact disjoint

lemma Law'_univ_eq_one (μ : random α) : Law' μ Set.univ = 1 := by
  unfold Law'
  simp only [Set.indicator_univ]
  apply μ.normalized

lemma Law'_lt_one (μ : random α) (A : Set α) : Law' μ A ≤ 1 := by
  rw [←Law'_univ_eq_one μ]
  apply Law'_monotone
  simp_all only [Set.subset_univ]

lemma Law_nonneg (μ : random α) (p : α → Bool) : Law μ p ≥ 0 := by
  rw [Law'_eq_Law]
  apply Law'_nonneg

lemma Law_lt_one (μ : random α) (p : α → Bool) : Law μ p ≤ 1 := by
  rw [Law'_eq_Law]
  apply Law'_lt_one

lemma Law_monotone (μ : random α) (p q : α → Bool) (p_lt_q : p ≤ q) : Law μ p ≤ Law μ q := by
  rw [Law'_eq_Law]
  rw [Law'_eq_Law]
  apply Law'_monotone
  assumption

-- *Conditionals*

def CondLaw (μ : random α) (p : α → Bool) (q : α → Bool) : ℚ := Law μ (fun x ↦ (p x ∧ q x)) / Law μ q

lemma CondLaw_nonneg (μ : random α) (p : α → Bool) (q : α → Bool) : CondLaw μ p q ≥ 0 := by
  apply div_nonneg
  apply Law_nonneg
  apply Law_nonneg

lemma CondLaw_and_lt_proj
  (μ : random α) (p : α → Bool) (q : α → Bool)
  : Law μ (fun x ↦ (p x ∧ q x)) ≤ Law μ q :=
by
  apply Law_monotone
  refine Pi.le_def.mpr ?p_lt_q.a
  intro x
  simp only [Bool.decide_and, Bool.decide_coe]
  exact Bool.and_le_right (p x) (q x)

lemma CondLaw_lt_one (μ : random α) (p : α → Bool) (q : α → Bool) : CondLaw μ p q ≤ 1 := by
  let a := Law μ (fun x ↦ (p x ∧ q x))
  let b := Law μ q
  have h1 : CondLaw μ p q = a / b := rfl
  rw [h1, div_le_one_iff]
  have h2 : a ≤ b := by apply CondLaw_and_lt_proj
  have h3 : ¬(b < 0) := by simp [Law_nonneg]
  simp only [h2, and_true, h3, false_and, or_false]
  refine LE.le.gt_or_eq ?h
  apply Law_nonneg

def CondProb (μ : random (Bool × Bool)) : ℚ := CondLaw μ (fun (x, y) ↦ x ∧ y) (fun (_, y) ↦ y)

def CondProb_nonneg (μ : random (Bool × Bool)) : CondProb μ ≥ 0 := by apply CondLaw_nonneg

def CondProb_lt_one (μ : random (Bool × Bool)) : CondProb μ ≤ 1 := by apply CondLaw_lt_one

def conditionally (μ : random (Bool × Bool)) : random Bool :=
  Bernoulli (CondProb μ) (CondProb_nonneg μ) (CondProb_lt_one μ)

notation:10 lhs:10 "|" rhs:11 => (lhs, rhs)  -- notation used for conditional probability (see Examples.lean)

-- TODO :
-- 1. Change UniformDist so that it consumes a [Nonempty α] and remove Finset.nonemepty argument,
--    instead returning a point mass at a default element if the given Finset is empty.
-- 2. Define law (μ : random α) (p : α → Bool) : ℚ := μ.expectation (fun x ↦ if p x then 1 else 0)
-- 3. Define condLaw ( : ) : ...
-- 4. Think about how to prove remaining sorry, possibly redefining CondProb using condLaw
-- 5. Make Functor instance for monad and redefine contitional probability without do notation.
