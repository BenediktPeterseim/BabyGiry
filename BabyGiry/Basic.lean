/-
Copyright (c) 2024 Benedikt Peterseim. All rights reserved.
Author: Benedikt Peterseim
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Baby Giry: A Monad for Elementary Probability in Lean

## Main Definitions:

- The `BabyGiry.Random` monad is the monad from the title. It is defined
  via rational-valued positive linear functionals, which enables a computable
  treatment. This is only effective for small sample spaces, but already
  illustrates the basic ideas behind probability monads and probabilistic programming.
- Three important example distributions, `BabyGiry.Unif`, `BabyGiry.Bernoulli`
  and `BabyGiry.Binomial` are defined.
- `BabyGiry.Prod` is the product of probability measures, the notation ` ⊗ ` is introduced.
- We also treat conditionals and a probabilistic programming style `randomly do` notation
  including an `observe` statement to condition on events, see Examples.lean for usage.
-/

namespace BabyGiry

open Finset BigOperators

structure Random (α : Type) where
  expectation : (α → ℚ) → ℚ  -- expectation functional
  nonnegative : ∀ f : (α → ℚ), f ≥ 0 → expectation f ≥ 0
  additive : ∀ f g : (α → ℚ), expectation (f + g) = expectation f + expectation g
  normalized : expectation (fun _ ↦ 1) = 1


instance : Monad Random where
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
      simp only [Random.additive]
      apply μ.additive
    normalized := by
      conv =>
        dsimp only
        lhs
        pattern Random.expectation (f _) fun _ ↦ 1
        rw [(f x).normalized]
      apply μ.normalized
  }


def Unif [Inhabited α] (support : Finset α) : Random α where
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


def Bernoulli (q : ℚ) : Random Bool where
  expectation (f : Bool → ℚ) := let p := max (min q 1) 0; p * (f True) + (1-p) * (f False)
  nonnegative := by
    intro f hf
    simp
    let p := max (min q 1) 0
    have h1 : 0 ≤ (1-p) := by simp only [ge_iff_le, le_min_iff, zero_le_one, and_true, min_le_iff,
      sub_nonneg, max_le_iff, le_refl, or_true, and_self]
    have h2 : 0 ≤ f true := by apply hf
    have h3 : 0 ≤ f false := by apply hf
    positivity
  additive := by
    intros f g
    simp only [decide_True, Pi.add_apply, decide_False]
    ring
  normalized := by ring


def IID (μ : Random α) (n : ℕ) : Random (List α) :=
  if n = 0 then
    pure []
  else do
    let l <- IID μ (n - 1)
    let x <- μ
    return l.append [x]


def Binomial (n : ℕ) (p : ℚ) : Random ℕ := do
  let trials <- IID (Bernoulli p) n
  let mut sum := 0
  for trial in trials do
    if trial then
      sum := sum + 1
  return sum


def Pick [DecidableEq α] [Inhabited α] (n : ℕ) (s : List α) : Random (List α) := do
  let mut picks := ([] : List α)
  let mut s' := s
  for _ in List.range n do
    let x <- Unif s'.toFinset
    picks := picks.append [x]
    s' := s'.filter (fun y => y ≠ x)
  return picks


-- Helper function to swap two elements of a list.
def Swap [Inhabited α] (l : List α) (i j : ℕ) : List α :=
let a := l[i]!
let b := l[j]!
(l.set j a).set i b

-- Fisher-Yates shuffle algorithm.
def Shuffle [Inhabited α] (l : List α) : Random (List α) := do
  let mut l' := l
  for i in List.range (l.length - 1) do
    let j ← Unif (Finset.Icc 1 i)
    l' := Swap l' i j
  return l'


-- *Auxiliary definitions and lemmas*

def Probability (event : Random Bool) : ℚ := event.expectation (fun x ↦ if x then 1 else 0)

noncomputable
def indicator (A : Set α) (x : α) : ℚ :=
  --have : Decidable (A x) := Classical.dec (A x)
  --if A x then 1 else 0
  Set.indicator (M := ℚ) A (fun _ ↦ 1) x

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

def Law (μ : Random α) (p : α → Bool) : ℚ := μ.expectation (fun x ↦ if p x then 1 else 0)

-- A version of Law ignoring decidability.
noncomputable
def Law' (μ : Random α) (A : Set α) : ℚ :=
  -- have (x : α) : Decidable (A x) := Classical.dec (A x)
  μ.expectation (Set.indicator (M := ℚ) A (fun _ ↦ 1))

lemma Law'_eq_Law (μ : Random α) (p : α → Bool) : Law μ p = Law' μ {x | p x} := by
  have h : (fun x ↦ if p x then 1 else 0) = (Set.indicator (M := ℚ) {x | p x} (fun _ ↦ 1)) := by aesop
  unfold Law
  rw [h]
  rfl

lemma Law'_nonneg (μ : Random α) (A : Set α) : 0 ≤ Law' μ A := by
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
  (μ : Random α)
  (A B : Set α)
  (disjoint : A ∩ B = ∅)
  : Law' μ (A ∪ B) = Law' μ A + Law' μ B :=
by
  change μ.expectation (indicator (A ∪ B)) = Law' μ A + Law' μ B
  rw [indicator_of_disjoint_union, μ.additive]
  rfl
  exact disjoint

lemma Law'_monotone
  (μ : Random α)
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

lemma Law'_univ_eq_one (μ : Random α) : Law' μ Set.univ = 1 := by
  unfold Law'
  simp only [Set.indicator_univ]
  apply μ.normalized

lemma Law'_lt_one (μ : Random α) (A : Set α) : Law' μ A ≤ 1 := by
  rw [←Law'_univ_eq_one μ]
  apply Law'_monotone
  simp_all only [Set.subset_univ]

lemma Law_nonneg (μ : Random α) (p : α → Bool) : Law μ p ≥ 0 := by
  rw [Law'_eq_Law]
  apply Law'_nonneg

lemma Law_lt_one (μ : Random α) (p : α → Bool) : Law μ p ≤ 1 := by
  rw [Law'_eq_Law]
  apply Law'_lt_one

lemma Law_monotone (μ : Random α) (p q : α → Bool) (p_lt_q : p ≤ q) : Law μ p ≤ Law μ q := by
  rw [Law'_eq_Law]
  rw [Law'_eq_Law]
  apply Law'_monotone
  assumption

-- *Conditionals*

def CondLaw (μ : Random α) (p : α → Bool) (q : α → Bool) : ℚ := Law μ (fun x ↦ (p x ∧ q x)) / Law μ q

lemma CondLaw_nonneg (μ : Random α) (p : α → Bool) (q : α → Bool) : CondLaw μ p q ≥ 0 := by
  apply div_nonneg
  apply Law_nonneg
  apply Law_nonneg

lemma CondLaw_and_lt_proj
  (μ : Random α) (p : α → Bool) (q : α → Bool)
  : Law μ (fun x ↦ (p x ∧ q x)) ≤ Law μ q :=
by
  apply Law_monotone
  refine Pi.le_def.mpr ?p_lt_q.a
  intro x
  simp only [Bool.decide_and, Bool.decide_coe]
  exact Bool.and_le_right (p x) (q x)

lemma CondLaw_lt_one (μ : Random α) (p : α → Bool) (q : α → Bool) : CondLaw μ p q ≤ 1 := by
  let a := Law μ (fun x ↦ (p x ∧ q x))
  let b := Law μ q
  have h1 : CondLaw μ p q = a / b := rfl
  rw [h1, div_le_one_iff]
  have h2 : a ≤ b := by apply CondLaw_and_lt_proj
  have h3 : ¬(b < 0) := by simp only [not_lt, Law_nonneg]
  simp only [h2, and_true, h3, false_and, or_false]
  refine LE.le.gt_or_eq ?h
  apply Law_nonneg

def CondProb (μ : Random (Bool × Bool)) : ℚ := CondLaw μ (fun (x, y) ↦ x ∧ y) (fun (_, y) ↦ y)

def CondProb_nonneg (μ : Random (Bool × Bool)) : CondProb μ ≥ 0 := by apply CondLaw_nonneg

def CondProb_lt_one (μ : Random (Bool × Bool)) : CondProb μ ≤ 1 := by apply CondLaw_lt_one

def conditionally (μ : Random (Bool × Bool)) : Random Bool := Bernoulli (CondProb μ)

-- Allows writing ℙ[p x | x ~ μ] for Law μ p.
notation "ℙ[" p:20 "|" x " ~ " mu "]" => Law mu (fun x => p)
-- Allows writing ℙ[p x | q x, x ~ μ] for CondLaw μ p q.
notation "ℙ[" p:20 "|" q ", " x " ~ " mu "]" => CondLaw mu (fun x => p) (fun x => q)

-- Example usage:
def μ := Unif {(0, 1), (1, 0), (2, 3), (1, 1)}
example : ℙ[x = 1 ∧ y > 0 | x > 0, (x, y) ~ μ] = 1/3 := by rfl
example : ℙ[x + y = 5 | (x, y) ~ μ] = 1/4 := by rfl

--*Products*

def Prod (μ : Random α) (ν : Random β) : Random (α × β) := do
  let x <- μ
  let y <- ν
  return (x, y)

infix:80 " ⊗ " => Prod

-- example usage
example : ℙ[x + y = 9 | x ≥ 2,
  (x, y) ~ (Unif {1, 2, 3, 4, 5, 6}) ⊗ (Unif {1, 2, 3, 4, 5, 6})]
  = 2/15 := by rfl

--*Probabilistic programming style do notation*

def CondRandom := WriterT Bool Random

instance : Monad CondRandom := WriterT.monad true Bool.and

instance : Functor Random := Applicative.toFunctor

def observe (p : Bool) : CondRandom Unit := WriterT.mk $ pure (⟨⟩, p)

def sample (μ : Random α) : CondRandom α := WriterT.mk do
  let x <- μ
  return (x, true)

def reject_on_condition (μ : CondRandom α) : Random (Option α) := do
  let (x, p) <- μ
  if p then
    return x
  return none

def extend_to_option (f : α → ℚ) : Option α → ℚ
  | none => 0
  | some x => f x

lemma extend_to_option_additive (f : α → ℚ) (g : α → ℚ) : extend_to_option (f + g) = extend_to_option f + extend_to_option g := by
  unfold extend_to_option
  funext x
  simp only [Pi.add_apply]
  split
  · rfl
  · rfl

def probOfCond (μ : CondRandom α) : ℚ :=
  (reject_on_condition μ).expectation (extend_to_option (fun _ ↦ 1))

def randomly (μ : CondRandom α) : Random α where
  expectation f :=
    if (probOfCond μ) = 0 then
      μ.expectation (fun (x, _) ↦ f x)
    else
      ((reject_on_condition μ).expectation (extend_to_option f)) / (probOfCond μ)
  nonnegative := by
    intros f hf
    apply ite_nonneg
    · apply Random.nonnegative
      simp only [ge_iff_le]
      refine Pi.le_def.mpr ?ha.a.a
      intro (x, p)
      simp only [Pi.zero_apply, ge_iff_le]
      apply hf
    · apply div_nonneg
      · apply Random.nonnegative
        apply Pi.le_def.mpr
        intro y
        rcases y
        · rfl
        · apply hf
      · apply Random.nonnegative
        simp only [ge_iff_le]
        refine Pi.le_def.mpr ?hb.a.a
        intro p
        simp only [Pi.zero_apply]
        unfold extend_to_option
        split
        · rfl
        · rfl
  additive := by
    intros f g
    simp
    split_ifs with h
    · apply Random.additive
    · rw [extend_to_option_additive, Random.additive]
      rw [← add_div]
  normalized := by
    beta_reduce
    split_ifs with h
    · apply Random.normalized
    · field_simp
      rfl

notation "~"mu => sample $ mu
notation "{" i ",..," j "}" => Finset.Icc i j

/-- `Linspace a b` is the Finset of (N := 11) evenly spaced rationals between a and b, -/
def Linspace (a : ℚ) (b : ℚ) (N : ℕ := 11) (hab : b - a ≠ 0 := by norm_num) (hN : (N : ℚ) - 1 ≠ 0 := by norm_num) :=
  let f (n : ℕ) := (a + (b-a) * (n : ℚ) / (N-1))
  have : Function.Injective f := by intros n m; field_simp; aesop
  Finset.map ⟨f, this⟩ (Finset.range N)


/-!
*TODO:*
- create LawfulMonad instance
- make def `independent` (List (Random α)) : Random (List α) := ...
  --> Q: can this be used with pattern matching à la
    let [x, y, z, w] <- independent [μ, ν, ...] ?
- Examples for higher-order probability:
  - ℙ[ℙ[x = 0 | x ~ f y] = 1/2 | y ~ μ]
    e.g. rolling either one or two dice depending on coin flip.
  - empirical measure.
- make definition of:
  - expectation with notation 𝔼[ f x | p x, x ~ μ]
  - select n (s : Finset α) ~~> i.e. pick without duplicates
    --> should have type:
      def select (n : ℕ) (s : Finset α) : Random (List α)
  - ...
-/
