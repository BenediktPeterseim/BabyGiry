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


def Bernoulli (p : ℚ) (nonneg : 0 ≤ p) (lt_one : p ≤ 1): FinProb Bool where
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



-- TODO :
-- 1. write down example of a FinProb (e.g. coinflip) (DONE)
-- 2. add requirements : positivity, sum to 1 (DONE)
-- 3. adjust example (DONE)
-- 4. Write P : FinProb Bool → ℚ evaluting mass at true, rename mass to mass?
--    Add some comments. Remove simp by using "simp?". Rename coinflip to BernoulliTrial?
-- 5. implement monad structure
-- 6. introduce nice notation
-- 7. nice non-trivial example
