import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset BigOperators

structure FinProb (α : Type) where
  support : Finset α
  prob_mass_fun : support → ℚ
  nonnegative : ∀ x : support, prob_mass_fun x ≥ 0
  normalized : ∑ x, prob_mass_fun x = 1


def coinflip : FinProb Bool where
  support := {true, false}
  prob_mass_fun := fun _ => 1/2
  nonnegative := by
    intro
    simp
    norm_num
  normalized := by rfl


-- TODO :
-- 1. write down example of a FinProb (e.g. coinflip) (DONE)
-- 2. add requirements : positivity, sum to 1 (DONE)
-- 3. adjust example (DONE)
-- 4. Write P : FinProb Bool → ℚ evaluting prob_mass_fun at true, rename prob_mass_fun to mass?
--    Add some comments. Remove simp by using "simp?". Rename coinflip to BernoulliTrial?
-- 5. implement monad structure
-- 6. introduce nice notation
-- 7. nice non-trivial example
