import Mathlib.Data.Finset.Basic

open Finset

structure FinProb (α : Type) where
  supported_in : Finset α
  prob_mass_fun : { x // (supported_in : Set α) x } → ℚ

-- TODO :
-- 1. write down example of a FinProb (e.g. coinflip)
-- 2. add requirements : positivity, sum to 1
-- 3. adjust example
-- 4. implement monad structure
-- 5. introduce nice notation
-- 6. nice non-trivial example
