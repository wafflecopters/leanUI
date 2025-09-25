-- Basic calculus setup for LeanUI
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- Setup for our mathematical workspace
variable {f : ℝ → ℝ} {c : ℝ} {x : ℝ}

-- Example theorem we want to prove
theorem deriv_const_mul (hf : Differentiable ℝ f) :
  deriv (fun x => c * f x) = fun x => c * deriv f x := by
  simp [deriv_const_mul, hf]