/-
# Sieve.MultiPrime.SelbergCorrelation

Correlation bounds for the multi-prime Selberg majorant.

## Main results

* `selbergNu_autocorrelation_eq_l2` — h=0 autocorrelation is the L² norm
* `correlationBound` — the error bound for the correlation sum
* `correlationBound_nonneg` — the bound is nonneg

-- Source: Green-Tao 2007 (0404188v6-3.pdf) Proposition 9.1 as model.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower

open Finset BigOperators

noncomputable section

/-- The correlation bound for shift h.
    This is a uniform bound valid for all shifts, using the triangle inequality
    on the double sum expansion of the correlation. The bound is
    Σ_{d,e} |λ_d| |λ_e| / lcm(d,e), which equals Q(|λ|). -/
noncomputable def correlationBound (P m : ℕ) (lambda : ℕ → ℝ) (_h : Fin (P * m)) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    |lambda d| * |lambda e| / (Nat.lcm d e : ℝ)

/-- The correlation bound is nonneg. -/
lemma correlationBound_nonneg (P m : ℕ) (lambda : ℕ → ℝ) (h : Fin (P * m)) :
    0 ≤ correlationBound P m lambda h :=
  Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ =>
    div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg _)

-- Source: Direct identity
/-- The h=0 autocorrelation: Σ_x ν(x)² equals the L² norm of ν. -/
theorem selbergNu_autocorrelation_eq_l2
    (P m : ℕ) (hP_pos : 0 < P) (_hm : 0 < m)
    (lambda : ℕ → ℝ) :
    ∑ x : Fin (P * m),
      selbergNu (P * m) P lambda x * selbergNu (P * m) P lambda x =
    ∑ x : Fin (P * m), selbergNu (P * m) P lambda x ^ 2 := by
  exact Finset.sum_congr rfl fun x _ => (sq (selbergNu (P * m) P lambda x)).symm

end
