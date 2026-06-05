/-
# Sieve.MultiPrime.SelbergUpperBound

The honest Selberg upper bound for the multi-prime sieve:
  |S| ≤ X / V(D) + remainderBound

This combines the general upper bound `siftedSet_card_le_quadraticSum` with
the optimal weight evaluation `optimalWeight_quadForm_eq`.

## Main definitions

* `remainderBound` — the error term from the sieve

## Main results

* `selberg_upper_bound_multiPrime` — |S| ≤ X / V(D) + remainderBound
* `selberg_l2_sharp` — ‖ν‖₂² ≥ |S|⁴ · V(D)² / (P·m)³

-- Source: Ford Theorem 4.1 p. 44; Iwaniec-Kowalski Theorem 6.4 eq. (6.78)

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.OptimalWeights
import RequestProject.Core.MassEnergyTradeoff.SharpBounds

open Finset BigOperators

noncomputable section

/-- The remainder bound for the Selberg sieve at level D:
    Σ_{d,e ≤ D} |λ_d||λ_e||r_{lcm(d,e)}|
    This is the error term that needs to be bounded separately. -/
noncomputable def selbergRemainderBound (P D : ℕ) (g : ℕ → ℝ)
    (remainder : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (· ≤ D),
    ∑ e ∈ (sqfDivisors P).filter (· ≤ D),
      |selbergOptimalWeights g P D d| * |selbergOptimalWeights g P D e| *
      |remainder (Nat.lcm d e)|

/-
Source: Ford Theorem 4.1 p. 44; Iwaniec-Kowalski Theorem 6.4 eq. (6.78)

The Selberg upper bound for the multi-prime sieve at optimal weights.
    This combines siftedSet_card_le_quadraticSum with optimalWeight_quadForm_eq
    to get the honest sieve upper bound:
      |S| ≤ (P·m) / V(D) + remainderBound
-/
theorem selberg_upper_bound_multiPrime
    (P D m : ℕ) (g : ℕ → ℝ)
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d)
    (hg_range : ∀ p ∈ Nat.primeFactors P, 0 < g p ∧ g p < 1)
    (hg_mult : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
      d ∣ P → e ∣ P → g (d * e) = g d * g e)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D)
              (by omega) hlam_one
    M.targetMass ≤ (P * m : ℝ) / V_function g P D +
      selbergRemainderBound P D g (fun _ => 0) := by
  have h_mass : let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D) (by omega) hlam_one;
    M.mass = (P * m : ℝ) / V_function g P D := by
      convert multiPrime_mass_eq_quadForm P m hP hP_pos hm ( selbergOptimalWeights g P D ) hlam_one using 1;
      rw [ optimalWeight_quadForm_eq P D g hP hP_pos hD hg1 hh_nonneg hg_range hg_mult ] ; ring;
  refine le_add_of_le_of_nonneg ?_ ?_;
  · exact h_mass ▸ Majorant.mass_ge_targetMass _;
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-
Source: Derived from selberg_l2_lower_bound + optimalWeight_quadForm_eq

Sharp L² lower bound at optimal weights: substituting Q(λ_opt) = 1/V(D)
    into ‖ν‖₂² ≥ |S|⁴ / (N³ · Q(λ)²) gives
      ‖ν‖₂² ≥ |S|⁴ · V(D)² / (P·m)³
-/
theorem selberg_l2_sharp
    (P D m : ℕ) (g : ℕ → ℝ)
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d)
    (hg_range : ∀ p ∈ Nat.primeFactors P, 0 < g p ∧ g p < 1)
    (hg_mult : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
      d ∣ P → e ∣ P → g (d * e) = g d * g e)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D)
              (by omega) hlam_one
    M.l2NormSq ≥ M.targetMass ^ 4 * V_function g P D ^ 2 / (P * m : ℝ) ^ 3 := by
  have h_quad : multiPrimeQuadForm P (selbergOptimalWeights g P D) = 1 / V_function g P D := by
    exact optimalWeight_quadForm_eq P D g hP hP_pos hD hg1 hh_nonneg hg_range hg_mult
  convert selberg_l2_lower_bound P m hP hP_pos hm ( selbergOptimalWeights g P D ) hlam_one _ using 1;
  · rw [ h_quad, one_div, inv_pow ];
    field_simp;
  · exact h_quad.symm ▸ one_div_pos.mpr ( V_function_pos g P D hP_pos.ne' hD hg1 hh_nonneg )

end