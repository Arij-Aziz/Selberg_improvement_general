/-
# Sieve.MultiPrime.FourierRatio

Novel results connecting the multi-prime quadratic form Q(λ) to the
restriction lower bound.

## Main results

* `multiPrime_mass_eq_quadForm` — mass(ν) = N · Q(λ)
* `multiPrime_mass_lower_bound` — Q(λ) ≥ targetMass / N (the Selberg bound)
* `multiPrime_restriction_lower_bound` — mass² · l2NormSq ≥ targetMass⁴/N
    expressed with mass = N · Q(λ)

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.RestrictionLowerBound

open Finset BigOperators

noncomputable section

/-- The multi-prime Selberg majorant as a `Majorant` structure. -/
def multiPrimeMajorant (N P : ℕ) (lambda : ℕ → ℝ)
    (hP : P ≠ 0) (hlambda_one : lambda 1 = 1) : Majorant N where
  nu := selbergNu N P lambda
  target := sieveIndicator N P
  nu_nonneg := selbergNu_nonneg N P lambda
  target_nonneg := sieveIndicator_nonneg N P
  target_indicator := sieveIndicator_indicator N P
  domination := selbergNu_dominates N P lambda hP hlambda_one

/-- The mass of the multi-prime Selberg majorant equals N · Q(λ). -/
theorem multiPrime_mass_eq_quadForm
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    (multiPrimeMajorant (P * m) P lambda (by omega) hlam_one).mass =
    (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  unfold Majorant.mass multiPrimeMajorant
  simp only
  exact l2NormSq_multiPrime_eq_quadForm P m hP hP_pos hm lambda

/-
Q(λ) ≥ targetMass / N: the Selberg upper bound in quadratic form language.
    Since mass(ν) ≥ targetMass and mass(ν) = N · Q(λ), we get Q(λ) ≥ targetMass/N.
-/
theorem multiPrime_quadForm_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    let M := multiPrimeMajorant (P * m) P lambda (by omega) hlam_one
    multiPrimeQuadForm P lambda ≥ M.targetMass / (P * m) := by
  have h_mass_ge_targetMass : (multiPrimeMajorant (P * m) P lambda (by omega) hlam_one).mass ≥ (multiPrimeMajorant (P * m) P lambda (by omega) hlam_one).targetMass :=
    Majorant.mass_ge_targetMass _
  rw [ ge_iff_le, div_le_iff₀ ] <;> first | positivity | nlinarith! [ multiPrime_mass_eq_quadForm P m hP hP_pos hm lambda hlam_one ] ;

/-
The restriction lower bound for the multi-prime Selberg majorant,
    with mass expressed as N · Q(λ):

    (N · Q(λ))² · l2NormSq(ν) ≥ targetMass⁴ / N
-/
theorem multiPrime_restriction_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    let N : ℕ := P * m
    let M := multiPrimeMajorant N P lambda (by omega) hlam_one
    ((P * m : ℝ) * multiPrimeQuadForm P lambda) ^ 2 * M.l2NormSq ≥
    M.targetMass ^ 4 / (P * m) := by
  convert restriction_lower_bound _ _ using 3;
  · exact (multiPrime_mass_eq_quadForm P m hP hP_pos hm lambda hlam_one).symm
  · norm_cast;
  · positivity

end