/-
# ConditionalConnection.lean
# The Connecting Theorem: Mass–Energy, Restriction, and Kinetic Stability

## Mathematical Status

This file proves that Results 1, 2, and 3 are connected through a single chain:
  kinetic stability (Result 3) → V_function stability
                               → mass = N/V(g,P,D) (Result 1)
                               → l2NormSq ≥ |S|⁴ · V² / N³ (Result 2)

The connecting theorem `selberg_unified_connection` ASSUMES the theorem
  `optimalWeight_quadForm_eq`
from `RequestProject/Core/MultiPrime/OptimalWeights.lean`.

**That theorem IS mathematically correct.**
It states: multiPrimeQuadForm P (selbergOptimalWeights g P D) = 1 / V_function g P D.
This is Iwaniec–Kowalski eq. (6.70), Ford Theorem 4.1 p.44, and
JTNB_2006 eq. (8.2).
The mathematical proof proceeds by solving the Selberg variational system:
  Σ_{d,e ≤ D} μ(d)μ(e) V(D/d) V(D/e) / lcm(d,e) = V(D)
via Möbius inversion on the squarefree divisor lattice.

**The Lean formalization of this proof is not currently present in the repository.**
The `sorry` in `optimalWeight_quadForm_eq` reflects a missing formalization only —
not a mathematical gap, conjecture, or open problem.

The theorem `selberg_unified_connection_moebius` below is fully sorry-free and
establishes the same chain for the Möbius-weight specialisation (g = 1/·, D = P).
Results 1, 2, and 3 in their respective files are fully sorry-free.
-/
import Mathlib
import RequestProject.Core.MultiPrime.OptimalWeights
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MassEnergyTradeoff.MassEnergySandwich
import RequestProject.Core.KineticStability.VFunctionStability
import RequestProject.Core.RestrictionLowerBoundSelberg

open Finset BigOperators

noncomputable section

/-
The Unified Selberg Connection Theorem (general g, conditional).
    ASSUMES optimalWeight_quadForm_eq. See file header.
-/
theorem selberg_unified_connection
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (g : ℕ → ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d)
    (hg_range : ∀ p ∈ Nat.primeFactors P, 0 < g p ∧ g p < 1)
    (hg_mult : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
      d ∣ P → e ∣ P → g (d * e) = g d * g e)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D) (by omega) hlam_one
    -- Chain link (B): mass = N/V
    M.mass = (P * m : ℝ) / V_function g P D
    ∧
    -- Chain link (C): l2NormSq lower bound
    M.l2NormSq ≥ M.targetMass ^ 4 * V_function g P D ^ 2 / (P * m : ℝ) ^ 3 := by
  constructor;
  · convert multiPrime_mass_eq_quadForm P m hP hP_pos hm ( selbergOptimalWeights g P D ) hlam_one using 1;
    rw [ optimalWeight_quadForm_eq P D g hP hP_pos hD hg1 hh_nonneg hg_range hg_mult ] ; ring;
  · convert selberg_l2_lower_bound P m hP hP_pos hm ( selbergOptimalWeights g P D ) hlam_one _ using 1;
    · rw [ optimalWeight_quadForm_eq P D g hP hP_pos hD hg1 hh_nonneg hg_range hg_mult ] ; ring_nf;
      grobner;
    · rw [ optimalWeight_quadForm_eq ] <;> try assumption;
      exact one_div_pos.mpr ( V_function_pos g P D ( by positivity ) hD hg1 hh_nonneg )

/-
The Möbius-weight case of the connecting theorem. Fully sorry-free.
    Uses only proved lemmas: selberg_mass_eq + selberg_l2_sharp.
-/
theorem selberg_unified_connection_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one
    M.mass = (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P
    ∧
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P P ^ 2 / (P * m : ℝ) ^ 3 := by
  exact ⟨ selberg_mass_eq P m hP hP_pos hm hlam_one, selberg_l2_sharp P m hP hP_pos hm hlam_one ⟩

end
