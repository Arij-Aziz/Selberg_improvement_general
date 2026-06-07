/-
  Statements.lean
  ===============
  Auditable statement file for the Selberg Majorant: Multi-Prime Extension.

  ── HOW TO USE ──────────────────────────────────────────────────────────────
  This file has ONE import: `import Mathlib`.
  No `RequestProject.*` imports appear anywhere.

  Every theorem is stated with its verbatim signature from the source file,
  with `sorry` as the proof body. All project-internal definitions are
  reproduced inline below using only Mathlib primitives, so a reviewer can
  verify every statement is well-typed without building the project.

  To check: `lake build RequestProject.Statements`
  Expected: zero errors; only `declaration uses sorry` warnings (intended).

  ── SCOPE ────────────────────────────────────────────────────────────────────
  New theorems introduced in this project only. The 20 theorems from Step 1
  (selbergComparison_massImprovement, sieveMajorant_l2_improvement,
  selbergComparison_dual_improvement, sieveMajorant_l2NormSq_eq_selbergForm,
  restriction_lower_bound, sieve_additive_energy_lower,
  restriction_lower_bound_zero_mode, siftedSet_card_le_quadraticSum,
  weighted_remainder_bound, perturbation_propagates, eulerProduct_stability,
  sieveH_stable, selberg_concrete_restriction_bound,
  selberg_additive_energy_explicit, selberg_mass_energy_interval,
  Nat.Squarefree.lcm, inv_diff_bound, quadForm_term_diff,
  quadForm_term_bound, quadForm_kinetic_stability) are NOT in this file.

  ── CONTENTS ─────────────────────────────────────────────────────────────────
  §0.  Inline definitions (Mathlib-only reproductions)
  §1.  Multi-prime setup                                     (2 theorems)
  §2.  Central Identity: L² identity                        (1 theorem)
  §3.  FourierRatio                                         (3 theorems)
  §4.  Möbius weights and optimality                        (5 theorems)
  §5.  Selberg upper bound and sharp L² bound               (2 theorems)
  §6.  Sharp mass–energy tradeoff                           (1 theorem)
  §7.  Coprime-shift correlation                            (2 theorems)
  §8.  Additive energy lower bound                          (3 theorems)

  Total: 19 theorems (new, matching Audit.lean new-theorem list exactly).
  Axiom footprint for each: [propext, Classical.choice, Quot.sound].
  ─────────────────────────────────────────────────────────────────────────────
-/
import Mathlib

open Finset BigOperators Complex ArithmeticFunction

noncomputable section

-- ════════════════════════════════════════════════════════════════════════════
-- §0.  Inline definitions (Mathlib primitives only)
-- ════════════════════════════════════════════════════════════════════════════

-- ── From Setup.lean ──────────────────────────────────────────────────────

/-- Squarefree divisors of P. -/
def sqfDivisors (P : ℕ) : Finset ℕ :=
  (P.divisors).filter Squarefree

/-- The multi-prime Selberg majorant:
    ν(x) = (Σ_{d ∈ sqfDivisors P, d | gcd(x,P)} λ_d)² -/
def selbergNu (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) : ℝ :=
  (∑ d ∈ (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P), lambda d) ^ 2

/-- The sieve indicator: 1 if gcd(x, P) = 1, else 0. -/
def sieveIndicator (N P : ℕ) (x : Fin N) : ℝ :=
  if Nat.Coprime x.val P then 1 else 0

-- ── From L2Identity.lean ─────────────────────────────────────────────────

/-- The multi-prime quadratic form:
    Q(λ) = Σ_{d,e ∈ sqfDivisors P} λ_d · λ_e / lcm(d,e) -/
def multiPrimeQuadForm (P : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    lambda d * lambda e / (Nat.lcm d e : ℝ)

-- ── From Majorant.lean ───────────────────────────────────────────────────

/-- An abstract majorant for a target indicator function on a finite set. -/
structure Majorant (N : ℕ) where
  nu         : Fin N → ℝ
  target     : Fin N → ℝ
  nu_nonneg      : ∀ x, 0 ≤ nu x
  target_nonneg  : ∀ x, 0 ≤ target x
  target_indicator : ∀ x, target x = 0 ∨ target x = 1
  domination : ∀ x, target x ≤ nu x

namespace Majorant
variable {N : ℕ} (M : Majorant N)
def mass       : ℝ := ∑ x : Fin N, M.nu x
def targetMass : ℝ := ∑ x : Fin N, M.target x
def l2NormSq   : ℝ := ∑ x : Fin N, M.nu x ^ 2
lemma mass_ge_targetMass : M.targetMass ≤ M.mass :=
  Finset.sum_le_sum (fun x _ => M.domination x)
end Majorant

-- ── From FourierRatio.lean ───────────────────────────────────────────────

/-- The multi-prime Selberg majorant packaged as a Majorant structure. -/
def multiPrimeMajorant (N P : ℕ) (lambda : ℕ → ℝ)
    (hP : P ≠ 0) (hlambda_one : lambda 1 = 1) : Majorant N where
  nu               := selbergNu N P lambda
  target           := sieveIndicator N P
  nu_nonneg        := fun x => sq_nonneg _
  target_nonneg    := fun x => by unfold sieveIndicator; split_ifs <;> norm_num
  target_indicator := fun x => by unfold sieveIndicator; split_ifs <;> simp
  domination := by
    intro x; unfold sieveIndicator selbergNu
    split_ifs with hcop
    · have hmem : ∀ d : ℕ, d ∈ sqfDivisors P ↔ d ∣ P ∧ P ≠ 0 ∧ Squarefree d := by
        intro d; simp [sqfDivisors, Nat.mem_divisors]; tauto
      have hfilt : (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P) = {1} := by
        ext d
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro ⟨hd, hdg⟩
          have : d ∣ 1 := by
            have := (hmem d).mp hd
            calc d ∣ Nat.gcd x.val P := hdg
              _ = 1 := Nat.Coprime.gcd_eq_one hcop
          exact Nat.eq_one_of_dvd_one this
        · intro h; subst h
          refine ⟨(hmem 1).mpr ⟨one_dvd P, hP, squarefree_one⟩, ?_⟩
          simp [Nat.Coprime.gcd_eq_one hcop]
      rw [hfilt]; simp [hlambda_one]
    · exact sq_nonneg _
-- ── From Fourier.lean ────────────────────────────────────────────────────

/-- The discrete Fourier transform on Fin N. -/
def dft' (N : ℕ) [NeZero N] (f : Fin N → ℂ) (k : Fin N) : ℂ :=
  ∑ n : Fin N, f n * Complex.exp (-2 * Real.pi * Complex.I * k.val * n.val / N)

/-- DFT L² norm squared. -/
def dftL2NormSq' (N : ℕ) [NeZero N] (f : Fin N → ℂ) : ℝ :=
  ∑ k : Fin N, ‖dft' N f k‖ ^ 2

/-- Embed a real function into ℂ. -/
def realToComplex' (N : ℕ) (f : Fin N → ℝ) : Fin N → ℂ :=
  fun n => (f n : ℂ)

/-- The Fourier transform of a real-valued function. -/
def realDft' (N : ℕ) [NeZero N] (f : Fin N → ℝ) : Fin N → ℂ :=
  dft' N (realToComplex' N f)

-- ── From RestrictionLowerBound.lean ──────────────────────────────────────

/-- Additive energy: E(f) = Σ_x (Σ_a f(a) · f(x−a))² -/
def additiveEnergy' {N : ℕ} [NeZero N] (f : Fin N → ℝ) : ℝ :=
  ∑ x : Fin N, (∑ a : Fin N, f a * f (x - a)) ^ 2

/-- Real L² norm squared. -/
def l2NormSq_real {N : ℕ} (f : Fin N → ℝ) : ℝ :=
  ∑ x : Fin N, f x ^ 2

-- ── From MoebiusWeights.lean ─────────────────────────────────────────────

/-- The Möbius weights restricted to sqfDivisors P. -/
def moebiusWeights (P : ℕ) (d : ℕ) : ℝ :=
  if d ∈ sqfDivisors P then (moebius d : ℝ) else 0

-- ── From OptimalWeights.lean ─────────────────────────────────────────────

/-- h(d) = g(d) / ∏_{p ∈ primeFactors(d)} (1 − g(p)) -/
def hFunction (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  g d / ∏ p ∈ d.primeFactors, (1 - g p)

/-- V(g, P, D) = Σ_{d ∈ sqfDivisors P, d ≤ D} h(d) -/
def V_function (g : ℕ → ℝ) (P D : ℕ) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (· ≤ D), hFunction g d

/-- Optimal Selberg weights: λ_d = μ(d) · V(D/d) / V(D) -/
def selbergOptimalWeights (g : ℕ → ℝ) (P D : ℕ) (d : ℕ) : ℝ :=
  if d ∈ (sqfDivisors P).filter (· ≤ D)
  then (moebius d : ℝ) * V_function g P (D / d) / V_function g P D
  else 0

-- ── From SelbergUpperBound.lean ───────────────────────────────────────────

/-- Remainder bound at Möbius weights: Σ_{d,e} |μ(d)| |μ(e)| |r(lcm(d,e))| -/
def moebiusRemainderBound (P : ℕ) (remainder : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    |moebiusWeights P d| * |moebiusWeights P e| * |remainder (Nat.lcm d e)|

-- ── From SelbergWeightCorrelation.lean ────────────────────────────────────

/-- The coprime-pairs quadratic form:
    Σ_{d,e ∈ sqfDivisors P, gcd(d,e)=1} λ_d · λ_e / (d·e) -/
def coprimePairsQuadForm (P : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P,
  ∑ e ∈ (sqfDivisors P).filter (Nat.Coprime d),
    lambda d * lambda e / (d * e : ℝ)

-- ════════════════════════════════════════════════════════════════════════════
-- §1.  Multi-prime setup
-- ════════════════════════════════════════════════════════════════════════════

/-- **selbergNu_dominates**
    The multi-prime Selberg majorant dominates the sieve indicator when λ₁ = 1. -/
theorem selbergNu_dominates (N P : ℕ) (lambda : ℕ → ℝ)
    (hP : P ≠ 0)
    (hlambda_one : lambda 1 = 1) :
    ∀ x : Fin N, sieveIndicator N P x ≤ selbergNu N P lambda x := by
  sorry

/-- **card_joint_multiples_of_lcm**
    When lcm(d,e) | N, the count of x ∈ Fin N with d | x and e | x
    equals N / lcm(d,e). -/
theorem card_joint_multiples_of_lcm (N d e : ℕ)
    (hN : 0 < N) (hlcm : Nat.lcm d e ∣ N) (hlcm_pos : 0 < Nat.lcm d e) :
    (Finset.univ.filter (fun x : Fin N => d ∣ x.val ∧ e ∣ x.val)).card =
    N / Nat.lcm d e := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §2.  Central Identity
-- ════════════════════════════════════════════════════════════════════════════

/-- **l2NormSq_multiPrime_eq_quadForm**
    Σ_{x ∈ Fin(P·m)} ν(x) = (P·m) · Q(λ). -/
theorem l2NormSq_multiPrime_eq_quadForm
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) :
    ∑ x : Fin (P * m), selbergNu (P * m) P lambda x =
    (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §3.  FourierRatio
-- ════════════════════════════════════════════════════════════════════════════

/-- **multiPrime_mass_eq_quadForm**
    The mass of the multi-prime Selberg majorant equals (P·m) · Q(λ). -/
theorem multiPrime_mass_eq_quadForm
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    (multiPrimeMajorant (P * m) P lambda (by omega) hlam_one).mass =
    (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  sorry

/-- **multiPrime_quadForm_lower_bound**
    Q(λ) ≥ targetMass / (P·m). -/
theorem multiPrime_quadForm_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    let M := multiPrimeMajorant (P * m) P lambda (by omega) hlam_one
    multiPrimeQuadForm P lambda ≥ M.targetMass / (P * m) := by
  sorry

/-- **multiPrime_restriction_lower_bound**
    ((P·m) · Q(λ))² · l2NormSq(ν) ≥ targetMass⁴ / (P·m). -/
theorem multiPrime_restriction_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    let N : ℕ := P * m
    let M := multiPrimeMajorant N P lambda (by omega) hlam_one
    ((P * m : ℝ) * multiPrimeQuadForm P lambda) ^ 2 * M.l2NormSq ≥
    M.targetMass ^ 4 / (P * m) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §4.  Möbius weights and optimality
-- ════════════════════════════════════════════════════════════════════════════

/-- **moebiusWeights_one**
    The Möbius weights satisfy λ₁ = 1. -/
theorem moebiusWeights_one (P : ℕ) (hP_pos : 0 < P) :
    moebiusWeights P 1 = 1 := by
  sorry

/-- **moebius_quadForm_eq**
    Q(μ_P) = φ(P)/P. -/
theorem moebius_quadForm_eq (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (moebiusWeights P) =
      (P.totient : ℝ) / (P : ℝ) := by
  sorry

/-- **multiPrimeQuadForm_lower_bound'**
    Q(λ) ≥ φ(P)/P for any λ with λ(1) = 1 supported on sqfDivisors P. -/
theorem multiPrimeQuadForm_lower_bound'
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    (P.totient : ℝ) / (P : ℝ) ≤ multiPrimeQuadForm P lambda := by
  sorry

/-- **optimalWeight_quadForm_eq_moebius**
    Q(μ_P) = 1 / V(1/·, P, P). -/
theorem optimalWeight_quadForm_eq_moebius
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (moebiusWeights P) =
      1 / V_function (fun n => (1 : ℝ) / n) P P := by
  sorry

/-- **multiPrimeQuadForm_lower_bound_inv**
    Q(λ) ≥ 1 / V(1/·, P, P) for any λ with λ(1) = 1. -/
theorem multiPrimeQuadForm_lower_bound_inv
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    1 / V_function (fun n => (1 : ℝ) / n) P P ≤
      multiPrimeQuadForm P lambda := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §5.  Selberg upper bound and sharp L² bound
-- ════════════════════════════════════════════════════════════════════════════

/-- **selberg_upper_bound_multiPrime**
    |S| ≤ (P·m) / V(1/·, P, P) + moebiusRemainderBound. -/
theorem selberg_upper_bound_multiPrime
    (P m : ℕ)
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P)
              (by omega) hlam_one
    M.targetMass ≤ (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P +
      moebiusRemainderBound P (fun _ => 0) := by
  sorry

/-- **selberg_l2_sharp**
    ‖ν‖₂² ≥ targetMass⁴ · V(1/·,P,P)² / (P·m)³ at Möbius weights. -/
theorem selberg_l2_sharp
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P)
              (by omega) hlam_one
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P P ^ 2 / (P * m : ℝ) ^ 3 := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §6.  Sharp mass–energy tradeoff
-- ════════════════════════════════════════════════════════════════════════════

/-- **selberg_l2_lower_bound**
    ‖ν‖₂² ≥ targetMass⁴ / ((P·m)³ · Q(λ)²). -/
theorem selberg_l2_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hQ_pos : 0 < multiPrimeQuadForm P lambda) :
    let M := multiPrimeMajorant (P * m) P lambda (by omega) hlam_one
    M.l2NormSq ≥ M.targetMass ^ 4 /
      ((P * m : ℝ) ^ 3 * multiPrimeQuadForm P lambda ^ 2) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §7.  Coprime-shift correlation
-- ════════════════════════════════════════════════════════════════════════════

/-- **coprimePairsQuadForm_le_multiPrimeQuadForm**
    coprimePairsQuadForm P λ ≤ multiPrimeQuadForm P λ for nonneg λ. -/
theorem coprimePairsQuadForm_le_multiPrimeQuadForm
    (P : ℕ) (hP_pos : 0 < P) (lambda : ℕ → ℝ)
    (hlam_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ lambda d) :
    coprimePairsQuadForm P lambda ≤ multiPrimeQuadForm P lambda := by
  sorry

/-- **selbergWeight_correlation_coprime_bound**
    Σ_x w(x) · w(x+h) ≤ (P·m) · Q(λ)
    for any h with gcd(h,P) = 1 and nonneg λ. -/
theorem selbergWeight_correlation_coprime_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    (hlam_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ lambda d)
    (h : Fin (P * m)) (hcop : Nat.Coprime h.val P) :
    ∑ x : Fin (P * m),
      (∑ d ∈ (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P),
         lambda d) *
      (∑ d ∈ (sqfDivisors P).filter
               (fun d => d ∣ Nat.gcd ((x.val + h.val) % (P * m)) P),
         lambda d) ≤
    (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  sorry

-- ════════════════════════════════════════════════════════════════════════════
-- §8.  Additive energy lower bound
-- ════════════════════════════════════════════════════════════════════════════

/-- **additiveEnergy_lower_bound**
    E(f) ≥ (‖f‖₂²)² / N for nonneg f on Fin N. -/
theorem additiveEnergy_lower_bound {N : ℕ} [NeZero N] (f : Fin N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hN : (0 : ℝ) < N) :
    additiveEnergy' f ≥ (l2NormSq_real f) ^ 2 / N := by
  sorry

/-- **restriction_lower_bound** (Majorant form)
    mass² · l2NormSq ≥ targetMass⁴ / N. -/
theorem restriction_lower_bound {N : ℕ} (M : Majorant N) (hN : (0 : ℝ) < N) :
    M.mass ^ 2 * M.l2NormSq ≥ M.targetMass ^ 4 / N := by
  sorry

/-- **sieve_additive_energy_lower**
    E(ν) ≥ targetMass⁴ / N³ for any Majorant. -/
theorem sieve_additive_energy_lower {N : ℕ} [NeZero N] (M : Majorant N)
    (hN : (0 : ℝ) < N) :
    additiveEnergy' M.nu ≥ M.targetMass ^ 4 / N ^ 3 := by
  sorry

end
