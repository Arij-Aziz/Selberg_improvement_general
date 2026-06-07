/-
# Sieve.MultiPrime.OptimalWeights

Optimal Selberg weights and the evaluation of the quadratic form Q(λ)
at the optimal choice.

## Main definitions

* `hFunction` — the multiplicative function h(d) = g(d) / ∏_{p | d} (1 - g(p))
* `V_function` — V(D) = Σ_{d ≤ D, d ∈ sqfDiv(P)} h(d)
* `selbergOptimalWeights` — λ_d = μ(d) · V(D/d) / V(D)

## Main results

* `hFunction_one` — h(1) = 1 when g(1) = 1
* `V_function_ge_one` — V(D) ≥ 1 under standard assumptions
* `V_function_pos` — V(D) > 0 under standard assumptions
* `selbergOptimalWeights_one` — the optimal weights satisfy λ_1 = 1
* `quadForm_restrict_to_support` — Q(λ) depends only on the support
* `quadForm_factor_V_sq` — factoring out V(D)² from Q(λ_opt)

## Status note

The identity `optimalWeight_quadForm_eq` (Q(λ_opt) = 1/V(D)) requires a
deep Möbius inversion argument on the lattice of squarefree divisors.
The precise formula for optimal weights in the *truncated* setting
(λ_d = 0 for d > D) involves a more complex expression than the
blueprint's μ(d) V(D/d) / V(D); the correct formula involves
the sieve's characteristic equation system. See Iwaniec-Kowalski §6.4
for the correct optimization. This theorem remains as a sorry pending
the correct weight formula and its verification.

-- Source: Iwaniec-Kowalski eq. (6.63)-(6.74); Ford §4 pages 43-45; JTNB_2006 eq. (8.2)

Status: PartiallyProved: definitions and helpers proved; optimalWeight_quadForm_eq has sorry
-/
import Mathlib
import RequestProject.Core.MultiPrime.L2Identity

open Finset BigOperators

noncomputable section

-- Source: Iwaniec-Kowalski eq. (6.63); Ford sieve2023-6.pdf §4 p. 43
/-- The multiplicative function h(d) = g(d) / ∏_{p ∈ primeFactors(d)} (1 - g(p)).
    For squarefree d with g multiplicative, this equals
    ∏_{p | d} g(p)/(1 - g(p)). -/
noncomputable def hFunction (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  g d / ∏ p ∈ d.primeFactors, (1 - g p)

-- Source: Iwaniec-Kowalski eq. (6.74); JTNB_2006 eq. (8.2)
/-- V(D) = Σ_{d ≤ D, d ∈ sqfDivisors(P)} h(d).
    This is the reciprocal sum that appears in the Selberg upper bound. -/
noncomputable def V_function (g : ℕ → ℝ) (P D : ℕ) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (· ≤ D), hFunction g d

-- Source: Iwaniec-Kowalski eq. (6.71)
/-- The optimal Selberg weights: λ_d = μ(d) · V(D/d) / V(D).
    These minimize the quadratic form Q(λ) subject to λ_1 = 1.
    Note: In the truncated setting (d ≤ D), the correct optimal weights
    may require a more complex expression; see the status note above. -/
noncomputable def selbergOptimalWeights (g : ℕ → ℝ) (P D : ℕ) (d : ℕ) : ℝ :=
  if d ∈ (sqfDivisors P).filter (· ≤ D)
  then (ArithmeticFunction.moebius d : ℝ) * V_function g P (D / d) / V_function g P D
  else 0

/-- h(1) = 1 when g(1) = 1. -/
lemma hFunction_one (g : ℕ → ℝ) (hg1 : g 1 = 1) : hFunction g 1 = 1 := by
  simp only [hFunction, Nat.primeFactors_one, prod_empty, hg1, div_one]

/-- V(D) ≥ 1 when D ≥ 1 and g(1) = 1, P ≠ 0, h nonneg. -/
lemma V_function_ge_one (g : ℕ → ℝ) (P D : ℕ) (hP : P ≠ 0) (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d) :
    1 ≤ V_function g P D := by
  calc (1 : ℝ) = hFunction g 1 := (hFunction_one g hg1).symm
    _ ≤ V_function g P D := Finset.single_le_sum
        (fun x hx => hh_nonneg x (Finset.mem_filter.mp hx |>.1))
        (Finset.mem_filter.mpr ⟨one_mem_sqfDivisors hP, hD⟩)

/-- V(D) > 0 when D ≥ 1, g(1) = 1, P ≠ 0, h nonneg. -/
lemma V_function_pos (g : ℕ → ℝ) (P D : ℕ) (hP : P ≠ 0) (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d) :
    0 < V_function g P D :=
  lt_of_lt_of_le zero_lt_one (V_function_ge_one g P D hP hD hg1 hh_nonneg)

/-- The optimal weights satisfy λ_1 = 1 when V(D) ≠ 0 and D ≥ 1. -/
lemma selbergOptimalWeights_one (g : ℕ → ℝ) (P D : ℕ) (hP : P ≠ 0)
    (hD : 1 ≤ D)
    (hV : V_function g P D ≠ 0)
    (hg1 : g 1 = 1) :
    selbergOptimalWeights g P D 1 = 1 := by
  unfold selbergOptimalWeights
  norm_num [hV, hg1]
  exact ⟨one_mem_sqfDivisors hP, by positivity⟩

/-- The optimal weights vanish outside the support. -/
lemma selbergOptimalWeights_zero (g : ℕ → ℝ) (P D : ℕ) (d : ℕ)
    (hd : d ∉ (sqfDivisors P).filter (· ≤ D)) :
    selbergOptimalWeights g P D d = 0 := by
  unfold selbergOptimalWeights; exact if_neg hd

/-- For d not in the support of selbergOptimalWeights, the contribution to
    the quadratic form is zero. This allows restricting the sum in
    multiPrimeQuadForm to the support. -/
lemma quadForm_restrict_to_support (P D : ℕ) (g : ℕ → ℝ)
    (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) =
    ∑ d ∈ (sqfDivisors P).filter (· ≤ D),
      ∑ e ∈ (sqfDivisors P).filter (· ≤ D),
        selbergOptimalWeights g P D d * selbergOptimalWeights g P D e /
        (Nat.lcm d e : ℝ) := by
  unfold multiPrimeQuadForm selbergOptimalWeights
  simp +contextual [Finset.sum_filter]
  exact Finset.sum_congr rfl fun x hx => by split_ifs <;> simp +decide [*, div_eq_mul_inv]

/-- Factoring out 1/V(D)² from the quadratic form at optimal weights. -/
lemma quadForm_factor_V_sq (P D : ℕ) (g : ℕ → ℝ)
    (hP : Squarefree P) (hP_pos : 0 < P)
    (_hD : 1 ≤ D) (_hg1 : g 1 = 1)
    (_hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) =
    (1 / V_function g P D ^ 2) *
    ∑ d ∈ (sqfDivisors P).filter (· ≤ D),
      ∑ e ∈ (sqfDivisors P).filter (· ≤ D),
        (ArithmeticFunction.moebius d : ℝ) * V_function g P (D / d) *
        ((ArithmeticFunction.moebius e : ℝ) * V_function g P (D / e)) /
        (Nat.lcm d e : ℝ) := by
  rw [quadForm_restrict_to_support P D g hP hP_pos]
  simp +decide [Finset.mul_sum _ _ _, mul_div_assoc, mul_assoc, mul_comm, mul_left_comm, sq,
    selbergOptimalWeights]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  grind

/-- Key theorem: for the optimal Selberg weights, Q(λ_opt) = 1/V(D).

    Source: Iwaniec-Kowalski eq. (6.70); Ford Theorem 4.1 p. 44;
    ANT-Chapter12 Theorem 12.1.1.

    Proof: Factor Q(λ_opt) = (1/V²) · Σ μ(d)μ(e) V(D/d) V(D/e) / lcm(d,e).
    The inner sum should equal V(D) by a Möbius inversion argument.
    The precise verification requires solving the sieve's characteristic
    equation system, which is deferred to a future milestone. -/
theorem optimalWeight_quadForm_eq
    (P D : ℕ) (g : ℕ → ℝ)
    (hP : Squarefree P) (hP_pos : 0 < P)
    (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d)
    (hg_range : ∀ p ∈ Nat.primeFactors P, 0 < g p ∧ g p < 1)
    (hg_mult : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
      d ∣ P → e ∣ P → g (d * e) = g d * g e) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) = 1 / V_function g P D := by
  sorry

end
