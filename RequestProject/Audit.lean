-- Audit.lean: axiom footprint for all main theorems.
-- Expected for each: [propext, Classical.choice, Quot.sound]
-- Any 'sorry' invalidates the proof chain.

import RequestProject.Core.SelbergComparison
import RequestProject.Core.KineticPropagation
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.Weights.FourierConnection
import RequestProject.Core.SelbergRestriction
import RequestProject.Core.Weights.QuadFormStability
import RequestProject.Core.Weights.UpperBound
import RequestProject.Core.MultiPrime.Setup
import RequestProject.Core.MultiPrime.JointCount
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower
import RequestProject.Core.KineticStability.QuadFormPerturbation
import RequestProject.Core.MultiPrime.FourierRatioSharp
import RequestProject.Core.MultiPrime.SelbergCorrelation

-- ── Theorem 1: Mass and L² improvement ──────────────────────────────────────
#print axioms selbergComparison_massImprovement
#print axioms sieveMajorant_l2_improvement
#print axioms selbergComparison_dual_improvement
#print axioms sieveMajorant_l2NormSq_eq_selbergForm

-- ── Theorem 2: Restriction lower bound ──────────────────────────────────────
#print axioms restriction_lower_bound
#print axioms sieve_additive_energy_lower
#print axioms restriction_lower_bound_zero_mode

-- ── Selberg upper bound infrastructure ───────────────────────────────────────
#print axioms siftedSet_card_le_quadraticSum
#print axioms weighted_remainder_bound

-- ── Theorem 3: Kinetic propagation ──────────────────────────────────────────
#print axioms perturbation_propagates
#print axioms eulerProduct_stability
#print axioms sieveH_stable

-- ── Concrete instantiations ──────────────────────────────────────────────────
#print axioms selberg_concrete_restriction_bound
#print axioms selberg_additive_energy_explicit
#print axioms selberg_mass_energy_interval

-- ── Theorem 4: Quadratic form stability ──────────────────────────────────────
#print axioms quadForm_kinetic_stability
#print axioms quadForm_term_bound
#print axioms quadForm_term_diff
#print axioms inv_diff_bound
#print axioms Nat.Squarefree.lcm

-- ── Multi-prime extension ────────────────────────────────────────────────────
#print axioms selbergNu_dominates
#print axioms card_joint_multiples_of_lcm
#print axioms l2NormSq_multiPrime_eq_quadForm
#print axioms multiPrime_mass_eq_quadForm
#print axioms multiPrime_quadForm_lower_bound
#print axioms multiPrime_restriction_lower_bound

-- ── Extension 1: Sharp Mass-Energy Tradeoff ─────────────────────────────────
#print axioms selberg_l2_lower_bound

-- ── Extension 2: Correlation-Enhanced Additive Energy Lower Bound ───────────
#print axioms correlationSum_total_eq_sq
#print axioms sum_sq_ge_sq_div
#print axioms correlation_sum_approx_N
#print axioms mass_approx_N
#print axioms additiveEnergy_eq_sum_correlationSq
#print axioms correlation_additive_energy_lower

-- ── Extension 3: Quadratic Form Perturbation ────────────────────────────────
#print axioms multiPrimeQuadForm_perturbation

-- ── Extension 4: Sharp Fourier Ratio Lower Bound (novel) ───────────────────
#print axioms sieveMass_eq_quadForm
#print axioms real_l2NormSq_eq
#print axioms parseval_real
#print axioms fourier_zero_norm_sq
#print axioms nonzero_fourier_sum_eq
#print axioms exists_ge_of_sum_ge
#print axioms sharp_fourier_ratio_lower_bound

-- ── Extension 5: Correlation Definitions ─────────────────────────────────
#print axioms correlationBound_nonneg
#print axioms selbergNu_autocorrelation_eq_l2
