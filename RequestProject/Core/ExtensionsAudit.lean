-- ExtensionsAudit.lean: axiom footprint for all extensions.
-- Expected for each: [propext, Classical.choice, Quot.sound]

import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower
import RequestProject.Core.KineticStability.QuadFormPerturbation
import RequestProject.Core.MultiPrime.FourierRatioSharp

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
