-- ExtensionsAudit.lean: axiom footprint for the three extensions.
-- Expected for each: [propext, Classical.choice, Quot.sound]

import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower
import RequestProject.Core.KineticStability.QuadFormPerturbation

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
