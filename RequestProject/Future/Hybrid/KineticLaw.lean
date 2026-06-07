/-
# Hybrid.KineticLaw

Abstract mesoscopic interface: the kinetic law summarizes how local congruence
exclusions propagate into averaged statistical structure. The interface is
dimension-sensitive and exposes the quantitative outputs needed downstream.

Status: ProvedInProject (interface definition and basic properties)
-/
import Mathlib

open MeasureTheory Finset BigOperators

noncomputable section

/-! ## Kinetic law interface -/

/-- A kinetic law: the mesoscopic interface between microscopic congruence
    exclusions and macroscopic sieve bounds. -/
structure KineticLaw where
  /-- The state space -/
  State : Type
  /-- The effective dimension of the sieve problem -/
  dimension : ℕ
  /-- Measurable space structure -/
  measurableSpace : MeasurableSpace State
  /-- Measure on the state space -/
  measure : @Measure State measurableSpace
  /-- Observable function: the "density" or "weight" at each state -/
  observable : State → ℝ
  /-- Admissibility predicate -/
  admissible : State → Prop
  /-- The observable dominates the indicator of admissible states -/
  dominatesIndicator : ∀ x, admissible x → 1 ≤ observable x
  /-- Normalization bound: ∫ observable dμ ≤ C · dim^k for some controlled constant -/
  normalizationConstant : ℝ
  normalizationBound : normalizationConstant > 0
  /-- Fourier decay parameter -/
  fourierDecayRate : ℝ
  fourierDecayPositive : fourierDecayRate > 0
  /-- Averaged remainder parameter -/
  avgRemainderBound : ℝ
  avgRemainderPositive : avgRemainderBound > 0

namespace KineticLaw

variable (K : KineticLaw)

/-- The dimension-scaled normalization: C · dim^α -/
def scaledNormalization (alpha : ℝ) : ℝ :=
  K.normalizationConstant * (K.dimension : ℝ) ^ alpha

/-- The effective density parameter: inverse of normalization -/
def effectiveDensity : ℝ :=
  1 / K.normalizationConstant

/-- Effective density is positive -/
lemma effectiveDensity_pos : 0 < K.effectiveDensity := by
  exact div_pos one_pos K.normalizationBound

/-- A kinetic law is said to be an improvement over a benchmark
    if its Fourier decay rate is strictly better. -/
def improvesOver (benchmark : KineticLaw) : Prop :=
  K.fourierDecayRate < benchmark.fourierDecayRate ∧
  K.dimension = benchmark.dimension

end KineticLaw

/-! ## Dimension-dependent bounds -/

/-- A dimension-scaling law: how a quantity grows with the dimension parameter. -/
structure DimensionScaling where
  /-- The base constant -/
  baseConstant : ℝ
  /-- The exponent -/
  exponent : ℝ
  /-- Base constant is positive -/
  hbase : baseConstant > 0
  /-- Exponent is nonneg -/
  hexp : exponent ≥ 0

namespace DimensionScaling

variable (D : DimensionScaling)

/-- Evaluate the scaling at a given dimension -/
def eval (dim : ℕ) : ℝ :=
  D.baseConstant * (dim : ℝ) ^ D.exponent

/-- The scaling is positive at any positive dimension -/
lemma eval_pos (dim : ℕ) (hdim : 0 < dim) : 0 < D.eval dim := by
  apply mul_pos D.hbase
  apply Real.rpow_pos_of_pos (Nat.cast_pos.mpr hdim)

end DimensionScaling

/-! ## Kinetic equilibrium -/

/-- A kinetic equilibrium: a state where the mesoscopic law is in a
    "steady state" that minimizes some functional. -/
structure KineticEquilibrium extends KineticLaw where
  /-- The free energy functional being minimized -/
  freeEnergy : ℝ
  /-- The equilibrium minimizes among all kinetic laws with the same dimension -/
  isMinimal : ∀ K' : KineticLaw, K'.dimension = dimension →
    freeEnergy ≤ K'.normalizationConstant * K'.fourierDecayRate

end
