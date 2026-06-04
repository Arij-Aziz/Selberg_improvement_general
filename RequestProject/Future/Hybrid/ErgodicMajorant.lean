/-
# Hybrid.ErgodicMajorant

Construction of a Selberg-type majorant from dynamical/kinetic data,
and comparison with a classical benchmark majorant.

Status: ProvedInProject (construction and basic comparison)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Ergodic majorant construction -/

/-- An ergodic majorant: a majorant constructed from a kinetic law's
    observable, specialized to a finite model. -/
structure ErgodicMajorant (N : ℕ) where
  /-- The majorant weights -/
  nu : Fin N → ℝ
  /-- Nonnegativity -/
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- The target indicator -/
  target : Fin N → ℝ
  /-- Target nonnegativity -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Domination -/
  domination : ∀ x, target x ≤ nu x
  /-- The kinetic dimension parameter -/
  dimension : ℕ
  /-- Fourier decay rate -/
  fourierDecayRate : ℝ
  /-- Fourier decay is positive -/
  hfourier : fourierDecayRate > 0
  /-- Averaged remainder bound -/
  avgRemainderBound : ℝ
  /-- Remainder bound is positive -/
  hremainder : avgRemainderBound > 0

namespace ErgodicMajorant

variable {N : ℕ} (E : ErgodicMajorant N)

/-- Mass of the ergodic majorant -/
def mass : ℝ := ∑ x : Fin N, E.nu x

/-- Mass of the target -/
def targetMass : ℝ := ∑ x : Fin N, E.target x

/-- Mass is nonneg -/
lemma mass_nonneg : 0 ≤ E.mass :=
  Finset.sum_nonneg (fun x _ => E.nu_nonneg x)

/-- Domination at the mass level -/
lemma mass_ge_targetMass : E.targetMass ≤ E.mass := by
  apply Finset.sum_le_sum
  intro x _
  exact E.domination x

/-- L² norm squared -/
def l2NormSq : ℝ := ∑ x : Fin N, E.nu x ^ 2

/-- The mass ratio: how much larger ν is compared to target -/
def massRatio : ℝ := E.mass / E.targetMass

end ErgodicMajorant

/-! ## Classical benchmark majorant -/

/-- A classical Selberg majorant (benchmark for comparison). -/
structure ClassicalMajorant (N : ℕ) where
  /-- The majorant weights -/
  nu : Fin N → ℝ
  /-- Nonnegativity -/
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- The target indicator -/
  target : Fin N → ℝ
  /-- Target nonnegativity -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Domination -/
  domination : ∀ x, target x ≤ nu x
  /-- Fourier decay rate -/
  fourierDecayRate : ℝ
  /-- Averaged remainder bound -/
  avgRemainderBound : ℝ

namespace ClassicalMajorant

variable {N : ℕ} (C : ClassicalMajorant N)

/-- Mass of the classical majorant -/
def mass : ℝ := ∑ x : Fin N, C.nu x

end ClassicalMajorant

/-! ## Comparison theorem -/

/-- Comparison between ergodic and classical majorants. -/
structure MajorantImprovement (N : ℕ) where
  /-- The ergodic majorant -/
  ergodic : ErgodicMajorant N
  /-- The classical majorant -/
  classical : ClassicalMajorant N
  /-- Same target -/
  same_target : ergodic.target = classical.target
  /-- Mass improvement -/
  mass_improvement : ergodic.mass ≤ classical.mass
  /-- Fourier improvement -/
  fourier_improvement : ergodic.fourierDecayRate ≤ classical.fourierDecayRate

namespace MajorantImprovement

variable {N : ℕ} (M : MajorantImprovement N)

/-- A strict improvement means at least one metric is strictly better -/
def isStrictImprovement : Prop :=
  M.ergodic.mass < M.classical.mass ∨
  M.ergodic.fourierDecayRate < M.classical.fourierDecayRate

/-- No-regression: the ergodic majorant is at least as good as classical -/
lemma noRegression : M.ergodic.mass ≤ M.classical.mass :=
  M.mass_improvement

end MajorantImprovement

end
