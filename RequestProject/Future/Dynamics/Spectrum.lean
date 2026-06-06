/-
# Dynamics.Spectrum

Ergodic rotations, observable averages, and spectral packaging
for sieve-state dynamics.

Status: ProvedInProject (definitions and basic spectral properties)
-/
import Mathlib

open Finset BigOperators Complex

noncomputable section

/-! ## Characters on ZMod m -/

/-- A multiplicative character on ZMod m via exponential map. -/
def additiveChar' (m : ℕ) [NeZero m] (k : ZMod m) : ZMod m → ℂ :=
  fun x => Complex.exp (2 * Real.pi * Complex.I * (ZMod.val x * ZMod.val k : ℝ) / m)

/-- Character at k=0 is identically 1 -/
lemma additiveChar'_zero (m : ℕ) [NeZero m] :
    additiveChar' m 0 = fun _ => 1 := by
  ext x
  simp [additiveChar', ZMod.val_zero]

/-! ## Spectral decomposition of observables -/

/-- Fourier coefficient of an observable at character k -/
def fourierCoeff' (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) (k : ZMod m) : ℂ :=
  ∑ x : ZMod m, (obs x : ℂ) * starRingEnd ℂ (additiveChar' m k x)

/-- An observable is spectrally concentrated at a set of characters
    if most of its L² energy is captured by those characters. -/
def spectrallyConcentrated (m : ℕ) [NeZero m] (obs : ZMod m → ℝ)
    (S : Finset (ZMod m)) (eta : ℝ) : Prop :=
  ∑ k ∈ Finset.univ \ S, ‖fourierCoeff' m obs k‖ ^ 2 ≤ eta * (m : ℝ) ^ 2

/-! ## Ergodic averages -/

/-- The time average of an observable along an orbit -/
def orbitAverage (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) (x₀ : ZMod m)
    (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, obs (x₀ + (t : ZMod m))) / T

/-- The space average of an observable -/
def spaceAverage (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) : ℝ :=
  (∑ x : ZMod m, obs x) / m

/-
For a full orbit (T = m), orbit average equals space average
-/
lemma orbit_avg_eq_space_avg (m : ℕ) [hm : NeZero m]
    (obs : ZMod m → ℝ) (x₀ : ZMod m) :
    orbitAverage m obs x₀ m = spaceAverage m obs := by
  convert congr_arg ( fun x : ℝ => x / m ) ( show ∑ x ∈ Finset.range m, obs ( x₀ + x ) = ∑ x : ZMod m, obs x from ?_ ) using 1;
  rcases m with ( _ | m ) <;> simp_all +decide [ Finset.sum_range, ZMod ];
  · exact False.elim <| NeZero.ne 0 rfl;
  · exact Equiv.sum_comp ( Equiv.addLeft x₀ ) _

/-! ## Spectral gap and mixing -/

/-- Spectral gap: the largest nontrivial Fourier coefficient is small. -/
def hasSpectralGap (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) (gap : ℝ) : Prop :=
  ∀ k : ZMod m, k ≠ 0 → ‖fourierCoeff' m obs k‖ ≤ gap

/-- Mixing rate: largest nontrivial Fourier coefficient normalized -/
def mixingRate (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨(0 : ZMod m), Finset.mem_univ _⟩
    (fun k => if k = (0 : ZMod m) then 0 else ‖fourierCoeff' m obs k‖ / m)

end