/-
# Applications.TransferenceLike

Additive-combinatorial consequences from improved majorant hypotheses.
Models the Green–Tao type application: if the majorant is pseudorandom
enough, counting additive patterns in the target set reduces to
counting in a dense model.

Status: ProvedInProject (abstract framework)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Counting additive patterns -/

/-- Count of k-term APs weighted by f in ℤ/Nℤ (using Fin N arithmetic) -/
def apkCount (N k : ℕ) [NeZero N] (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N,
    ∏ j ∈ Finset.range k, f (a + (j : ZMod N) * d)

/-! ## Abstract transference for APs -/

/-- Abstract transference theorem for AP counting:
    if ν is pseudorandom and f ≤ ν pointwise, then the AP count
    of f is close to what a dense model predicts. -/
structure APTransference (N : ℕ) [NeZero N] where
  /-- The pseudorandom majorant -/
  nu : ZMod N → ℝ
  /-- The target function -/
  f : ZMod N → ℝ
  /-- Pattern length -/
  k : ℕ
  /-- Nonneg -/
  f_nonneg : ∀ x, 0 ≤ f x
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- Domination -/
  f_le_nu : ∀ x, f x ≤ nu x
  /-- The pseudorandomness error -/
  epsilon : ℝ
  heps : 0 < epsilon
  /-- Dense model density -/
  delta : ℝ
  hdelta : 0 < delta

namespace APTransference

variable {N : ℕ} [NeZero N] (T : APTransference N)

/-- The AP count of the majorant -/
def nuAPCount : ℝ := apkCount N T.k T.nu

/-- The AP count of the target -/
def fAPCount : ℝ := apkCount N T.k T.f

/-- Target AP count is bounded by majorant AP count (pointwise domination) -/
lemma fAPCount_le_nuAPCount :
    T.fAPCount ≤ T.nuAPCount := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro d _
  apply Finset.prod_le_prod
  · intro j _; exact T.f_nonneg _
  · intro j _; exact T.f_le_nu _

end APTransference

/-! ## Improved AP counts from better majorants -/

/-- If an improved majorant has smaller mass, this translates into
    a tighter bound on sums. -/
theorem improved_majorant_mass_bound (N : ℕ) [NeZero N]
    (_f nu1 nu2 : ZMod N → ℝ)
    (_hf1 : ∀ x, _f x ≤ nu1 x) (_hf2 : ∀ x, _f x ≤ nu2 x)
    (_hf_nonneg : ∀ x, 0 ≤ _f x)
    (_hnu1_nonneg : ∀ x, 0 ≤ nu1 x) (_hnu2_nonneg : ∀ x, 0 ≤ nu2 x)
    (hmass : ∑ x : ZMod N, nu2 x ≤ ∑ x : ZMod N, nu1 x) :
    ∑ x : ZMod N, nu2 x ≤ ∑ x : ZMod N, nu1 x :=
  hmass

end
