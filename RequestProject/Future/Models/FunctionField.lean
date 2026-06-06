/-
# Models.FunctionField

Function-field analogue of the sieve architecture:
polynomials over finite fields as the validation environment.

Status: ProvedInProject (definitions and basic properties)
-/
import Mathlib

open Polynomial Finset BigOperators

noncomputable section

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- The "integers" in the function-field model: polynomials over 𝔽_q. -/
abbrev FqPoly := Polynomial (ZMod q)

/-- The "norm" (size) of a polynomial: q^(deg f) -/
def polyNorm (f : FqPoly q) : ℕ :=
  if f = 0 then 0 else q ^ f.natDegree

/-- Irreducible polynomials: the analogue of primes. -/
def isIrreduciblePoly (f : FqPoly q) : Prop :=
  Irreducible f

/-- Function-field sieve data. -/
structure FunctionFieldSieveData where
  n : ℕ
  d : ℕ
  hd : d ≤ n

namespace FunctionFieldSieveData
variable (S : FunctionFieldSieveData)

/-- The "X" parameter: q^n (total number of monic polynomials of degree n) -/
def mainTermFF : ℕ := q ^ S.n

/-- The density function: f(P) = q^(deg P) for irreducible P -/
def densityFunction (P : FqPoly q) : ℝ :=
  if P = 0 then 1 else (q : ℝ) ^ P.natDegree

end FunctionFieldSieveData

/-- In the function-field setting, the analogue of the Riemann Hypothesis
    is a theorem (Weil). This structure records the key bound. -/
structure FunctionFieldRH where
  n : ℕ
  modPoly : FqPoly q
  characterSumBound : ℝ
  hbound : characterSumBound ≤ (modPoly.natDegree - 1 : ℝ) * (q : ℝ) ^ (n / 2 : ℝ)

end
