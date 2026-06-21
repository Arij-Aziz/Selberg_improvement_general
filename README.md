![Build](https://github.com/Arij-Aziz/Selberg_improvement_general/actions/workflows/build.yml/badge.svg)
# Selberg Majorant: Multi-Prime Extension — A Lean 4 Formalization

Machine-verified proofs extending the single-prime Selberg majorant
construction to arbitrary squarefree moduli, formalized in Lean 4 using
Mathlib. The Möbius-weight case is fully sorry-free; axiom footprint
verified as `[propext, Classical.choice, Quot.sound]` for all theorems
outside the one deferred step (see `RequestProject/Audit.lean` and
**Sorry Status** below).
Challenge.lean (root) is a statement-only mirror for the comparator check; 
its sorry proofs are intentional placeholders and are not part of the verified proof chain.

## What This Project Is

This project generalizes the single-prime Selberg majorant of
[Sieve-majorant-improvement](https://github.com/Arij-Aziz/Sieve-majorant-improvement)
to the **full multi-prime setting**: arbitrary squarefree P = p₁·····pₖ,
arbitrary Selberg weights λ on sqfDivisors(P), and the Möbius-weight
specialization g = 1/·, D = P.

The central object is the multi-prime Selberg majorant

    ν(x) = (Σ_{d ∈ sqfDivisors(P), d | gcd(x,P)} λ_d)²

and the multi-prime quadratic form

    Q(λ) = Σ_{d,e ∈ sqfDivisors(P)} λ_d λ_e / lcm(d,e)

The central identity of the project is `l2NormSq_multiPrime_eq_quadForm`:

    Σ_{x ∈ Fin(P·m)} ν(x) = (P·m) · Q(λ)

which holds for any squarefree P, any m ≥ 1, and any weight function λ.
Every other result in the project follows from this identity.

This is **not** the full Selberg sieve with arbitrary level D and general
density function. The optimal-weight result `Q(λ_opt) = 1/V(D)` for
general g and D carries a single `sorry` (a deferred Möbius inversion
argument); the Möbius-weight case Q(μ_P) = 1/V(1/·, P, P) is fully
proved from first principles.

## What This Project Is Not

- **Not an asymptotic result.** No primes, no density estimates, no big-O.
- **Not a proof that ν is the unique optimal majorant.** The project proves
  Möbius weights minimize Q(λ) among all λ with λ₁ = 1; it does not prove
  optimality in a broader function space.
- **Not a proof of Green–Tao or any additive combinatorics result.** The
  correlation and additive energy theorems are bounds about the sieve
  majorant itself. The instantiation of `correlation_additive_energy_lower`
  for `multiPrimeMajorant` (computing Σ_x ν(x)ν(x+h) explicitly) is a
  separate project, noted in the file.
- **Not a full formalization of Iwaniec–Kowalski §6.** The optimal-weight
  identity `optimalWeight_quadForm_eq` (IK eq. 6.70) is stated and its
  proof is deferred; all consequences that can be proved without it are
  proved.
- **`RequestProject/Future/`** is scaffolding only and is not part of the
  proof chain.

## Sorry Status

There is exactly **one `sorry`** in the project:

```
optimalWeight_quadForm_eq   (RequestProject/Core/MultiPrime/OptimalWeights.lean)
```

This states: for the optimal Selberg weights λ_d = μ(d)·V(D/d)/V(D),
the quadratic form satisfies Q(λ_opt) = 1/V(D).

This is Iwaniec–Kowalski eq. (6.70), Ford Theorem 4.1 p. 44, and
JTNB_2006 eq. (8.2). The mathematics is not in doubt. The Lean
formalization of the Möbius inversion argument on the squarefree divisor
lattice is deferred. The file header documents this explicitly.

**Everything that can be proved without this step is proved.**
The Möbius-weight specialization — where g = 1/· and D = P — is fully
proved separately via `optimalWeight_quadForm_eq_moebius`, which goes
through `moebius_quadForm_eq` (Q(μ_P) = φ(P)/P) and
`V_function_inv_eq_totient_ratio` (V(1/·,P,P) = P/φ(P)).

The connecting theorem `selberg_unified_connection` (general g, D) is
conditional on the sorry. The connecting theorem
`selberg_unified_connection_moebius` (Möbius weights) is fully sorry-free.

## Main Results

**Central Identity — Multi-Prime L² Identity**
(`Core/MultiPrime/L2Identity.lean`)

For any squarefree P, any m ≥ 1, and any weight λ:

    Σ_{x ∈ Fin(P·m)} ν(x)  =  (P·m) · Q(λ)

This is `l2NormSq_multiPrime_eq_quadForm`. The proof reduces to
`card_joint_multiples_of_lcm`: the count of x ∈ Fin(P·m) with d∣x
and e∣x equals P·m / lcm(d,e) for squarefree d,e dividing P.

**Theorem A — Möbius Weights and Optimality**
(`Core/MultiPrime/MoebiusWeights.lean`)

The Möbius weight function μ_P(d) = μ(d) for d ∈ sqfDivisors(P) satisfies:

    Q(μ_P) = φ(P)/P

proved by induction on prime factors of P using multiplicativity of μ and
the totient. Combined with `V_function_inv_eq_totient_ratio`:

    Q(μ_P) = 1/V(1/·, P, P)

For any λ with λ₁ = 1 supported on sqfDivisors(P):

    Q(λ) ≥ 1/V(1/·, P, P)

This is `multiPrimeQuadForm_lower_bound_inv`: Möbius weights minimize Q(λ).
The proof drops non-coprime terms in the L² identity and counts coprime
residues via `card_coprime_fin`.

**Theorem B — Sharp Mass–Energy Tradeoff**
(`Core/MassEnergyTradeoff/SharpBounds.lean`,
`Core/MassEnergyTradeoff/MassEnergySandwich.lean`,
`Core/MultiPrime/SelbergUpperBound.lean`)

For the multi-prime Selberg majorant at Möbius weights, with N = P·m:

    mass(ν)  =  N / V(1/·, P, P)             [selberg_mass_eq]

    ‖ν‖₂²  ≥  |S|⁴ · V(1/·,P,P)² / N³      [selberg_l2_sharp]

`selberg_l2_sharp` is derived from the general bound
`selberg_l2_lower_bound` (‖ν‖₂² ≥ |S|⁴ / (N³·Q(λ)²)) by substituting
Q(μ_P) = 1/V. Both are fully sorry-free. The same chain for arbitrary g
and D is given by `selberg_unified_connection`, conditional on
`optimalWeight_quadForm_eq`; the Möbius-weight version
`selberg_unified_connection_moebius` is unconditional.

To the authors' knowledge, no paper in the literature states this
mass–energy sandwich explicitly for sieve-constrained majorants.

**Theorem C — Coprime-Shift Correlation**
(`Core/MultiPrime/SelbergWeightCorrelation.lean`)

For the unsquared Selberg weight w(x) = Σ_{d ∈ sqfDivisors(P), d|gcd(x,P)} λ_d
and any shift h with gcd(h, P) = 1:

    Σ_{x ∈ Fin(P·m)} w(x) · w(x+h)  =  (P·m) · coprimePairsQuadForm(P, λ)

where coprimePairsQuadForm(P,λ) = Σ_{d,e ∈ sqfDivisors(P), gcd(d,e)=1} λ_d λ_e / (d·e).

Since coprimePairsQuadForm ≤ Q(λ) (as lcm(d,e) = d·e when gcd(d,e) = 1):

    Σ_{x ∈ Fin(P·m)} w(x) · w(x+h)  ≤  (P·m) · Q(λ)

The exact identity (`selbergWeight_correlation_coprime`) is proved via
the Chinese Remainder Theorem: when gcd(d,e) = 1, the count of x with
d∣gcd(x,P) and e∣gcd(x+h,P) is exactly P·m/(d·e); when gcd(d,e) > 1,
the count is 0 because a shared prime factor of d and e would divide h,
contradicting gcd(h,P) = 1.

**Theorem D — V-Function Kinetic Stability**
(`Core/KineticStability/VFunctionStability.lean`)

If two local density functions g, g' agree at each prime p | P to within ε
and are bounded by M, then:

    |V(g, P, D) − V(g', P, D)|  ≤  Σ_{d ∈ sqfDivisors(P), d≤D} |h_g(d) − h_{g'}(d)|

The proof uses `finset_prod_perturb` from `KineticPropagation.lean` to
bound the numerator and denominator changes in h(d) = g(d)/∏(1−g(p))
separately. The full statement for a `SievePerturbation` object is
`kinetic_V_stability`. This result is independent of and parallel to the
connecting theorem; it does not appear in the proof chain of
`selberg_unified_connection`.

No paper in kinetic theory or sieve theory states a stability theorem of
this type for the V-function, to the authors' knowledge.

**Theorem E — Multi-Prime Quadratic Form Perturbation**
(`Core/KineticStability/QuadFormPerturbation.lean`)

If |λ_d|, |μ_d| ≤ C and |λ_d − μ_d| ≤ δ_d for all d ∈ sqfDivisors(P):

    |Q(λ) − Q(μ)|  ≤  2C · Σ_{d,e ∈ sqfDivisors(P)} δ_d / lcm(d,e)

The algebraic engine is `prod_perturb`: |ac − bd| ≤ C·(|a−b| + |c−d|).

**Extension — Sharp Fourier Ratio Lower Bound**
(`Core/MultiPrime/FourierRatioSharp.lean`)

For the multi-prime Selberg majorant on Fin(N) with mass M = N·Q(λ):

    ∃ ξ ≠ 0,  |ν̂(ξ)|²  ≥  (N · ‖ν‖₂² − M²) / (N − 1)

This is `sharp_fourier_ratio_lower_bound`. The proof applies Parseval to
separate the zero mode (|ν̂(0)|² = M²) from the nonzero modes, then uses
a pigeonhole lemma (`exists_ge_of_sum_ge`) over the N−1 nonzero
frequencies. Green–Tao 2006 Prop. 3.1(iv) bounds |ν̂(ξ)| from above;
this bound goes in the opposite direction.

**Extension — Correlation-Enhanced Additive Energy Lower Bound**
(`Core/CorrelationBound/AdditiveEnergyLower.lean`)

For a `StrongPseudorandomMajorant` with correlationError ε and
averageCondition δ (ε < 1/2, δ < 1/4):

    E(ν)  ≥  N³ · (1 − 2ε − 4δ)

Proved via: E(ν) = Σ_h g(h)² (`additiveEnergy_eq_sum_correlationSq`),
Cauchy–Schwarz on the correlation sums, and the mass approximation.
Instantiation for `multiPrimeMajorant` — computing Σ_x ν(x)ν(x+h)
explicitly — is a separate project.

## The Connecting Theorem

`ConditionalConnection.lean` packages two versions of the proof chain:

- `selberg_unified_connection` — general g and D. Assumes
  `optimalWeight_quadForm_eq` (the one sorry) and derives both
  mass = N/V(g,P,D) and ‖ν‖₂² ≥ |S|⁴·V²/N³ by substituting the
  optimal quadratic form value directly into `multiPrime_mass_eq_quadForm`
  and `selberg_l2_lower_bound`.
- `selberg_unified_connection_moebius` — Möbius weights only. Fully
  sorry-free. One line: `exact ⟨selberg_mass_eq ..., selberg_l2_sharp ...⟩`.

The kinetic stability results (Theorems D and E) are parallel outputs of
the project, not steps in this chain.

## Selberg Upper Bound Infrastructure

(`Core/Weights/`, `Core/MultiPrime/RemainderBound.lean`,
`Core/MultiPrime/SelbergUpperBound.lean`)

The `Core/Weights/` directory provides the algebraic foundation on which
the upper bound machinery rests:

- `Weights/Definition.lean` — `SelbergWeights` structure; `sieveWeight`
  w(n) = Σ_{d ∈ D, d | gcd(n,P)} λ_d; `quadraticMajorantSum` Σ_n w(n)²
- `Weights/UpperBound.lean` — `siftedSet_card_le_quadraticSum`:
  |siftedSet| ≤ Σ_n w(n)²; `sieveWeight_coprime_eq`: w(n) = λ₁ = 1
  when gcd(n,P) = 1; `weighted_remainder_bound`
- `Weights/Bounds.lean` — Bounds on `sieveWeight` values
- `Weights/Optimization.lean` — Weight optimization lemmas
- `Weights/FourierConnection.lean` — Connection between sieve weights and
  Fourier structure
- `Weights/QuadFormStability.lean` — Quadratic form stability for weights

The complete Selberg upper bound is machine-verified in two complementary
forms. `selberg_upper_bound_complete` (`RemainderBound.lean`) is the general
form: for squarefree P, m ≥ 1, and a remainder function r satisfying
|{a ∈ range(P·m) : lcm(d,e) ∣ a}| = P·m/lcm(d,e) + r(lcm(d,e)),

    |{a ∈ [P·m] : gcd(a,P) = 1}|  ≤  (P·m)/V  +  moebiusRemainderBound(P, r)

where moebiusRemainderBound(P, r) = Σ_{d,e ∈ sqfDivisors P} |μ_P(d)| |μ_P(e)| |r(lcm(d,e))|.

The proof assembles: `siftedCount_le_quadraticMajorantSum` (from
`Weights/UpperBound.lean`), `quadraticMajorantSum_eq_mainTerm_plus_errorTerm`
(expand Σ w(n)² into N·Q(λ) plus double remainder sum), and
`double_error_le_moebiusRemainderBound`.

`selberg_upper_bound_multiPrime` (`SelbergUpperBound.lean`) is the
specialization to range(P·m) with zero remainder:

    |S(A, P)|  ≤  N / V(1/·, P, P)  +  moebiusRemainderBound(P, 0)

## A Machine-Verified Disproof

(`Core/MultiPrime/SelbergCorrelationBoundDisproved.lean`)

An earlier attempt proposed the following correlation bound for the
squared majorant ν (modeled on Green–Tao 2007 Proposition 9.1):

    |Σ_x ν(x)·ν(x+h) / N  −  Q(λ)|  ≤  correlationBound(P, m, λ, h)

for **all** squarefree P, all m ≥ 1, all λ with λ₁ = 1, and all shifts h.

This statement is false. `selbergNu_correlation_bound_is_false` gives a
machine-verified proof of its negation. The counterexample is
P = 2, m = 2 (N = 4), λ₁ = λ₂ = 1, h = 0: at this small scale the
residues are not equidistributed and the bound fails. The underlying
issue is that the equidistribution argument requires N to be large
relative to P; without this hypothesis the correlation sum can deviate
arbitrarily beyond the proposed bound.

The correct result — proved in `SelbergWeightCorrelation.lean` — is the
exact identity for the **unsquared** weight w(x) at **coprime** shifts h,
not for the squared majorant ν at all shifts.

## Auditable Statement File

`RequestProject/Statements.lean` is a self-contained reviewer file.
It has exactly one import (`import Mathlib`) and no `RequestProject.*`
imports. Every theorem introduced in this project is restated verbatim
with `sorry` as its proof body, with all project-internal definitions
reproduced inline using only Mathlib primitives. A reviewer can verify
every statement is well-typed by running:

```bash
lake build RequestProject.Statements
```

Expected output: zero errors; only `declaration uses sorry` warnings
(intended). The file covers exactly 19 new theorems, matching
`Audit.lean` exactly. The 20 theorems from Step 1 are explicitly
excluded and documented in the file header.

## Scope of Novelty

We are not aware of the following appearing in the literature in this form:

1. The L² identity `Σ_x ν(x) = N·Q(λ)` for general multi-prime squarefree P
   as a machine-verified theorem proved from counting arguments.
2. The identity `Q(μ_P) = φ(P)/P` proved from first principles by induction
   on prime factors of P, without appealing to Dirichlet series.
3. The mass–energy sandwich mass = N/V, ‖ν‖₂² ≥ |S|⁴·V²/N³ for the
   multi-prime Selberg majorant, to the authors' knowledge.
4. The exact coprime-shift correlation identity
   Σ_x w(x)·w(x+h) = N·coprimePairsQuadForm for the unsquared weights,
   proved via the Chinese Remainder Theorem.
5. A lower bound ∃ ξ ≠ 0, |ν̂(ξ)|² ≥ (N·‖ν‖₂²−mass²)/(N−1) for
   sieve-constrained majorants. Green–Tao 2006 Prop. 3.1(iv) gives an
   upper bound; this goes in the opposite direction.
6. A stability theorem for the V-function under prime-level perturbation,
   to the authors' knowledge.

We make no claim to have surveyed all literature exhaustively.

## Axiom Audit

All sorry-free theorems verified with `#print axioms`
(see `RequestProject/Audit.lean`). Expected footprint for each:
`[propext, Classical.choice, Quot.sound]`.

```
── §1. Multi-prime setup ───────────────────────────────────────────────────
selbergNu_dominates                     → [propext, Classical.choice, Quot.sound]
card_joint_multiples_of_lcm             → [propext, Classical.choice, Quot.sound]

── §2. Central Identity ────────────────────────────────────────────────────
l2NormSq_multiPrime_eq_quadForm         → [propext, Classical.choice, Quot.sound]

── §3. FourierRatio ────────────────────────────────────────────────────────
multiPrime_mass_eq_quadForm             → [propext, Classical.choice, Quot.sound]
multiPrime_quadForm_lower_bound         → [propext, Classical.choice, Quot.sound]
multiPrime_restriction_lower_bound      → [propext, Classical.choice, Quot.sound]

── §4. Möbius weights and optimality ───────────────────────────────────────
moebiusWeights_one                      → [propext, Classical.choice, Quot.sound]
moebius_quadForm_eq                     → [propext, Classical.choice, Quot.sound]
multiPrimeQuadForm_lower_bound'         → [propext, Classical.choice, Quot.sound]
optimalWeight_quadForm_eq_moebius       → [propext, Classical.choice, Quot.sound]
multiPrimeQuadForm_lower_bound_inv      → [propext, Classical.choice, Quot.sound]

── §5. Selberg upper bound and sharp L² bound ──────────────────────────────
selberg_upper_bound_multiPrime          → [propext, Classical.choice, Quot.sound]
selberg_l2_sharp                        → [propext, Classical.choice, Quot.sound]

── §6. Sharp mass–energy tradeoff ──────────────────────────────────────────
selberg_l2_lower_bound                  → [propext, Classical.choice, Quot.sound]

── §7. Coprime-shift correlation ───────────────────────────────────────────
coprimePairsQuadForm_le_multiPrimeQuadForm → [propext, Classical.choice, Quot.sound]
selbergWeight_correlation_coprime_bound → [propext, Classical.choice, Quot.sound]

── §8. Additive energy lower bound ─────────────────────────────────────────
additiveEnergy_lower_bound              → [propext, Classical.choice, Quot.sound]
restriction_lower_bound                 → [propext, Classical.choice, Quot.sound]
sieve_additive_energy_lower             → [propext, Classical.choice, Quot.sound]

── Connecting theorem (Möbius, sorry-free) ─────────────────────────────────
selberg_unified_connection_moebius      → [propext, Classical.choice, Quot.sound]

── Complete upper bound with remainder ─────────────────────────────────────
selberg_upper_bound_complete            → [propext, Classical.choice, Quot.sound]

── Machine-verified disproof ───────────────────────────────────────────────
selbergNu_correlation_bound_is_false    → [propext, Classical.choice, Quot.sound]

-- conditional on optimalWeight_quadForm_eq — sorryAx is EXPECTED
#print axioms selberg_mass_eq_general
#print axioms selberg_l2_lower_bound_general
#print axioms selberg_upper_bound_general
#print axioms selberg_unified_connection_general
-- Expected: [propext, Classical.choice, Quot.sound, sorryAx]

```

Classical logic only.

## AI Assistance

This project is a human–AI collaboration. Mathematical direction, theorem
statements, proof strategies, novelty identification, and scope decisions
were made by the human author. AI assistance was used for tactic search,
proof elaboration, and infrastructure lemmas. All mathematical claims were
decided and verified by the human author.

## Build

```bash
lake exe cache get
lake build
```

Requires Lean toolchain `leanprover/lean4:v4.28.0` (see `lean-toolchain`).

## File Map

```
RequestProject/
├── Audit.lean                              ← #print axioms for all new theorems
├── AssumptionsRegistry.lean                ← Manually maintained proof-status log
├── Main.lean                               ← Top-level imports
└── Core/
    ├── Basic.lean                          ← SieveData, squarefreeDivisors, UpperBoundSieve
    ├── Majorant.lean                       ← Abstract Majorant structure (mass, l2NormSq,
    │                                          targetMass, domination)
    ├── MajorantComparison.lean             ← Benchmark comparison structure
    ├── SelbergComparison.lean              ← Single-prime mass/L² improvement (Step 1)
    ├── SelbergRestriction.lean             ← Single-prime restriction instantiation
    ├── RestrictionLowerBound.lean          ← Abstract Cauchy–Schwarz restriction bound
    ├── RestrictionLowerBoundSelberg.lean   ← Selberg instantiation of restriction bound
    ├── KineticPropagation.lean             ← SievePerturbation, prod_perturb, H-functional,
    │                                          eulerProduct_stability, sieveH_stable
    ├── Fourier.lean                        ← DFT, Parseval, additiveEnergy
    ├── FourierRatio.lean                   ← Single-prime mass-energy tradeoff
    ├── Transference.lean                   ← PseudorandomMajorant structures (scaffolding)
    ├── ConditionalConnection.lean          ← selberg_unified_connection (conditional) +
    │                                          selberg_unified_connection_moebius (sorry-free)
    ├── Weights/
    │   ├── Definition.lean                 ← SelbergWeights structure; sieveWeight;
    │   │                                      quadraticMajorantSum
    │   ├── UpperBound.lean                 ← siftedSet_card_le_quadraticSum;
    │   │                                      sieveWeight_coprime_eq;
    │   │                                      weighted_remainder_bound
    │   ├── Bounds.lean                     ← Bounds on sieveWeight values
    │   ├── Optimization.lean               ← Weight optimization lemmas
    │   ├── FourierConnection.lean          ← Sieve weight / Fourier connection
    │   └── QuadFormStability.lean          ← Quadratic form stability for weights
    ├── MultiPrime/
    │   ├── Setup.lean                      ← sqfDivisors, selbergNu, sieveIndicator,
    │   │                                      domination
    │   ├── JointCount.lean                 ← card_joint_multiples_of_lcm
    │   ├── L2Identity.lean                 ← Central identity: Σν = N·Q(λ)
    │   ├── FourierRatio.lean               ← multiPrimeMajorant; mass = N·Q(λ)
    │   ├── FourierRatioSharp.lean          ← sharp_fourier_ratio_lower_bound
    │   ├── OptimalWeights.lean             ← hFunction, V_function,
    │   │                                      selbergOptimalWeights;
    │   │                                      optimalWeight_quadForm_eq (sorry here)
    │   ├── MoebiusWeights.lean             ← Q(μ_P)=φ(P)/P; minimality;
    │   │                                      optimalWeight_quadForm_eq_moebius
    │   ├── SelbergCorrelation.lean         ← correlationBound definition;
    │   │                                      autocorrelation lemmas
    │   ├── SelbergCorrelationBoundDisproved.lean
    │   │                                   ← selbergNu_correlation_bound_is_false
    │   │                                      (machine-verified disproof of blueprint C1)
    │   ├── SelbergWeightCorrelation.lean   ← Coprime-shift correlation identity (CRT proof);
    │   │                                      coprimePairsQuadForm_le_multiPrimeQuadForm
    │   ├── RemainderBound.lean             ← selberg_upper_bound_complete (general remainder)
    │   └── SelbergUpperBound.lean          ← selberg_upper_bound_multiPrime;
    │                                          selberg_l2_sharp
    ├── MassEnergyTradeoff/
    │   ├── SharpBounds.lean                ← selberg_l2_lower_bound:
    │   │                                      ‖ν‖₂² ≥ |S|⁴/(N³·Q²)
    │   └── MassEnergySandwich.lean         ← selberg_mass_eq: mass = N/V (Möbius weights)
    ├── CorrelationBound/
    │   └── AdditiveEnergyLower.lean        ← correlation_additive_energy_lower:
    │                                          E(ν) ≥ N³(1−2ε−4δ)
    └── KineticStability/
        ├── VFunctionStability.lean         ← kinetic_V_stability:
        │                                      V-function stability under SievePerturbation
        └── QuadFormPerturbation.lean       ← multiPrimeQuadForm_perturbation:
                                               |Q(λ)−Q(μ)| ≤ 2C·Σδ_d/lcm(d,e)

Future/                                     ← Scaffolding; not part of proof chain
formalization.yml                           ← Machine-readable project metadata
Challenge.lean                        ← Pure-Mathlib auditable statement file (sorry proofs) (has inline definitions)
Solution.lean                         ← File that only imports main.lean file
```
