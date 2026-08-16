# NSFormal — Machine Certificates for *Global Regularity for the Three-Dimensional Incompressible Navier–Stokes Equations on the Torus*

This Lean 4 project contains the machine-verified certificates accompanying the
paper *Global Regularity for the Three-Dimensional Incompressible Navier–Stokes
Equations on the Torus* (Jeffrey S. Cambria, ORCID 0009-0008-4226-2099). It
formalizes selected exact and algebraic displays from the proof: **54 original
kernel-checked theorems, zero unproven placeholders**, over a pinned, unmodified
Mathlib. The ongoing full-formalization work adds 160 topological,
measure-theoretic, differential, and analytic theorems, bringing the current total
to **214**.

The original certificates are supporting, not a formal proof of global regularity.
The new files formalize the PDE-facing argument far enough to expose the remaining
load-bearing mathematical gaps; see `FORMALIZATION.md`. In particular, the current
library does not prove global existence or the Clay statement.

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager). The toolchain (`leanprover/lean4:v4.33.0`) and the Mathlib
dependency (`v4.33.0`) are pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. To reproduce the verification:

```
lake exe cache get
lake build
```

A successful `lake build` is the verification: every theorem in the library
has been checked by the Lean kernel, and the library contains no `sorry`.

## Contents

| File | Theorems | Certifies |
| --- | ---: | --- |
| `NSFormal/Financing.lean` | 4 | the financing identity: the trace split, the sign tr(SW²), tr S³ = 3 det S, the pointwise assembly |
| `NSFormal/Lemma18.lean` | 4 | the exact pairing, its Cauchy–Schwarz step, the organization bound, the calibration factor 1/2 − (ln 2)/3 in closed form |
| `NSFormal/QT1Moment.lean` | 4 | the localized defect energy identity with its exact −1/4 scaling balance; the second-moment law and the Burgers equilibrium |
| `NSFormal/Lemmas27.lean` | 4 | the pancake discriminant identity; the veto S ẑ = 0; the odd parity kernel; the Rayleigh sign core |
| `NSFormal/CampaignAlgebra.lean` | 26 | the episode-machinery algebra (adiabatic boundary exponent, window slack, bootstrap root closure, log-norm assembly, cell-shell series, Hölder exponents, the superseded defect-gap dichotomy) and the closure inequalities of the repair lemmas: close pairs, background absorption, circularization, transit factor and chain fold, coherence inheritance, slice scaling, sector uniformity, depletion exponent, squeeze arithmetic |
| `NSFormal/NewProofAlgebra.lean` | 1 | the far-field exponent chain (x^{−1/3})^{−5/2} = x^{5/6} |
| `NSFormal/Integrals.lean` | 11 | the evaluated integrals: the Duhamel integral, the kernel tails ∫s⁻⁴ and ∫s⁻⁶, the Gram pairing ⟨r, W′⟩ = −2, the volume Chebyshev bound, the ℂ²-skew content of the episode gain, and the Fujita–Kato beta integral = π with its three supporting theorems |
| `NSFormal/Budget.lean` | 3 | the measure-theoretic Hölder estimate, its finite-time enstrophy-budget corollary, and the integrated three-term strain budget |
| `NSFormal/Domain.lean` | 2 | the concrete period-`2π`, three-dimensional torus and proofs that its whole space is nonempty and compact |
| `NSFormal/MaxEnvelope.lean` | 30 | attained spatial maxima on nonempty compact spaces; sup-norm Lipschitz continuity; maximizer sets; the compact-domain Danskin upper-Dini estimate; and constant- and variable-rate maximizer-only Grönwall closure |
| `NSFormal/Vorticity.lean` | 10 | first and second derivatives of vorticity magnitude and half squared magnitude; the corrected viscous evolution identities; favorable-sign inequalities; and conditional Grönwall closures |
| `NSFormal/VorticityMaximum.lean` | 9 | the continuous half-squared-vorticity field, its sup-norm derivative from a differentiable vorticity curve, and the corrected constant- and variable-rate maximizer-only parabolic maximum-principle closures |
| `NSFormal/PeriodicCalculus.lean` | 15 | the canonical periodic lift and representative; transport cancellation and scalar-Laplacian sign at torus maxima; nonnegative gradient square; and `⟪ω, Δω⟫ = Δ(|ω|²/2) - |∇ω|²` |
| `NSFormal/TorusVorticity.lean` | 7 | the corrected torus maximum principle, including variable-rate, vector-equation, time-integral, and explicit strain-budget closures |
| `NSFormal/NavierStokes.lean` | 17 | concrete and lifted torus differential operators; classical and jointly smooth velocity-pressure predicates; and zero-solution witnesses proving those interfaces nonvacuous |
| `NSFormal/VectorCalculus.lean` | 58 | Fréchet-coordinate reconstruction; mixed-partial, pressure, convection, Laplacian, and time-curl identities; and derivation of the classical vector-vorticity equation from smooth Navier--Stokes for a regular concrete curl field |
| `NSFormal/Stretching.lean` | 9 | the honest full-gradient and symmetric-strain bounds for `⟪ω,(ω·∇)u⟫`, plus their local-rate/maximizer wrappers |

`NSFormal/Basic.lean` is the standard project scaffold and contains no
mathematical content; the original 54 certificates live in the original seven files,
and the 160 new formalization theorems live in `Budget.lean`, `Domain.lean`,
`MaxEnvelope.lean`, `Vorticity.lean`, `VorticityMaximum.lean`,
`PeriodicCalculus.lean`, `TorusVorticity.lean`, `NavierStokes.lean`, and
`VectorCalculus.lean`, and `Stretching.lean`.

## License

CC BY 4.0. If you use these certificates, please cite the paper.
