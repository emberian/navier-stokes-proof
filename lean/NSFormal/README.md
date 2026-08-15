# NSFormal — Machine Certificates for *Global Regularity for the Three-Dimensional Incompressible Navier–Stokes Equations on the Torus*

This Lean 4 project contains the machine-verified certificates accompanying the
paper *Global Regularity for the Three-Dimensional Incompressible Navier–Stokes
Equations on the Torus* (Jeffrey S. Cambria, ORCID 0009-0008-4226-2099). It
formalizes the exact and algebraic core of the proof — every closed-form
identity, sign, coefficient chain, closure inequality, and evaluated integral
that the lemmas rest on: **54 kernel-checked theorems, zero unproven
placeholders**, over a pinned, unmodified Mathlib.

The certificates are supporting, not load-bearing: the proof in the paper is a
closed analytic argument, and no step of it consumes a numerical result. Each
theorem here certifies the algebraic content of a specific display in the
paper; the mapping is given in Appendix C of the paper (Index of machine
certificates).

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

`NSFormal/Basic.lean` is the standard project scaffold and contains no
mathematical content; the 54 theorems live in the seven files above.

## License

CC BY 4.0. If you use these certificates, please cite the paper.
