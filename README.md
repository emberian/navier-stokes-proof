# Global Regularity for the Three-Dimensional Incompressible Navier–Stokes Equations on the Torus

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21959161.svg)](https://doi.org/10.5281/zenodo.21959161)
[![lean-verify](https://github.com/truthintime/navier-stokes-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/truthintime/navier-stokes-proof/actions/workflows/lean.yml)

**Jeffrey S. Cambria** · ORCID [0009-0008-4226-2099](https://orcid.org/0009-0008-4226-2099) · truthintime@tuta.io

This is the verification companion to the paper

> *Global Regularity for the Three-Dimensional Incompressible Navier–Stokes Equations
> on the Torus* — [doi:10.5281/zenodo.21959161](https://doi.org/10.5281/zenodo.21959161)

which proves global regularity for the spatially periodic case — statement (B) of the
official Clay Millennium formulation: every smooth, divergence-free initial velocity
field on the torus T³, with positive viscosity and zero external force, evolves into a
unique global smooth solution.

## Erratum (2026-08-16) — repair in progress

The first external review of this repository
([PR #1](https://github.com/truthintime/navier-stokes-proof/pull/1), ember arlynx)
identified a genuine error in the paper as published: the display D_t|ω| = α|ω| in
§3.1 is the *inviscid* identity — for ν > 0 the correct identity is
D_t|ω| = α|ω| + ν ξ·Δω — and the per-trajectory chain (§16.2) and the localization
step (§10, Step 3) rely on the defective shorthand as written. The author has
verified the finding independently (derivation and numerics). The omitted viscous
term has a favorable sign at spatial maximizers, and the repair — recasting the
chain on the maximum envelope ‖ω(t)‖∞, whose analytic skeleton is machine-checked in
the community formalization contributed in the same PR — is being carried out for a
revised version (v002) of the paper.

**Until v002 is published, the proof should be read as carrying a known,
credited, repair-in-progress gap:** the architecture (the exact laws, the linear
theory, the episode cap, the strain budget, and the rigidity squeeze) is unaffected,
but the chain section as written is not correct. This section will be updated when
the revision is published.

**What is claimed, precisely.** The proof in the paper is a closed analytic argument
(see the Erratum above for its current status). The exact and algebraic core of that
argument — every closed-form identity, sign, coefficient chain, closure inequality,
and evaluated integral the lemmas rest on — is machine-verified here: **54
kernel-checked Lean 4 theorems, zero unproven placeholders, over a pinned unmodified
Mathlib**. The numerical instruments are supporting, not load-bearing: they motivated
and cross-checked the lemmas, but no step of the proof consumes a numerical result.
The analytic layer is rigorous prose in the paper; the machine certificates
strengthen it and do not substitute for any part of it.

**The community formalization layer.** Beginning with PR #1 (ember arlynx), the
repository also hosts an in-progress formalization of the PDE-level argument itself:
**160 additional kernel-checked theorems** — a concrete period-2π torus, classical
Navier–Stokes and vorticity-equation predicates with nonvacuous witnesses, the
derived vector-vorticity equation, measure-theoretic strain-budget estimates, and
the maximum-envelope machinery (attained maxima, a compact-domain Danskin/Dini
theorem, corrected parabolic closures). This layer is distinct from the paper's 54
certificates: it does **not** yet prove global regularity, and its status and
dependency roadmap are tracked in `FORMALIZATION.md`.

## Contents

| path | contents |
|---|---|
| `paper/v001/` | the published paper v001: source (`main.tex`, `refs.bib`) and the published PDF |
| `paper/v001/zenodo-v001-r4/` | the frozen artifacts exactly as published on Zenodo, with SHA-256 manifests and OpenTimestamps `.ots` receipts |
| `lean/NSFormal/` | the Lean 4 + Mathlib development: the paper's 54 certificates and the community formalization layer — `lake build` re-verifies all of it |
| `FORMALIZATION.md` | the full-formalization roadmap and current proof obligations |
| `code/` | the symbolic-adjudication scripts (`sympy_*.py`) and the calibrated numerical instruments cited by the paper (see `code/README.md`) |
| `results/` | the archived output log of every script in `code/` |

## Verify the Lean development yourself

The Mathlib dependency is **never modified** — it is pinned by exact version
(`v4.33.0`) in `lean/NSFormal/lakefile.toml` and `lake-manifest.json`; the pinned Lean
toolchain is installed automatically from `lean-toolchain` by
[elan](https://github.com/leanprover/elan). All theorems live in our own files under
`lean/NSFormal/NSFormal/` — the paper's 54 certificates (mapped display-by-display in
Appendix C of the paper) and the community formalization files (inventoried in
`lean/NSFormal/README.md`). To verify:

```
cd lean/NSFormal
lake exe cache get   # one-time: downloads the pinned Mathlib's prebuilt cache
lake build           # kernel-verifies every theorem
```

A successful build with no `sorry` warnings is the verification. The same build runs
in CI on every commit (`.github/workflows/lean.yml`).

## Reproduce the instruments

Python 3.12 with `numpy` + `scipy` + `sympy` only; every script is self-contained and
deterministic, and prints its registered gates with named outcomes:

```
python3 code/<script>.py        # regenerates its log in results/
```

`code/README.md` is the manifest: what each instrument measures, and which certificate
family each `sympy_*.py` script adjudicates.

## Integrity

`paper/v001/zenodo-v001-r4/MANIFEST.sha256` fixes the exact bytes of the published
artifacts; the accompanying `.ots` files are OpenTimestamps receipts anchoring those
bytes in the Bitcoin blockchain (verify with `ots verify <file>.ots`). The repository
state at publication of paper v001 is permanently addressable at the git tag
[`paper-v001`](https://github.com/truthintime/navier-stokes-proof/tree/paper-v001).

## License and citation

CC BY 4.0 (see `LICENSE`). To cite, use `CITATION.cff` or cite the paper directly via
[doi:10.5281/zenodo.21959161](https://doi.org/10.5281/zenodo.21959161).
