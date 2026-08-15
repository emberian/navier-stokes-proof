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

**What is claimed, precisely.** The proof in the paper is a closed analytic argument.
The exact and algebraic core of that argument — every closed-form identity, sign,
coefficient chain, closure inequality, and evaluated integral the lemmas rest on — is
machine-verified here: **54 kernel-checked Lean 4 theorems, zero unproven placeholders,
over a pinned unmodified Mathlib**. The numerical instruments are supporting, not
load-bearing: they motivated and cross-checked the lemmas, but no step of the proof
consumes a numerical result. The analytic layer is rigorous prose in the paper; the
machine certificates strengthen it and do not substitute for any part of it.

## Contents

| path | contents |
|---|---|
| `paper/` | the paper source (`main.tex`, `refs.bib`) and the published PDF |
| `paper/zenodo-v001-r4/` | the frozen artifacts exactly as published on Zenodo, with SHA-256 manifests and OpenTimestamps `.ots` receipts |
| `lean/NSFormal/` | the Lean 4 + Mathlib machine certificates — `lake build` re-verifies all 54 theorems |
| `code/` | the symbolic-adjudication scripts (`sympy_*.py`) and the calibrated numerical instruments cited by the paper (see `code/README.md`) |
| `results/` | the archived output log of every script in `code/` |

## Verify the Lean certificates yourself

The Mathlib dependency is **never modified** — it is pinned by exact version
(`v4.33.0`) in `lean/NSFormal/lakefile.toml` and `lake-manifest.json`; the pinned Lean
toolchain is installed automatically from `lean-toolchain` by
[elan](https://github.com/leanprover/elan). All 54 theorems live in our own files under
`lean/NSFormal/NSFormal/`. To verify:

```
cd lean/NSFormal
lake exe cache get   # one-time: downloads the pinned Mathlib's prebuilt cache
lake build           # kernel-verifies every theorem
```

A successful build with no `sorry` warnings is the verification. Appendix C of the
paper maps each theorem to the display it certifies. The same build runs in CI on every
commit (`.github/workflows/lean.yml`).

## Reproduce the instruments

Python 3.12 with `numpy` + `scipy` + `sympy` only; every script is self-contained and
deterministic, and prints its registered gates with named outcomes:

```
python3 code/<script>.py        # regenerates its log in results/
```

`code/README.md` is the manifest: what each instrument measures, and which certificate
family each `sympy_*.py` script adjudicates.

## Integrity

`paper/zenodo-v001-r4/MANIFEST.sha256` fixes the exact bytes of the published
artifacts; the accompanying `.ots` files are OpenTimestamps receipts anchoring those
bytes in the Bitcoin blockchain (verify with `ots verify <file>.ots`).

## License and citation

CC BY 4.0 (see `LICENSE`). To cite, use `CITATION.cff` or cite the paper directly via
[doi:10.5281/zenodo.21959161](https://doi.org/10.5281/zenodo.21959161).
