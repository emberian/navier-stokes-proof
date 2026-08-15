# Verification code — manifest

Python 3.12, `numpy` + `scipy` + `sympy` only. No virtual environment needed. Every
script is self-contained and deterministic; each prints its registered gates with named
outcomes, and its archived output log lives in `../results/` under the same stem.

These scripts are **supporting, not load-bearing** (paper, Section 11): the proof
stands entirely on the analytic chain, and no step of it consumes a numerical result.

## Symbolic adjudication (`sympy_*.py`)

Every algebraic claim in the paper passed through this layer before Lean
formalization: derivations solved symbolically, identities checked exactly, and every
disagreement between the desk mathematics and the machine resolved in writing before
the corresponding Lean certificate was attempted (paper, Section 11.2). Each script
adjudicates the certificate family its name carries — `sympy_financing.py` the
financing identity; `sympy_qt1_moment.py` the localized defect energy identity (the
exact −1/4 balance) and the moment law; `sympy_rulers.py` the calibration constant
1/2 − (ln 2)/3; the `sympy_w*.py` series the episode estimates (kernel tails, parity,
gain, adiabatic window, bootstrap root, shell series); and the `sympy_sc*.py` series
the closure inequalities of the review-campaign repair lemmas (background absorption,
close pairs, circularization, transit factor, coherence inheritance, squeeze
arithmetic, slice scaling, sector uniformity and depletion). The tee'd log beside each
script is its adjudication record.

## Numerical instruments

Direct-numerical-simulation gates and calibrated rulers (paper, Section 11.3). Each
quoted number sits on a named instrument with its tolerance stated in its log.

| script | measures |
|---|---|
| `l19_gate.py` | production vs polarization-coherence bins on an evolved field, with phase-randomized control |
| `l19_gate2.py` | the nematic organization discriminator C_n; antiparallel-pair validation; dichotomy census |
| `l19r_gate.py` | fast-tangle drain and the basin test (randomize → re-evolve) |
| `l19r3_gate.py` | the 3:1-law fragility clock (production-field vs enstrophy-field decorrelation) |
| `l14_residual_gate.py` | the matched approximation's residual directly against the ν^{1/3} law (measured exponent 0.387) |
| `l16_block_gate.py` | coupled strained-operator centroid control; the crossing eigensolve (recorded void — the instrument lesson kept) |
| `l16_block_gate2.py` | Riesz projection at the isolated Kelvin resonance; the O(ν) damping law |
| `l16_block_gate3.py` | the grower method at the crossing; the 2×2 normal-form fingerprint |
| `l16_qscan.py` | band-center location and slope (q-scan) |
| `l3d_indicial_gate.py` | the swirl vanishing law: local exponent fits vs 2D control |
| `l3d_control_fix.py` | artifact-free layer-point scaling (fixed-reference) |
| `l3d_exact_gate.py` | 8-point Re scan of the swirl exponent; two-branch interference identified |
| `l3d_exact_fit2.py` | the locked-exact test: exponent 1/6 and interference frequency 2μ/3 both exact, parameter-free |
| `l17_worm_gate.py` | the episode-cap clauses on a real DNS worm: veto cap, Burgers radius, coherence |
| `l17_worm_gate2.py` | δ² estimator calibration (N=64 — proved quantization-limited) |
| `l17_worm_gate3.py` | recalibration at N=128 with sub-cell tracer; worm curvature |
| `l17_worm_gate4.py` | position-locked worm across snapshots; Burgers budget and stable radius |
| `l17_strain_split.py` | the Biot–Savart split α_self vs α_ambient on the tracked core — the veto measured on a real bent worm |
| `l17_profile_ruler.py` | transverse flatness of the core profile (Gaussian verification of the ruler) |
| `l17_ruler_review.py` | ruler audit: corrected references; strain-split verified exact |
| `l17_profile_cut.py` | canonical core-profile cut: the 1.9:1 elliptical core and the exact-standard radius measurement |
| `sweep_b.py` | the headline-figure trace: every quoted number resolved to its instrument log |
