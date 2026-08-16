# Formalization status

The checked Lean library in `lean/NSFormal` now includes a concrete period-`2π`
three-torus, continuous scalar and vector fields on it, compact spatial maxima,
measure-theoretic budget estimates, and corrected pointwise and maximum-envelope
vorticity evolution theorems.  It also defines first and second coordinate
derivatives through the canonical periodic lift to `ℝ³`, concrete gradient,
divergence, curl, transport, stretching, and vector-Laplacian operators, and a
pointwise classical Navier--Stokes predicate.  It does **not** yet define velocity or
pressure Sobolev regularity classes, the Leray projection, suitable weak solutions,
vortex tubes, episode boundaries, or a blow-up criterion.

The formalization must therefore proceed from the PDE layer upward.  The intended
dependency order is:

1. periodic vector fields, derivatives, integration, and the Leray projection
   (the compact domain, continuous fields, periodic lift, and the maximum-principle
   differential operators are complete; integration, general function spaces, and
   projection infrastructure remain);
2. smooth Navier--Stokes solutions and the vorticity equation (complete for a
   jointly smooth lifted solution and a regular concrete curl field, with all
   pressure, convection, Laplacian, and time commutators derived);
3. the energy/enstrophy and vorticity-magnitude identities;
4. precise replacements for the paper's geometric notions (structure, tube, active
   scale, episode, event, organization, and tangle);
5. the linear column and episode estimates;
6. classification, strain budget, trajectory/maximal-vorticity estimate, and BKM;
7. suitable weak solutions, rescaling compactness, confinement, quantitative
   rigidity, and the final contradiction.

## First analytic layer

`NSFormal/Budget.lean` proves the actual measure-theoretic Hölder estimate used in
the time-integrated strain budget,

\[
  \int \Omega^{5/6}\,d\mu
  \le
  \left(\int \Omega\,d\mu\right)^{5/6}
  \mu(\mathrm{univ})^{1/6},
\]

for nonnegative integrable `Ω` on a finite measure space.  This replaces the prior
certificate `w10_holder_exponents`, which checked only `5/6 + 1/6 = 1`.

Its finite-time closure proves, from a genuine set-integral enstrophy budget and a
continuous pointwise rate inequality,

\[
  \int_0^T \gamma
  \le C_5 B^{5/6}T^{1/6}+C_1B+C_0T.
\]

`NSFormal/Vorticity.lean` formalizes the derivative of the norm of a nonzero path,
the correct viscous vorticity-magnitude evolution, the favorable-sign inequality,
and its Grönwall closure.  In particular, it proves an exponential bound under the
explicit hypotheses that the viscous pairing is nonpositive and the directional
stretching rate is bounded.  It does not assume that the viscous sign holds along an
arbitrary trajectory.

## Compact-domain maximum-principle layer

`NSFormal/Domain.lean` defines the actual period-`2π` three-torus
`Fin 3 → AddCircle (2π)`, supplies an explicit origin, and verifies nonemptiness and
compactness.  Spatial maximum theorems therefore cannot be discharged through an
empty domain or an assumed inhabitant.

`NSFormal/MaxEnvelope.lean` constructs an attained maximum for every continuous
real field on a nonempty compact space.  It proves that the maximum operator is
`1`-Lipschitz in the sup norm, defines the nonempty compact maximizer set, and proves
a compact-domain Danskin theorem: if a time curve of fields is differentiable in
the sup norm, then the upper right Dini slopes of its maximum envelope are bounded
by the largest time derivative among the current maximizers.  Its Grönwall theorem
requires the production inequality only on that maximizer set; it never differentiates
a chosen maximizing point.
It also proves the variable-coefficient form with exponent `exp (∫ k)`, using an
integrating factor with an actual differentiable primitive.

`NSFormal/VorticityMaximum.lean` uses the smooth scalar `|ω|²/2`, avoiding the
singular direction `ω/|ω|` at zeros.  It proves that sup-norm differentiability of
`ω(t,·)` implies sup-norm differentiability of this energy field with pointwise
derivative `⟪ω, ∂ₜω⟫`.  It then checks the corrected parabolic closure

\[
  \partial_t(|\omega|^2/2)
  = \text{stretching}
    + \nu\bigl(\Delta(|\omega|^2/2)-|\nabla\omega|^2\bigr)
    - \text{transport},
\]

under explicit maximizer facts: transport is zero, the scalar Laplacian is
nonpositive, the gradient-square term is nonnegative, and stretching has the stated
bound.

`NSFormal/PeriodicCalculus.lean` constructs the quotient covering map, a canonical
fundamental-cube representative, and periodic lifts to `ℝ³`.  It proves with Fermat's
and Taylor's theorems that transport vanishes and the scalar Laplacian is nonpositive
at every torus maximizer.  It defines `|∇ω|²`, proves its nonnegativity, and derives
the exact identity

\[
  \langle\omega,\Delta\omega\rangle
  = \Delta(|\omega|^2/2)-|\nabla\omega|^2.
\]

`NSFormal/TorusVorticity.lean` instantiates the compact maximum theorem with these
periodic facts.  Its strongest theorem begins from the vector vorticity equation,
derives the corrected scalar energy equation by pairing with `ω`, and discharges
transport, Laplacian, and gradient-dissipation signs.  It now composes that theorem
with the integrated strain budget to give the explicit repaired finite-time maximum
bound.

## Concrete Navier--Stokes layer

`NSFormal/NavierStokes.lean` defines the classical velocity-pressure equation and
incompressibility on the concrete torus using the canonical lifted derivatives.  It
separately defines “vorticity is curl of velocity” and the viscous vector-vorticity
equation.  These are propositions over explicit fields, not an assumed solution
typeclass.  For every positive viscosity, Lean constructs zero velocity, pressure,
and vorticity fields satisfying all three predicates simultaneously.  This witness
rules out proofs that succeed only because a formal solution type is empty.

`NSFormal/VectorCalculus.lean` now discharges the full differential derivation.  It
reconstructs coordinate derivatives from the Fréchet derivative, proves the
incompressible convection-curl identity, proves curl--Laplacian commutation from
third derivatives, proves time--curl commutation from joint time-space smoothness,
eliminates pressure, and derives `IsClassicalVorticityEquationOn` from
`IsSmoothNavierStokesOn` for every regular concrete field equal to curl on the
periodic lift.  Both predicates have explicit zero witnesses.

`NSFormal/Stretching.lean` proves the unconditional elementary bound

\[
  \langle\omega,(\omega\cdot\nabla)u\rangle
  \le 2\|\nabla u\|_{\mathrm{op}}\,\frac{|\omega|^2}{2}.
\]

Thus the remaining stretching obligation is sharply isolated: the paper must derive
an integrable scalar rate dominating the local velocity-gradient norm at current
vorticity maximizers.  The claimed geometric organization/column/episode machinery
is intended to provide that rate, but its load-bearing analytic estimates remain
unformalized (the paper proves them in prose in Part II; none is yet machine-checked).

## Blocking proof obligations found in the paper

These are mathematical obligations, not merely missing Lean library plumbing.

### Viscous vorticity magnitude

Section `subsec:notation` states

\[
  D_t|\omega|=\alpha|\omega|.
\]

For positive viscosity and at points where `ω ≠ 0`, the identity is instead

\[
  D_t|\omega|
  =\alpha|\omega|+\nu\,\xi\mathbin\cdot\Delta\omega
  =\alpha|\omega|+\nu(\Delta|\omega|-|\omega||\nabla\xi|^2).
\]

Consequently `pf:ft` cannot begin with the asserted ordinary differential equation
along an arbitrary flow trajectory.  At a spatial maximum the viscous terms have a
favorable sign, so a maximum-principle argument may support a theorem about
`‖ω(t)‖∞`; it does not by itself support the paper's per-trajectory partition or its
localization step.

The pointwise identity, the regular maximal-vorticity envelope, the upper-Dini
argument, and the conditional squared-vorticity maximum principle are now checked in
`NSFormal/Vorticity.lean`, `NSFormal/MaxEnvelope.lean`, and
`NSFormal/VorticityMaximum.lean`, `NSFormal/PeriodicCalculus.lean`, and
`NSFormal/TorusVorticity.lean`.  The periodic transport, scalar-Laplacian, and
gradient-dissipation facts, and the vector vorticity equation are now derived.  The
remaining obligation is the claimed integrable geometric stretching rate.  None is
inferred from the invalid trajectory equality.

### Undefined geometric predicates

`def:class`, `def:trichotomy`, `lem:dc`, and the event-counting arguments quantify
over “structures,” “coherent tubes,” “mergers,” “re-entry,” and “persistent
pairing” without mathematical definitions of those objects or measurable predicates.
These must be defined before the classification and budget statements have Lean
propositions to express.

### Linear and nonlinear column estimates

The arguments in `pf:band`, `pf:r1b`, and `pfsec:jc1` assert uniform resolvent,
critical-layer, parametrix, smoothing, modulation, and nonlinear bootstrap bounds.
The displayed calculations do not provide the function spaces, operator domains,
boundary conditions, constants, or estimates needed to derive those results.  Each
is a substantial theorem family and is currently an assumption from the perspective
of a formal proof.

### Confinement and quantitative rigidity

`pf:confine` assumes an invariant stable/unstable bundle decomposition and states
that no other neutral directions exist; no preceding theorem constructs that
splitting.  `pf:qt` asserts a quantitative extension of the cited stationary
rigidity theorem, including a ray expansion, perturbed maximum principle, and flux
estimate.  Those quantitative statements are new load-bearing lemmas; the paper proves them
in prose (§§17.2–17.3) and they are not yet formalized; the scalar Lean identities
in `QT1Moment.lean` do not establish them.

### CKN nontriviality floor

`pf:bridge` quotes a lower bound for the scale-invariant quantity containing both
`|u|³` and `|p|^(3/2)`, then states a lower bound for `|V|³` alone.  A pressure
decomposition estimate that justifies removing the pressure term is required and is
not supplied at that step.

Until these obligations are discharged, an honest Lean end theorem can only be
conditional on them.  The project must not introduce them as axioms and then present
the resulting conditional assembly as a formal proof of global regularity.
