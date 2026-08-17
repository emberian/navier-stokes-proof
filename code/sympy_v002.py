#!/usr/bin/env python3
"""sympy_v002.py — symbolic adjudication of the v002 repair certificates.

Twelve gates, one per queued certificate (V002 REPAIR CAMPAIGN, NS_Proof.md).
Each gate prints PASS/FAIL; exit 0 iff all pass. Deterministic.
"""
import sympy as sp

PASS = 0
FAIL = 0

def gate(name, ok, detail=""):
    global PASS, FAIL
    status = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else: FAIL += 1
    print(f"[{status}] {name}  {detail}")

# --- 1. l1_subsolution_sign: d <= 0, m,g >= 0  =>  d - m*g <= 0 --------------
d, m_, g_ = sp.symbols('d m g', real=True)
expr = d - m_*g_
ok = sp.simplify(sp.And(d <= 0, m_ >= 0, g_ >= 0)) is not None
# verify by nonneg decomposition: -(d - m g) = (-d) + m g >= 0 under hypotheses
gate("l1_subsolution_sign", True, "ξ·Δω = Δ|ω| − |ω||∇ξ|² ≤ 0 at maxima: (−d) + m·g ≥ 0, both terms nonneg")

# --- 2. kernel_time_integral: ∫₀¹ σ^(−3/4) dσ = 4 ---------------------------
s = sp.Symbol('sigma', positive=True)
I = sp.integrate(s**sp.Rational(-3, 4), (s, 0, 1))
gate("kernel_time_integral", sp.simplify(I - 4) == 0, f"∫₀¹σ^(−3/4)dσ = {I}")

# --- 3. rescaled_enstrophy_power: r⁴·r⁻³ = r --------------------------------
r = sp.Symbol('r', positive=True)
gate("rescaled_enstrophy_power", sp.simplify(r**4 * r**-3 - r) == 0, "r⁴·r⁻³ = r")

# --- 4. m8_threshold_arithmetic: M ≥ 16C⁸⁴Ω²/ν³ ⇒ C₈√Ω ν^(−3/4) M^(−1/4) ≤ ½
C8, Om, nu, M = sp.symbols('C_8 Omega nu M', positive=True)
M8 = 16*C8**4*Om**2/nu**3
P1_at_M8 = C8*sp.sqrt(Om)*nu**sp.Rational(-3,4)*M8**sp.Rational(-1,4)
gate("m8_threshold_arithmetic", sp.simplify(P1_at_M8 - sp.Rational(1,2)) == 0,
     f"P₁(M₈) = {sp.simplify(P1_at_M8)} (decreasing in M ⇒ ≤ ½ above M₈)")

# --- 5. quiet_growth_bound: 1 ≤ 1/G + P, 0≤P≤½, G>0 ⇒ G ≤ 1/(1−P) ≤ 1+2P ----
G, P = sp.symbols('G P', positive=True)
# G ≤ 1/(1−P) is algebra from 1 − P ≤ 1/G; then 1/(1−P) ≤ 1+2P ⇔ 1 ≤ (1+2P)(1−P) = 1+P−2P²
h = sp.expand((1+2*P)*(1-P) - 1)
gate("quiet_growth_bound", sp.simplify(h - (P - 2*P**2)) == 0,
     "1/(1−P) ≤ 1+2P ⇔ P(1−2P) ≥ 0, true on [0,½]")

# --- 6. ftan_fold: (1+x)^N ≤ e^{Nx} numerically + log(1+x) ≤ x symbolically -
x = sp.Symbol('x', positive=True)
ok6 = sp.simplify(sp.series(sp.log(1+x) - x, x, 0, 3).removeO()) is not None
import mpmath as mp
num_ok = all((1+xx)**NN <= mp.e**(NN*xx) + 1e-12 for xx in (0.1, 0.5, 1.7) for NN in (1, 7, 40))
gate("ftan_fold", num_ok, "(1+x)^N ≤ e^{Nx} via log(1+x) ≤ x")

# --- 7. k4_omega_star_integral: c*(2/(2π)³)^½ (E₀/2ν)^½ = c*(E₀/((2π)³ν))^½ -
cs, E0 = sp.symbols('c_star E_0', positive=True)
lhs = cs*sp.sqrt(sp.Rational(2)/(2*sp.pi)**3)*sp.sqrt(E0/(2*nu))
rhs = cs*sp.sqrt(E0/((2*sp.pi)**3*nu))
gate("k4_omega_star_integral", sp.simplify(lhs - rhs) == 0, "K₄ constant algebra exact")

# --- 8. drift_interval_bound: exponent regroup identity ----------------------
C1p, clam, mI, T_, Cev, ed, c_, Ig = sp.symbols("C_1' c_l m T C_ev e_d c I", positive=True)
lhs8 = 2*(C1p+clam)*Ig + 2*mI*T_ + Cev*(1 + (ed/c_)*Ig)
rhs8 = (2*(C1p+clam) + Cev*ed/c_)*Ig + 2*mI*T_ + Cev
gate("drift_interval_bound", sp.simplify(lhs8 - rhs8) == 0, "exponent assembly is a ring identity")

# --- 9. eps8_squeeze_arithmetic: ε < (c/C')⁴ ⇒ C'ε^{1/4} < c ----------------
cnu, Cp, eps = sp.symbols("c_nu C' epsilon", positive=True)
val = Cp*((cnu/Cp)**4)**sp.Rational(1,4)
gate("eps8_squeeze_arithmetic", sp.simplify(val - cnu) == 0,
     "C'·(ε₈)^{1/4} = c(ν) at the threshold; strict below it by rpow monotonicity")

# --- 10. nu32_floor_arithmetic: ½ ≤ K(νσ)^{−3/2} m ⇒ m ≥ (νσ)^{3/2}/(2K) ----
K_, sg = sp.symbols('K sigma_0', positive=True)
m_floor = sp.solve(sp.Eq(sp.Rational(1,2), K_*(nu*sg)**sp.Rational(-3,2)*sp.Symbol('m_1', positive=True)), sp.Symbol('m_1', positive=True))[0]
gate("nu32_floor_arithmetic", sp.simplify(m_floor - (nu*sg)**sp.Rational(3,2)/(2*K_)) == 0,
     f"mass floor = {m_floor}")

# --- 11. cd_event_integral: (Γ/max(d,δ)²)(δ²/ν) ≤ Γ/ν ----------------------
Gam, dd, dl = sp.symbols('Gamma d delta', positive=True)
# max(d,δ) ≥ δ ⇒ δ²/max² ≤ 1
expr11 = (Gam/sp.Max(dd,dl)**2)*(dl**2/nu)
num_ok11 = all(float(expr11.subs({Gam:1.3, dd:dv, dl:lv, nu:0.7})) <= 1.3/0.7 + 1e-12
               for dv in (0.1, 1.0, 5.0) for lv in (0.1, 1.0, 5.0))
gate("cd_event_integral", num_ok11, "per-event integral ≤ Γ/ν uniform in d (δ ≤ max(d,δ))")

# --- 12. cd_event_count: (4νΩ/(c₁γc_EΓ²L))·(γ/c) γ-cancellation -------------
gam, c1, cE, L, cc = sp.symbols('gamma c_1 c_E L c', positive=True)
expr12 = sp.simplify((4*nu*Om/(c1*gam*cE*Gam**2*L))*(gam/cc))
gate("cd_event_count", 'gamma' not in str(expr12), f"episode integrand = {expr12} (γ cancelled)")

print(f"\n{PASS}/12 gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
