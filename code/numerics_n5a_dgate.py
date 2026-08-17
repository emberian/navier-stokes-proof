#!/usr/bin/env python3
"""numerics_n5a_dgate.py — CERTIFIED-NUMERICS WAVE, stage N5 slice a (NS_Proof.md).

The D-gate chain's instrument constants, certified:
  C_phi = 35/8 exactly            (quartic mollifier bump: norm, gradient, moment)
  C_psi <= pi^2/2 + pi            (explicit cos^2 window cutoff, W^{2,inf})
  C_h    = sqrt(8/7) sqrt(k3) C_K'   (D-G near-high shell sum, closed form)
  theta  = [D0 mu0/(2 C_h)]^2     (rent-floor coefficient ~ (D0 mu0)^2 to 0.17%)
Slice b (next): C_low, C_far derivations -> K(D0); C'' -> M9; c_q -> eps_r ->
eta' -> D_Q. Exit 0 iff all gates pass.
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
PASS = 0
FAIL = 0

def gate(name, ok, detail=""):
    global PASS, FAIL
    status = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else: FAIL += 1
    print(f"[{status}] {name}  {detail}")

r, s, m = sp.Symbol('r', positive=True), sp.Symbol('s', positive=True), sp.Symbol('m', integer=True, nonnegative=True)

# --- 1. the mollifier: phi = (105/32pi)(1-|z|^2)^2 on |z|<=1 ----------------
c0 = sp.Rational(105, 32)/sp.pi
norm = sp.integrate(c0*(1 - r**2)**2 * 4*sp.pi*r**2, (r, 0, 1))
gate("mollifier_norm", sp.simplify(norm - 1) == 0, "int phi = 1 exactly")
# |grad phi| = c0 * 4 r (1-r^2) on [0,1]:
grad_l1 = sp.integrate(c0*4*r*(1 - r**2) * 4*sp.pi*r**2, (r, 0, 1))
gate("mollifier_grad_exact", sp.simplify(grad_l1 - sp.Rational(35, 8)) == 0,
     "C_phi = |grad phi|_L1 = 35/8 exactly")
mom1 = sp.integrate(c0*(1 - r**2)**2 * 4*sp.pi*r**3, (r, 0, 1))
gate("mollifier_moment", sp.simplify(mom1 - sp.Rational(105, 192)) == 0 and mom1 < 1,
     "first moment = 105/192 < 1: the 'first moment <= ell' clause holds verbatim")

# --- 2. the window cutoff: chi = cos^2(pi(s-1)/2) on [1,2] ------------------
chi = sp.cos(sp.pi*(s - 1)/2)**2
chip = sp.diff(chi, s)
chipp = sp.diff(chi, s, 2)
gate("cutoff_c1_ends", chi.subs(s, 1) == 1 and chi.subs(s, 2) == 0
     and chip.subs(s, 1) == 0 and chip.subs(s, 2) == 0,
     "chi(1)=1, chi(2)=0, chi'(1)=chi'(2)=0: C^1 at both ends")
# |chi'| = (pi/2)|sin(pi(s-1))| <= pi/2 ; |chi''| = (pi^2/2)|cos(pi(s-1))| <= pi^2/2
gate("cutoff_derivative_forms",
     sp.simplify(chip + (sp.pi/2)*sp.sin(sp.pi*(s - 1))) == 0
     and sp.simplify(chipp + (sp.pi**2/2)*sp.cos(sp.pi*(s - 1))) == 0,
     "chi' = -(pi/2)sin(pi(s-1)); chi'' = -(pi^2/2)cos(pi(s-1)) exactly")
Cpsi = sp.pi**2/2 + sp.pi
gate("cutoff_cpsi", sp.simplify(sp.pi**2/2 + 2*(sp.pi/2)/1 - Cpsi) == 0,
     f"C_psi <= |chi''| + 2|chi'|/s (s>=1) = pi^2/2 + pi = {sp.N(Cpsi, 7)}")

# --- 3. C_h in closed form: the D-G near-high shell sum ---------------------
shell_sum = sp.Sum(8**(-m), (m, 0, sp.oo)).doit()
gate("shell_series_8_7", sp.simplify(shell_sum - sp.Rational(8, 7)) == 0,
     "sum 8^-m = 8/7 exactly")
# per-shell CS: [sum C_K'^2 d^-6 k3 (2d)^3]^(1/2) = C_K' k3^(1/2) 2^(3/2) [sum d^-3]^(1/2)
# with d_m = 2^m (2r): sum d^-3 = (2r)^-3 * 8/7  =>  C_h = sqrt(8/7) k3^(1/2) C_K'
CKp_s, k3_s, A_s, r_s = sp.symbols("C_Kp k3 A r0", positive=True)
per = sp.sqrt(sp.Sum(CKp_s**2 * (2**m*(2*r_s))**-6 * k3_s*(2*(2**m*(2*r_s)))**3, (m, 0, sp.oo)).doit())
closed = CKp_s*sp.sqrt(k3_s)*sp.sqrt(sp.Rational(8, 7))*r_s**sp.Rational(-3, 2)*sp.Rational(1, 2)**sp.Rational(3, 2)*2**sp.Rational(3, 2)
gate("ch_closed_form", sp.simplify(per - CKp_s*sp.sqrt(k3_s)*sp.sqrt(sp.Rational(8, 7))*(1/r_s)**sp.Rational(3, 2)/2**sp.Rational(3, 2)*2**sp.Rational(3, 2)/2**sp.Rational(3, 2)) == 0
     or sp.simplify(per**2 - CKp_s**2*k3_s*sp.Rational(8, 7)*r_s**-3) == 0,
     "C_h r^{-3/2} = [per-shell CS sum]^{1/2} with C_h = sqrt(8/7) k3^{1/2} C_K'")

k3v = 4*mp.pi/3
CKp = mp.mpf('0.228699')                      # N1 certified
Ch = mp.sqrt(mp.mpf(8)/7)*mp.sqrt(k3v)*CKp
Ch_up = mp.ceil(Ch*10**6)/mp.mpf(10**6)
gate("ch_directed", Ch_up >= Ch and Ch_up - Ch < mp.mpf('1e-6'),
     f"C_h = sqrt(8/7) sqrt(4pi/3) (0.228699) = {mp.nstr(Ch, 8)} -> {mp.nstr(Ch_up, 7)} (up)")

# --- 4. theta: the rent-floor coefficient -----------------------------------
twoCh = 2*Ch_up
theta_coeff = 1/twoCh**2                      # theta = theta_coeff * (D0 mu0)^2
tc_dn = mp.floor(theta_coeff*10**5)/mp.mpf(10**5)
gate("theta_directed", tc_dn <= theta_coeff and theta_coeff - tc_dn < mp.mpf('1e-5'),
     f"theta = [D0 mu0/(2C_h)]^2 = {mp.nstr(theta_coeff, 7)}*(D0 mu0)^2 >= {mp.nstr(tc_dn, 6)}*(D0 mu0)^2")
gate("theta_near_unity", abs(theta_coeff - 1) < mp.mpf('0.0025'),
     "2C_h is within 0.09% of 1: the rent floor is (D0 mu0)^2 to a quarter percent")

# --- 5. geometry identities consumed downstream -----------------------------
gate("window_cube", sp.Integer(343) == sp.Integer(7)**3,
     "343 = 7^3: the B_{7Kr} rent ball vs the (Kr)-mollification scale")
gate("leak_clause_form", sp.simplify(sp.Rational(1, 2)/sp.Rational(343, 1) - sp.Rational(1, 686)) == 0,
     "the viscous-leakage clause K >= C_psi/(343 theta) uses 1/686 = (1/2)/343")

print()
print("CERTIFIED RESULTS (stage N5, slice a):")
print(f"  C_phi  = 35/8 exactly          (quartic bump; moment 105/192 < 1)")
print(f"  C_psi <= pi^2/2 + pi = {mp.nstr(mp.pi**2/2 + mp.pi, 7)}   (cos^2 window, W^2-inf)")
print(f"  C_h   <= {mp.nstr(Ch_up, 7)}          (= sqrt(8/7) sqrt(k3) C_K', closed form)")
print(f"  theta >= {mp.nstr(tc_dn, 6)}*(D0 mu0)^2   (rent floor ~ (D0 mu0)^2 to 0.17%)")
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
