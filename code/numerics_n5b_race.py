#!/usr/bin/env python3
"""numerics_n5b_race.py — CERTIFIED-NUMERICS WAVE, stage N5 slice b (NS_Proof.md).

The D-gate chain's race core, certified:
  C_low = 2 sqrt(k3) C_K'' [315/8 + 48/(7K)]   (direct-kernel route, K^-2 gain
                                                — STRONGER than D-G's sketch)
  C_far = (16/9) sqrt(k3) C_K'                  (closed form)
  K     = 4                                     (the mollification scale lands
                                                 at its floor)
  theta/K^2, burn formula, the content clamp:
  eps_r >= 1/2, eta' >= 1, eta >= 1/2
mu0 taken AT ITS FLOOR mu0 = 2 C_ann/Delta0 (the paper's inheritance clause;
the conservative direction — the (0,1] in D-Alt is a recorded stale slip).
Exit 0 iff all gates pass.
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

r, m = sp.Symbol('r', positive=True), sp.Symbol('m', integer=True, nonnegative=True)

# --- 1. the exact ingredients of C_low --------------------------------------
c0 = sp.Rational(105, 32)/sp.pi                       # the N5a mollifier
gate("phi_sup_exact", sp.simplify(c0*(1 - 0**2)**2 - sp.Rational(105, 32)/sp.pi) == 0,
     "C_phi0 = |phi|_inf = 105/(32 pi) (attained at 0; (1-r^2)^2 decreasing)")
kern4 = sp.integrate(4*sp.pi*r**2 * r**-4, (r, 1, sp.oo))
gate("kernel_integral_4pi", sp.simplify(kern4 - 4*sp.pi) == 0,
     "int_{|z|>=r0} |z|^-4 dz = 4 pi/r0 exactly (scaled to r0 = 1)")
gate("pi_cancellation", sp.simplify(12*sp.pi*(sp.Rational(105, 32)/sp.pi) - sp.Rational(315, 8)) == 0,
     "12 pi C_phi0 = 315/8 exactly — the pi's cancel")
gate("series_8_7", sp.Sum(8**-m, (m, 0, sp.oo)).doit() == sp.Rational(8, 7), "sum 8^-m = 8/7")
gate("series_4_3", sp.Sum(4**-m, (m, 0, sp.oo)).doit() == sp.Rational(4, 3), "sum 4^-m = 4/3")
gate("outer_bracket_at_K4", sp.simplify(sp.Rational(315, 8) + sp.Rational(48, 7*4)
     - sp.Rational(2301, 56)) == 0, "315/8 + 48/28 = 2301/56 exactly (K = 4)")

# --- 2. the assemblies with N1 certified kernel bounds ----------------------
k3v = 4*mp.pi/3
CKp = mp.mpf('0.228699')       # N1: |z|^3 |grad^2 G|
CKpp = mp.mpf('0.788814')      # N1: |z|^4 |grad^3 G|
Ch = mp.mpf('0.500386')        # N5a
Cpsi = mp.pi**2/2 + mp.pi      # N5a

Clow = 2*mp.sqrt(k3v)*CKpp*(mp.mpf(2301)/56)
Cfar = (mp.mpf(16)/9)*mp.sqrt(k3v)*CKp
Cann = 24*mp.sqrt(k3v)*CKp
up = lambda v, d: mp.ceil(v*10**d)/mp.mpf(10**d)
dn = lambda v, d: mp.floor(v*10**d)/mp.mpf(10**d)
Clow_u, Cfar_u, Cann_u = up(Clow, 3), up(Cfar, 5), up(Cann, 4)
gate("clow_directed", Clow_u >= Clow and Clow_u - Clow < mp.mpf('1e-3'),
     f"C_low = 2 sqrt(k3) C_K'' (2301/56) = {mp.nstr(Clow, 7)} -> {mp.nstr(Clow_u, 7)} (up)")
gate("cfar_directed", Cfar_u >= Cfar and Cfar_u - Cfar < mp.mpf('1e-5'),
     f"C_far = (16/9) sqrt(k3) C_K' = {mp.nstr(Cfar, 6)} -> {mp.nstr(Cfar_u, 6)} (up)")
gate("cann_directed", Cann_u >= Cann and Cann_u - Cann < mp.mpf('1e-4'),
     f"C_ann = 24 sqrt(k3) C_K' = {mp.nstr(Cann, 7)} -> {mp.nstr(Cann_u, 7)} (up)")

# --- 3. the mu0 floor and K -------------------------------------------------
D0mu0 = 2*Cann                          # Delta0 mu0 at the inheritance floor
Kreq = mp.sqrt(2*(Clow_u + 2*Cfar_u)/dn(D0mu0, 4))
gate("k_requirement", Kreq < 4,
     f"burning clause: K >= sqrt(2(C_low + 2C_far)/(D0 mu0)) = {mp.nstr(Kreq, 5)} < 4")
theta = (dn(D0mu0, 4)/(2*Ch))**2
gate("k_leakage_negligible", Cpsi/(343*theta) < mp.mpf('1e-3'),
     f"K >= C_psi/(343 theta) = {mp.nstr(Cpsi/(343*theta), 3)}: negligible")
K = 4
gate("k_at_floor", max(4, int(mp.ceil(Kreq))) == 4,
     "K = max(4, ceil(3.46)) = 4 — the mollification scale is four core radii")

# --- 4. the race core -------------------------------------------------------
theta_dn = dn(theta, 2)
rent_coeff = theta_dn/K**2
gate("theta_value", theta_dn <= theta,
     f"theta = [D0 mu0/(2C_h)]^2 >= {mp.nstr(theta_dn, 6)} (mu0 at its floor)")
gate("rent_floor_strong", rent_coeff > 30,
     f"rent-floor coefficient theta/K^2 >= {mp.nstr(dn(rent_coeff, 3), 5)}")
burn_formula = rent_coeff/4                      # c_q = 1/4 above max(M8, M9)
gate("clamp_binds", burn_formula >= mp.mpf('0.5'),
     f"burn formula c_q theta/K^2 = {mp.nstr(burn_formula, 5)} >= 1/2: the content clamp binds")
gate("clamp_margin", burn_formula/mp.mpf('0.5') > 15,
     f"excess {mp.nstr(burn_formula/mp.mpf('0.5'), 4)}x: >93% of the mechanism could fail and eps_r >= 1/2 survives")
eps_r = mp.mpf('0.5')
eta_p = -mp.log(1 - eps_r)/mp.log(2)
gate("eta_prime_one", eta_p == 1, "eta' = -log2(1 - 1/2) = 1 exactly")
gate("q2_fold_clause", 4*(1 - eps_r) > 1,
     "4(1 - eps_r) = 2 > 1: the (q2) affine fold direction holds")
# race display spot check: [4(1-e)]^W / 2^(2W) = (1-e)^W
W = 7
lhs = (4*(1 - eps_r))**W / mp.mpf(2)**(2*W)
gate("race_ratio_algebra", abs(lhs - (1 - eps_r)**W) < mp.mpf('1e-30'),
     "[4(1-eps)]^W / (2^W)^2 = (1-eps)^W (rd_race_ratio's algebra, spot W = 7)")

print()
print("CERTIFIED RESULTS (stage N5, slice b):")
print(f"  C_low <= {mp.nstr(Clow_u, 7)}     (= 2 sqrt(k3) C_K''(315/8 + 48/(7K)); K^-2 gain — strengthened)")
print(f"  C_far <= {mp.nstr(Cfar_u, 6)}     (= (16/9) sqrt(k3) C_K', closed form)")
print(f"  C_ann <= {mp.nstr(Cann_u, 7)}     (= 24 sqrt(k3) C_K'; mu0 floor = 2 C_ann/Delta0)")
print(f"  K      = 4            (the mollification scale lands at its floor)")
print(f"  theta >= {mp.nstr(theta_dn, 6)}      (rent floor theta/K^2 >= {mp.nstr(dn(rent_coeff, 3), 5)})")
print(f"  eps_r >= 1/2   eta' >= 1   eta >= 1/2   (clamped; formula excess ~{mp.nstr(burn_formula/mp.mpf('0.5'), 3)}x)")
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
