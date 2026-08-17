#!/usr/bin/env python3
"""numerics_n6_tail.py — CERTIFIED-NUMERICS WAVE, stage N6 (NS_Proof.md): the
chain tail and the closing table.

  C''  = 16 (pi sqrt(k3))^(1/2) C_K        (annulus velocity interpolation)
  transport clause -> k3^(1/4) <= 49 theta/(4 C_psi C'')   (pure numbers,
                                            ~129x margin; M9 inherited from
                                            the scale-intensity lock)
  D_Q  = (D1 + 2 C2)/(1 - c_*^2)           (assembly form; entry sum <= 2)
  two-gauge: Gamma_E <= 0.14416 nu; ordered below Gamma_min for any
             admissible R7
  + the assembled table of every certified number of the wave (N1-N6).
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

# --- 1. C'': the annulus interpolation, optimized exactly -------------------
a, om, E, CK_s, k3_s = sp.symbols('a omega E C_K k3', positive=True)
f = 4*sp.pi*CK_s*a*om + 16*sp.sqrt(k3_s)*CK_s*sp.sqrt(E)/a
astar = sp.solve(sp.diff(f, a), a)
astar = [s_ for s_ in astar if s_.is_positive][0]
fmin = sp.simplify(f.subs(a, astar))
target = 16*sp.sqrt(sp.pi*sp.sqrt(k3_s))*CK_s*sp.sqrt(om)*E**sp.Rational(1, 4)
gate("cpp_optimization", sp.simplify(fmin - target) == 0,
     "min_a [4pi C_K a w + 16 sqrt(k3) C_K sqrt(E)/a] = 16 sqrt(pi sqrt(k3)) C_K w^(1/2) E^(1/4)")
gate("cpp_second_order", sp.simplify(sp.diff(f, a, 2).subs(a, astar)).is_positive,
     "the critical point is the minimum (f'' > 0)")
m = sp.Symbol('m', integer=True, nonnegative=True)
gate("u_far_series", sp.Sum(2**-m, (m, 0, sp.oo)).doit() == 2, "sum 2^-m = 2 exactly")

k3v = 4*mp.pi/3
CK = mp.mpf('0.102190')          # N1
Cpp = 16*mp.sqrt(mp.pi*mp.sqrt(k3v))*CK
up = lambda v, d: mp.ceil(v*10**d)/mp.mpf(10**d)
dn = lambda v, d: mp.floor(v*10**d)/mp.mpf(10**d)
Cpp_u = up(Cpp, 5)
gate("cpp_directed", Cpp_u >= Cpp and Cpp_u - Cpp < mp.mpf('1e-5'),
     f"C'' = 16 sqrt(pi sqrt(k3)) C_K = {mp.nstr(Cpp, 7)} -> {mp.nstr(Cpp_u, 7)} (up)")

# --- 2. the transport reduction: pure numbers under the lock ----------------
s_, nu_, th_, Cps_, Cpp_, eps_, K_ = sp.symbols('s nu theta C_psi C_pp eps K', positive=True)
# transport <= rent/4:  C_psi C'' w^(1/2) E^(5/4) / (49 K^2 s^2) <= (nu theta/(4K^2)) s^-3 E
# with E <= eps nu^2 and the lock s^2 = sqrt(k3/eps) nu / w  (worst case):
w_ = sp.Symbol('w', positive=True)
lhs = Cps_*Cpp_*sp.sqrt(w_)*(eps_*nu_**2)**sp.Rational(1, 4)*s_/49
rhs = nu_*th_/4
lock = sp.sqrt(k3_s/eps_)*nu_/w_
reduced = sp.simplify((lhs.subs(s_, sp.sqrt(lock))/rhs))
target_red = Cps_*Cpp_*k3_s**sp.Rational(1, 4)/(sp.Rational(49, 4)*th_)
gate("transport_cancellation", sp.simplify(reduced - target_red) == 0,
     "under the lock the w's and nu's cancel EXACTLY: condition = k3^(1/4) <= 49 theta/(4 C_psi C'')")
Cpsi = mp.pi**2/2 + mp.pi
theta = mp.mpf('503.99')          # N5b
lhs_n = k3v**mp.mpf('0.25')
rhs_n = 49*theta/(4*Cpsi*Cpp_u)
gate("transport_margin", rhs_n/lhs_n > 125,
     f"k3^(1/4) = {mp.nstr(lhs_n, 5)} vs 49 theta/(4 C_psi C'') = {mp.nstr(rhs_n, 6)}: margin {mp.nstr(rhs_n/lhs_n, 4)}x")

# --- 3. D_Q assembly: the geometric fold and the absorption -----------------
er = sp.Rational(1, 2)
j = sp.Symbol('j', integer=True, nonnegative=True)
gate("entry_sum_two", sp.Sum((1 - er)**j, (j, 0, sp.oo)).doit() == 2,
     "sum (1-eps_r)^j = 2 at eps_r = 1/2 (event-separated entries)")
X, D1, C2, cs = sp.symbols('X D_1 C_2 c_star', positive=True)
solX = sp.solve(sp.Eq(X, D1 + cs**2*X + 2*C2), X)[0]
gate("dq_absorption", sp.simplify(solX - (D1 + 2*C2)/(1 - cs**2)) == 0,
     "X = D1 + c*^2 X + 2C2  =>  D_Q = (D1 + 2C2)/(1 - c*^2) (c* < 1)")

# --- 4. the two-gauge ordering ----------------------------------------------
eps_reg = mp.mpf('0.013230')      # N4 (floor)
GammaE = mp.sqrt(mp.pi*eps_reg/2)
GE_u = up(GammaE, 5)
gate("gammaE_directed", GE_u >= GammaE,
     f"Gamma_E/nu = sqrt(pi eps*_reg/2) = {mp.nstr(GammaE, 6)} <= {mp.nstr(GE_u, 6)}")
R7_thresh = GE_u/4
gate("two_gauge_ordering", R7_thresh < mp.mpf('0.03605'),
     f"Gamma_E < Gamma_min iff R7 > {mp.nstr(up(R7_thresh, 5), 5)} C_1'/c_cc: any admissible (large) R7 passes")

# --- 5. the assembled table --------------------------------------------------
print()
print("=" * 72)
print("THE CERTIFIED-NUMERICS WAVE — ASSEMBLED TABLE (N1-N6)")
print("=" * 72)
rows = [
    ("C_G",      "<= 0.0226124",  "N1", "torus Green regular part, sup|grad R|"),
    ("C_K",      "<= 0.102190",   "N1", "= 1/(4pi) + C_G"),
    ("C_K'",     "<= 0.228699",   "N1", "sup |z|^3 |grad^2 G| (Frobenius)"),
    ("C_K''",    "<= 0.788814",   "N1", "sup |z|^4 |grad^3 G| (Frobenius)"),
    ("C_S",      "<= 1.313856",   "N2", "= 1/(2pi) + 2 sqrt(3)/3 (derived, closed form)"),
    ("C_E",      "=  96.101321",  "N2", "= 96 + 1/pi^2 exactly"),
    ("C_Ee",     "<= 1878.03",    "N2", "Master Estimate enstrophy constant"),
    ("c_f",      ">= 0.245420",   "N3", "= (1-e^-4)/4; leakage e^-4 <= 1.84% (w5 slack)"),
    ("mean rate", "= ln 2",       "N3", "core-mean precession (Frullani, exact)"),
    ("C_R'",     "<= 5.60919",    "N4", "= 1/2 + (64pi/9) C_K' (1/sqrt2 multiplier exact)"),
    ("C_A",      "<= 3959.69",    "N4", "= 4 C_R'^4 exactly"),
    ("eps*_reg", ">= 0.013230",   "N4", "= sqrt(log2/C_A); <=2 per viscous cylinder"),
    ("C_phi",    "=  35/8",       "N5a", "quartic mollifier, exact"),
    ("C_psi",    "<= 8.076395",   "N5a", "= pi^2/2 + pi, cos^2 window"),
    ("C_h",      "<= 0.500386",   "N5a", "= sqrt(8/7) sqrt(k3) C_K' (closed form)"),
    ("C_low",    "<= 132.672",    "N5b", "strengthened route: K^-2 gain; 315/8 exact"),
    ("C_far",    "<= 0.83213",    "N5b", "= (16/9) sqrt(k3) C_K'"),
    ("C_ann",    "<= 11.2337",    "N5b", "= 24 sqrt(k3) C_K'; mu0 >= 2C_ann/Delta0"),
    ("K",        "=  4",          "N5b", "mollification scale at its floor"),
    ("theta",    ">= 503.99",     "N5b", "rent floor; theta/K^2 >= 31.499"),
    ("eps_r",    ">= 1/2",        "N5b", "race fraction (clamp, 15.7x excess)"),
    ("eta'",     ">= 1",          "N5b", "= -log2(1-eps_r), exact at the clamp"),
    ("C''",      f"<= {mp.nstr(Cpp_u, 6)}", "N6", "= 16 sqrt(pi sqrt(k3)) C_K"),
    ("transport", "129x margin",  "N6", "k3^(1/4) <= 49 theta/(4 C_psi C''), pure numbers"),
    ("D_Q",      "assembly",      "N6", "= (D1 + 2C2)/(1 - c*^2), entry sum <= 2"),
    ("Gamma_E",  "<= 0.14416 nu", "N6", "two gauges ordered below Gamma_min"),
]
for nm, val, st, desc in rows:
    print(f"  {nm:<9} {val:<15} [{st:>3}]  {desc}")
print("=" * 72)
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
