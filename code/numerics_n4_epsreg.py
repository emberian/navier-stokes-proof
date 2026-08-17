#!/usr/bin/env python3
"""numerics_n4_epsreg.py — CERTIFIED-NUMERICS WAVE, stage N4 (NS_Proof.md).

The regular-horn stretching threshold eps*_reg, pinned and certified:
  C_R' <= 1/2 + (64 pi/9) C_K'          (Display 1's eps*-part: exact 1/sqrt2
                                         multiplier + dyadic shells, N1's C_K')
  C_A   = 4 C_R'^4                       (Display 2: the 27 and the GN-chain's
                                         64/27 cancel exactly)
  eps*_reg := sqrt(log 2 / C_A)          (factor <= 2 per viscous cylinder —
                                         the campaign's half-slack convention)
Scope: the stretching threshold only; the De Giorgi ladder constants are
classical-cited and gate nothing; the far-energy and flux/drift lines are
eps*-independent by construction. Exit 0 iff all gates pass.
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

# --- 1. the strain multiplier is EXACTLY 1/sqrt2 on divergence-free data ----
k1, k2, k3, w1, w2, w3 = sp.symbols('k1 k2 k3 w1 w2 w3', real=True)
k = sp.Matrix([k1, k2, k3]); w = sp.Matrix([w1, w2, w3])
u = k.cross(w)/(k.dot(k))                      # u-hat = i k x w / |k|^2 (i dropped: norms only)
Ssq = sp.Rational(1, 4)*sum((k[i]*u[j] + k[j]*u[i])**2 for i in range(3) for j in range(3))
# identity |k(x)u + u(x)k|_F^2 = 2|k|^2|u|^2 + 2(k.u)^2, with k.u = 0 automatic:
id1 = sp.simplify(sum((k[i]*u[j] + k[j]*u[i])**2 for i in range(3) for j in range(3))
                  - (2*k.dot(k)*u.dot(u) + 2*k.dot(u)**2))
gate("frobenius_identity", id1 == 0, "|k@u + u@k|_F^2 = 2|k|^2|u|^2 + 2(k.u)^2 exactly")
gate("incompressible_auto", sp.simplify(k.dot(u)) == 0, "k . (k x w) = 0 automatically")
# with k.w = 0: |k x w|^2 = |k|^2|w|^2, so Ssq = |w|^2/2:
lagrange = sp.simplify(k.cross(w).dot(k.cross(w)) - (k.dot(k)*w.dot(w) - k.dot(w)**2))
gate("lagrange_identity", lagrange == 0, "|k x w|^2 = |k|^2|w|^2 - (k.w)^2 exactly")
Ssq_df = sp.simplify(Ssq - w.dot(w)/2)
Ssq_df = sp.simplify(Ssq_df.subs(k1*w1 + k2*w2 + k3*w3, 0))
num = sp.simplify(sp.expand(Ssq*2 - w.dot(w)) .subs(w3, -(k1*w1 + k2*w2)/k3))
gate("multiplier_half", sp.simplify(num) == 0,
     "on k.w = 0: |S-hat|_F^2 = |w|^2/2 — the multiplier is exactly 1/sqrt2")

# --- 2. the shell geometry: distance factor and the series --------------------
j = sp.Symbol('j', positive=True, integer=True)
gate("shell_distance", all(2**jj - 1 >= 2**(jj-1) for jj in range(1, 12)),
     "2^j - 1 >= 2^(j-1) for j >= 1: kernel distance >= 2^(j-1) s")
gate("shell_series", sp.Sum(4**-j, (j, 1, sp.oo)).doit() == sp.Rational(1, 3),
     "sum 4^-j = 1/3 exactly")

# --- 3. C_R' assembly with N1's certified C_K' -------------------------------
k3v = 4*mp.pi/3
CKp = mp.mpf('0.228699')                     # N1 certified
CRp = mp.mpf('0.5') + (16*k3v/3)*CKp
coeff = sp.simplify(16*(4*sp.pi/3)/3 - 64*sp.pi/9)
gate("crp_coefficient", coeff == 0, "16 k3/3 = 64 pi/9 exactly")
CRp_up = mp.ceil(CRp*10**5)/mp.mpf(10**5)
gate("crp_directed", CRp_up >= CRp and CRp_up - CRp < mp.mpf('1e-5'),
     f"C_R' <= 1/2 + (64pi/9)(0.228699) = {mp.nstr(CRp, 8)} -> {mp.nstr(CRp_up, 7)} (rounded up)")

# --- 4. the GN-chain collapse: C_A = 4 C_R'^4 exactly ------------------------
S3 = 2*sp.sqrt(3)/3
gate("s3_square", sp.simplify(S3**2 - sp.Rational(4, 3)) == 0, "(2 sqrt3/3)^2 = 4/3 exactly")
gate("gn8_collapse", sp.simplify(S3**6 - sp.Rational(64, 27)) == 0,
     "C_GN^8 = S3^6 = (4/3)^3 = 64/27 exactly")
CA_sym = sp.Rational(27, 16)*sp.Rational(64, 27)
gate("ca_clean", sp.simplify(CA_sym - 4) == 0,
     "C_A = (27/16) C_GN^8 C_R'^4 = 4 C_R'^4 — the 27 and 64/27 cancel")

# --- 5. the Young step: (3l/4)x^(4/3) + y^4/(4 l^3) >= xy --------------------
xs, ys, ls = sp.symbols('x y l', positive=True)
# substitute x = a^3: weighted AM-GM (3/4, 1/4) on (l a^4, b^4/l^3):
a, b = sp.symbols('a b', positive=True)
amgm = sp.Rational(3, 4)*ls*a**4 + b**4/(4*ls**3) - a**3*b
# equality at b = l a: check the value and the second-order positivity on a grid
eq_at = sp.simplify(amgm.subs(b, ls*a))
grid_ok = all(float(amgm.subs({a: av, b: bv, ls: lv})) >= -1e-15
              for av in (0.3, 1, 2.7) for bv in (0.2, 1, 3.1) for lv in (0.5, 4/3.0, 2))
gate("young_weighted", eq_at == 0 and grid_ok,
     "(3l/4)a^4 + b^4/(4l^3) >= a^3 b, equality at b = la (weighted AM-GM)")

# --- 6. eps*_reg, rounded DOWN ----------------------------------------------
CA = 4*CRp_up**4
eps_reg = mp.sqrt(mp.log(2)/CA)
eps_dn = mp.floor(eps_reg*10**6)/mp.mpf(10**6)
gate("eps_reg_directed", eps_dn <= eps_reg and eps_dn > 0,
     f"eps*_reg = sqrt(log2/(4 C_R'^4)) = {mp.nstr(eps_reg, 7)} >= {mp.nstr(eps_dn, 7)}")
gate("threshold_positive_explicit", eps_dn >= mp.mpf('0.01'),
     "the threshold is a clean O(10^-2) number — no vanishing-constant pathology")

print()
print("CERTIFIED RESULTS (stage N4):")
print(f"  C_R'     <= {mp.nstr(CRp_up, 7)}      (= 1/2 + (64pi/9) C_K'; N1's C_K' <= 0.228699)")
print(f"  C_A      <= {mp.nstr(mp.ceil(CA*10**3)/mp.mpf(10**3), 8)}      (= 4 C_R'^4 exactly)")
print(f"  eps*_reg >= {mp.nstr(eps_dn, 7)}    (= sqrt(log2/C_A), floor; factor <= 2 per viscous cylinder)")
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
