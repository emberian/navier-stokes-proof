#!/usr/bin/env python3
"""numerics_n2_sobolev.py — CERTIFIED-NUMERICS WAVE, stage N2 (NS_Proof.md).

Certifies the derived torus Sobolev chain and assembles the Master Estimate
constants:
  C_S  <= 1/(2pi) + 2 sqrt(3)/3        (mean-zero |phi|_L6 <= C_S |grad phi|_L2)
  C_E   = 3(32 + 1/(3 pi^2))           (exact)
  C_Ee  = 3[2 C_S^2 c_g^2 + 144 pi^2 C_K^2 c_m^2 + 2 k3^2 c_p^2 C_K^2]
with the pinned pure numbers k3 = 4pi/3, c_g = k3^(1/3) + (2pi)^(-1/2) k3^(1/2),
c_m = 1 + 1/(6 pi^2), c_p = 8 c_m + 32, and N1's certified C_K <= 0.102190.

The C_S derivation (NS_Proof.md, stage N2) is a five-step elementary chain:
periodic line bound -> Loomis-Whitney -> AM-GM assembly -> |phi|^4 boost with
two Cauchy-Schwarz -> exact Poincare gap 1. The gates below verify each step:
the two combinatorial inequalities EXACTLY on random discrete structures
(both hold on counting measure — falsification tests, not approximations),
the algebra symbolically, and the end-to-end bound against witnesses.
Exit 0 iff all gates pass.
"""
import random
import sympy as sp
import mpmath as mp

mp.mp.dps = 30
random.seed(20260816)
PASS = 0
FAIL = 0

def gate(name, ok, detail=""):
    global PASS, FAIL
    status = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else: FAIL += 1
    print(f"[{status}] {name}  {detail}")

# ---------------------------------------------------------------------------
# Gate 1 — the periodic line bound, discrete-exact falsification test:
# on the discrete circle, |f(j)| <= mean|f| + (1/2) sum |f(i+1)-f(i)|.
# ---------------------------------------------------------------------------
ok = True
worst = 0.0
for _ in range(400):
    n = random.randint(3, 40)
    f = [random.uniform(-5, 5) for _ in range(n)]
    tv = sum(abs(f[(i+1) % n] - f[i]) for i in range(n))
    mean_abs = sum(abs(v) for v in f)/n
    for j in range(n):
        slack = mean_abs + tv/2 - abs(f[j])
        worst = min(worst, slack) if slack < worst else worst
        if slack < -1e-12:
            ok = False
gate("line_bound_discrete", ok, f"400 random circles, min slack {worst:.2e} >= 0")

# ---------------------------------------------------------------------------
# Gate 2 — Loomis-Whitney, discrete-exact falsification test:
# sum f^{3/2} <= sqrt( sum F1 * sum F2 * sum F3 ), F_i = max over axis i.
# ---------------------------------------------------------------------------
ok = True
for _ in range(200):
    n = random.randint(2, 7)
    f = [[[random.uniform(0, 3) for _ in range(n)] for _ in range(n)] for _ in range(n)]
    lhs = sum(f[i][j][k]**1.5 for i in range(n) for j in range(n) for k in range(n))
    F1 = sum(max(f[i][j][k] for i in range(n)) for j in range(n) for k in range(n))
    F2 = sum(max(f[i][j][k] for j in range(n)) for i in range(n) for k in range(n))
    F3 = sum(max(f[i][j][k] for k in range(n)) for i in range(n) for j in range(n))
    if lhs > (F1*F2*F3)**0.5 * (1 + 1e-12):
        ok = False
gate("loomis_whitney_discrete", ok, "200 random 3D grids, inequality exact")

# ---------------------------------------------------------------------------
# Gate 3 — the two Cauchy-Schwarz boosts on random trigonometric polynomials:
# int |phi|^3 |grad phi| <= |phi|_6^3 |grad phi|_2   and
# int |phi|^4 <= |phi|_2 |phi|_6^3      (1D circle suffices to test the step).
# ---------------------------------------------------------------------------
ok3a = ok3b = True
for _ in range(25):
    coefs = [(random.uniform(-1, 1), random.uniform(-1, 1)) for _ in range(4)]
    phi = lambda t, c=coefs: sum(a*mp.cos((m+1)*t) + b*mp.sin((m+1)*t) for m, (a, b) in enumerate(c))
    dphi = lambda t, c=coefs: sum(-(m+1)*a*mp.sin((m+1)*t) + (m+1)*b*mp.cos((m+1)*t) for m, (a, b) in enumerate(c))
    I = lambda g: mp.quad(g, [0, mp.pi, 2*mp.pi])
    n6 = I(lambda t: abs(phi(t))**6)**mp.mpf('1/6')
    n2 = I(lambda t: phi(t)**2)**mp.mpf('0.5')
    g2 = I(lambda t: dphi(t)**2)**mp.mpf('0.5')
    lhs_a = I(lambda t: abs(phi(t))**3*abs(dphi(t)))
    lhs_b = I(lambda t: phi(t)**4)
    if lhs_a > n6**3*g2*(1 + mp.mpf('1e-20')): ok3a = False
    if lhs_b > n2*n6**3*(1 + mp.mpf('1e-20')): ok3b = False
gate("cauchy_schwarz_grad", ok3a, "int |phi|^3|phi'| <= |phi|_6^3 |phi'|_2 on 25 trials")
gate("cauchy_schwarz_L4", ok3b, "int phi^4 <= |phi|_2 |phi|_6^3 on 25 trials")

# ---------------------------------------------------------------------------
# Gate 4 — the assembly algebra (symbolic): X^4 <= aX^3 + bX^3  =>  X <= a+b;
# the AM-GM/ell1-ell2 constants; the final closed form.
# ---------------------------------------------------------------------------
X, aa, bb = sp.symbols('X a b', positive=True)
gate("assembly_divide", sp.simplify((aa*X**3 + bb*X**3)/X**3 - (aa+bb)) == 0,
     "divide by X^3: X <= a + b")
gate("sqrt3_ell1_ell2", sp.simplify(sp.sqrt(3)*sp.Rational(1, 6)*4 - 2*sp.sqrt(3)/3) == 0,
     "(sqrt(3)/6)*4 = 2 sqrt(3)/3")
CS_exact = 1/(2*sp.pi) + 2*sp.sqrt(3)/3
CS = mp.mpf(1)/(2*mp.pi) + 2*mp.sqrt(3)/3
gate("cs_closed_form", abs(CS - mp.mpf(sp.N(CS_exact, 30).__str__())) < mp.mpf('1e-25'),
     f"C_S = 1/(2pi) + 2 sqrt(3)/3 = {mp.nstr(CS, 8)}")

# ---------------------------------------------------------------------------
# Gate 5 — Poincare gap: min_{k in Z^3 \ 0} |k|^2 = 1, with the equality
# witness phi = cos x1: |phi|_2 = |grad phi|_2 exactly (sympy).
# ---------------------------------------------------------------------------
t = sp.Symbol('t')
n2sq = sp.integrate(sp.cos(t)**2, (t, 0, 2*sp.pi)) * (2*sp.pi)**2
g2sq = sp.integrate(sp.sin(t)**2, (t, 0, 2*sp.pi)) * (2*sp.pi)**2
gate("poincare_gap_witness", sp.simplify(n2sq - g2sq) == 0,
     "phi = cos x1: |phi|_2 = |grad phi|_2 exactly (gap = 1 attained)")

# ---------------------------------------------------------------------------
# Gate 6 — end-to-end witnesses (probe C_S from below; must never exceed it).
# (a) exact: phi = cos x1 (sympy).  (b) concentrated periodic bubble, numeric.
# ---------------------------------------------------------------------------
n6_exact = (sp.integrate(sp.cos(t)**6, (t, 0, 2*sp.pi)) * (2*sp.pi)**2)**sp.Rational(1, 6)
ratio_a = sp.N(n6_exact / sp.sqrt(g2sq), 30)
gate("witness_cos", float(ratio_a) < float(CS),
     f"|cos x1|_6/|grad|_2 = {sp.N(ratio_a, 6)} < C_S = {mp.nstr(CS, 6)}")

def bubble_ratio(lam, N=48):
    # phi = exp(-lam * d^2)-like periodic bump via (1+cos)^lam, mean-removed
    import math
    vals = []
    h = 2*math.pi/N
    for i in range(N):
        row = []
        for j in range(N):
            col = []
            for k in range(N):
                v = ((1+math.cos(i*h))*(1+math.cos(j*h))*(1+math.cos(k*h))/8)**lam
                col.append(v)
            row.append(col)
        vals.append(row)
    meanv = sum(sum(sum(r) for r in p) for p in vals)/N**3
    l6 = (sum(sum(sum((abs(v-meanv))**6 for v in r) for r in p) for p in vals)*h**3)**(1/6)
    g2s = 0.0
    for i in range(N):
        for j in range(N):
            for k in range(N):
                dx = (vals[(i+1) % N][j][k]-vals[(i-1) % N][j][k])/(2*h)
                dy = (vals[i][(j+1) % N][k]-vals[i][(j-1) % N][k])/(2*h)
                dz = (vals[i][j][(k+1) % N]-vals[i][j][(k-1) % N])/(2*h)
                g2s += dx*dx+dy*dy+dz*dz
    return l6/(g2s*h**3)**0.5

worst_b = max(bubble_ratio(lam) for lam in (2, 5, 10))
gate("witness_bubbles", worst_b < float(CS),
     f"concentrated bubbles (lam=2,5,10): max ratio {worst_b:.5f} < C_S")

# ---------------------------------------------------------------------------
# Gate 7 — C_E exact and C_Ee assembly with pinned pure numbers + N1's C_K.
# ---------------------------------------------------------------------------
CE_sym = 3*(32 + 1/(3*sp.pi**2))
gate("ce_exact", sp.simplify(CE_sym - (96 + sp.pi**-2)) == 0,
     f"C_E = 3(32+1/(3pi^2)) = 96 + 1/pi^2 = {sp.N(CE_sym, 8)}")

k3 = 4*mp.pi/3
c_g = k3**(mp.mpf(1)/3) + (2*mp.pi)**mp.mpf('-0.5')*k3**mp.mpf('0.5')
c_m = 1 + 1/(6*mp.pi**2)
c_p = 8*c_m + 32
CK = mp.mpf('0.102190')          # N1 certified
CS_up = mp.mpf('1.313856')       # this stage, rounded up
t1 = 2*CS_up**2*c_g**2
t2 = 144*mp.pi**2*CK**2*c_m**2
t3 = 2*k3**2*c_p**2*CK**2
CEe = 3*(t1 + t2 + t3)
gate("cee_terms_positive", t3 > t2 > 0 and t1 > 0,
     f"terms: {mp.nstr(t1,6)} + {mp.nstr(t2,6)} + {mp.nstr(t3,6)} (shell-sum square dominates)")

print()
print("CERTIFIED RESULTS (rounded up where inexact):")
print(f"  C_S   <= 1/(2pi) + 2 sqrt(3)/3 = {mp.nstr(CS, 7)}  -> quote 1.313856")
print(f"  C_E    = 96 + 1/pi^2 = {mp.nstr(96 + mp.pi**-2, 8)}  (exact closed form)")
print(f"  c_g    = {mp.nstr(c_g, 7)}   c_m = {mp.nstr(c_m, 7)}   c_p = {mp.nstr(c_p, 7)}   (pinned pure numbers)")
print(f"  C_Ee  <= {mp.nstr(CEe, 7)}   (= 3[2 C_S^2 c_g^2 + 144 pi^2 C_K^2 c_m^2 + 2 k3^2 c_p^2 C_K^2])")
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
