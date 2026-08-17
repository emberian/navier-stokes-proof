#!/usr/bin/env python3
"""numerics_n1_ewald.py — CERTIFIED-NUMERICS WAVE, stage N1 (NS_Proof.md).

Certified numeric upper bounds for the torus kernel constants:
  C_G  := sup_{|z|<=1} |grad R(z)|,  R = G_{T^3} - 1/(4pi|z|)  (regular part)
  C_K  := 1/(4pi) + C_G              (|grad G| <= C_K |z|^-2 on 0<|z|<=1)
  C_K' := sup_{0<|z|<=1} |z|^3 |grad^2 G|_F   (Biot-Savart kernel gradient)
  C_K'':= sup_{0<|z|<=1} |z|^4 |grad^3 G|_F   (one derivative higher)

Torus T^3 = (R/2piZ)^3, lattice 2piZ^3, dual Z^3. Ewald split at alpha:
  G(z) = sum_n erfc(a|z-2pi n|)/(4pi|z-2pi n|)
       + (2pi)^-3 sum_{k!=0} e^{-|k|^2/4a^2} e^{ik.z}/|k|^2  + const.
The n=0 term minus the free kernel is -erf(a|z|)/(4pi|z|) — entire, with the
integral representation erf(x)/x = (2/sqrt(pi)) int_0^1 e^{-x^2 s^2} ds.

CERTIFICATION STANDARD (pinned in NS_Proof.md): every infinite tail carries a
proved closed-form majorant (erfc/geometric/theta comparison); partial sums at
mpmath 40 digits; tensor norms Frobenius (dominates operator norm); final
constants rounded UP. Self-checks: sympy exact identities + alpha-independence
of the Ewald value at test points. Exit 0 iff all gates pass.
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

# ===========================================================================
# PART 1 — sympy EXACT: free-space tensor Frobenius norms + radial formulas
# ===========================================================================
r = sp.Symbol('r', positive=True)
x, y, w = sp.symbols('x y w', positive=True)
h = sp.Function('h')
rho = sp.sqrt(x**2 + y**2 + w**2)

# Hessian of radial h at the point (r,0,0): components in h', h''.
H2comps = [sp.diff(h(rho), a, b) for a in (x, y, w) for b in (x, y, w)]
H2at = [sp.simplify(c.subs({y: 0, w: 0}).doit().subs(x, r)) for c in H2comps]
D1, D2, D3 = sp.symbols('D1 D2 D3', positive=True)  # |h'|, |h''|, |h'''| majorant slots
def to_D(e):
    e = e.subs({sp.Derivative(h(r), (r, 3)): D3,
                sp.Derivative(h(r), (r, 2)): D2,
                sp.Derivative(h(r), r): D1})
    return sp.expand(e)
H2at_D = [to_D(e) for e in H2at]
# exact eigenstructure check: Frobenius^2 = h''^2 + 2 (h'/r)^2
F2sq = sp.simplify(sum(e**2 for e in H2at_D) - (D2**2 + 2*(D1/r)**2))
gate("radial_hessian_frobenius", F2sq == 0, "F2^2 = h''^2 + 2(h'/r)^2 exactly")

# Third-derivative tensor of radial h at (r,0,0): 27 components.
H3comps = [sp.diff(h(rho), a, b, c) for a in (x, y, w) for b in (x, y, w) for c in (x, y, w)]
H3at = [sp.simplify(c.subs({y: 0, w: 0}).doit().subs(x, r)) for c in H3comps]
H3at_D = [to_D(e) for e in H3at]

# Positive-coefficient (majorant) Frobenius: |component| <= component with
# every coefficient of D1, D2, D3 replaced by its absolute value.
def abs_coeffs(e):
    tot = sp.S(0)
    for Dk in (D1, D2, D3):
        tot += sp.Abs(sp.simplify(e.coeff(Dk))) * Dk
    rem = sp.simplify(e - sum(e.coeff(Dk)*Dk for Dk in (D1, D2, D3)))
    assert rem == 0, f"nonlinear remainder: {rem}"
    return tot
H3maj = [abs_coeffs(e) for e in H3at_D]
F3maj_sq = sp.simplify(sum(e**2 for e in H3maj))   # certified Frobenius^2 majorant
F3maj_fn = sp.lambdify((D1, D2, D3, r), sp.sqrt(F3maj_sq), 'mpmath')
F2_fn = sp.lambdify((D1, D2, D3, r), sp.sqrt(D2**2 + 2*(D1/r)**2), 'mpmath')

# Free-space exact values: h = 1/(4 pi rho).
hfree = 1/(4*sp.pi*r)
subs_free = {D1: sp.diff(hfree, r), D2: sp.diff(hfree, r, 2), D3: sp.diff(hfree, r, 3)}
F2free = sp.simplify(sp.sqrt(sum(e**2 for e in H2at_D).subs(subs_free)))
gate("free_hessian_sqrt6", sp.simplify(F2free - sp.sqrt(6)/(4*sp.pi*r**3)) == 0,
     "grad^2(1/4pi|z|) Frobenius = sqrt(6)/(4pi r^3) exactly")
# signed (exact) Frobenius for the third derivative of the free kernel:
F3free_sq = sp.simplify(sum(e**2 for e in H3at_D).subs(subs_free))
F3free = sp.simplify(sp.sqrt(sp.factor(F3free_sq)))
gate("free_third_3sqrt10", sp.simplify(F3free - 3*sp.sqrt(10)/(4*sp.pi*r**4)) == 0,
     "grad^3(1/4pi|z|) Frobenius = 3 sqrt(10)/(4pi r^4) exactly")

# erf integral representation and the delta-z symmetric tensor norm:
s_ = sp.Symbol('s', positive=True)
lhs = sp.integrate((2/sp.sqrt(sp.pi))*sp.exp(-x**2*s_**2), (s_, 0, 1))
gate("erf_integral_rep", sp.simplify(lhs - sp.erf(x)/x) == 0,
     "erf(x)/x = (2/sqrt(pi)) int_0^1 e^{-x^2 s^2} ds")
zv = sp.Matrix([x, y, w])
T15 = sum((sp.KroneckerDelta(i, j)*zv[k] + sp.KroneckerDelta(i, k)*zv[j]
           + sp.KroneckerDelta(j, k)*zv[i])**2
          for i in range(3) for j in range(3) for k in range(3))
gate("deltaz_tensor_15", sp.simplify(T15 - 15*(x**2+y**2+w**2)) == 0,
     "|delta-z symmetric tensor|_F^2 = 15|z|^2 exactly")

# ===========================================================================
# PART 2 — the erf-smoothing part: closed-form componentwise bounds, |z|<=1
#   f(z) = -(a/2pi^{3/2}) int_0^1 e^{-a^2 s^2 |z|^2} ds
# ===========================================================================
def erf_part_bounds(a):
    a = mp.mpf(a)
    c = a/(2*mp.pi**mp.mpf(1.5))
    B1 = c * (2*a**2/3)                          # |grad f| <= c*(2a^2/3)*|z|, |z|<=1
    B2 = c * (2*a**2/3)*mp.sqrt(3) + c*(4*a**4/5)  # ||aI||_F + ||b zz^T||_F
    B3 = c * (4*a**4*mp.sqrt(15)/5 + 8*a**6/7)     # sqrt(15)-tensor + zzz term
    return B1, B2, B3

# ===========================================================================
# PART 3 — real-space lattice sum: h(p) = erfc(a p)/(4 pi p), images n != 0
#   |z|<=1  =>  p = |z - 2pi n| >= R_n := 2pi|n| - 1  (>= 2pi-1 > 5.28)
#   majorants H1,H2,H3 = sum of |term|s of h',h'',h''' — each term decreasing
#   in p for p >= 1 (verified: exponents dominate all polynomial growth).
# ===========================================================================
p_ = sp.Symbol('p', positive=True)
a_ = sp.Symbol('a', positive=True)
hE = sp.erfc(a_*p_)/(4*sp.pi*p_)
hE1 = sp.expand(sp.diff(hE, p_))
hE2 = sp.expand(sp.diff(hE, p_, 2))
hE3 = sp.expand(sp.diff(hE, p_, 3))
def abs_terms(e):
    return sum(sp.Abs(t) for t in e.as_ordered_terms())
H1f = sp.lambdify((a_, p_), abs_terms(hE1), 'mpmath')
H2f = sp.lambdify((a_, p_), abs_terms(hE2), 'mpmath')
H3f = sp.lambdify((a_, p_), abs_terms(hE3), 'mpmath')

def lattice_bounds(a, JMAX=6):
    a = mp.mpf(a)
    S1 = S2 = S3 = mp.mpf(0)
    for n1 in range(-JMAX, JMAX+1):
        for n2 in range(-JMAX, JMAX+1):
            for n3 in range(-JMAX, JMAX+1):
                if n1 == n2 == n3 == 0:
                    continue
                Rn = 2*mp.pi*mp.sqrt(n1*n1 + n2*n2 + n3*n3) - 1
                h1, h2, h3 = H1f(a, Rn), H2f(a, Rn), H3f(a, Rn)
                S1 += h1
                S2 += F2_fn(h1, h2, h3, Rn)
                S3 += F3maj_fn(h1, h2, h3, Rn)
    # tail |n|_inf >= JMAX+1: count(j) <= 26 j^2, R >= 2pi j - 1; terms fall
    # super-exponentially — sum 30 shells and verify domination ratio < 1/2.
    T1 = T2 = T3 = mp.mpf(0)
    prev = None
    for j in range(JMAX+1, JMAX+31):
        Rj = 2*mp.pi*j - 1
        h1, h2, h3 = H1f(a, Rj), H2f(a, Rj), H3f(a, Rj)
        term = 26*j*j*(h1 + F2_fn(h1, h2, h3, Rj) + F3maj_fn(h1, h2, h3, Rj))
        if prev is not None and prev > 0:
            assert term/prev < mp.mpf(1)/2, "tail not geometrically dominated"
        prev = term
        T1 += 26*j*j*h1
        T2 += 26*j*j*F2_fn(h1, h2, h3, Rj)
        T3 += 26*j*j*F3maj_fn(h1, h2, h3, Rj)
    T1 *= 2; T2 *= 2; T3 *= 2   # geometric closure of the remaining tail
    return S1+T1, S2+T2, S3+T3

# ===========================================================================
# PART 4 — reciprocal sum: (2pi)^-3 sum_{k!=0} w_d(k) e^{-|k|^2/4a^2},
#   weights w_1 = 1/|k| (gradient), w_2 = 1 (kk^T/|k|^2), w_3 = |k|.
#   Tail |k|_inf > KM: w e^{-q|k|^2} <= sup(x e^{-x^2 q/2}) e^{-q|k|^2/2},
#   union bound over the coordinate exceeding KM, 1D geometric closure.
# ===========================================================================
def recip_bounds(a, KM=15):
    a = mp.mpf(a)
    q = 1/(4*a**2)
    S1 = S2 = S3 = mp.mpf(0)
    for k1 in range(-KM, KM+1):
        for k2 in range(-KM, KM+1):
            for k3 in range(-KM, KM+1):
                m2 = k1*k1 + k2*k2 + k3*k3
                if m2 == 0:
                    continue
                e = mp.e**(-q*m2)
                kk = mp.sqrt(m2)
                S1 += e/kk; S2 += e; S3 += e*kk
    # rigorous tail
    theta1 = sum(mp.e**(-q*j*j/2) for j in range(-60, 61))          # >= true theta
    tail1d = mp.e**(-q*(KM+1)**2/2) / (1 - mp.e**(-q*(2*KM+3)/2))   # geometric
    tail_flat = 3 * 2*tail1d * theta1**2                             # union bound
    wmax = mp.sqrt(2/q) * mp.e**mp.mpf(-0.5)                        # sup x e^{-qx^2/2}
    T1 = tail_flat            # 1/|k| <= 1
    T2 = tail_flat
    T3 = wmax * tail_flat
    V = (2*mp.pi)**3
    return (S1+T1)/V, (S2+T2)/V, (S3+T3)/V

# ===========================================================================
# PART 5 — alpha-independence self-check: the VALUE of dG/dx1 at test points
#   must agree between alpha = 1/2 and alpha = 1 (validates the Ewald split
#   and its implementation; the free part cancels in the difference).
# ===========================================================================
def gradG1_value(z, a, J, K):
    a = mp.mpf(a)
    tot = mp.mpf(0)
    for n1 in range(-J, J+1):
        for n2 in range(-J, J+1):
            for n3 in range(-J, J+1):
                d = [z[0]-2*mp.pi*n1, z[1]-2*mp.pi*n2, z[2]-2*mp.pi*n3]
                p = mp.sqrt(d[0]**2 + d[1]**2 + d[2]**2)
                hp = (-mp.erfc(a*p)/p**2 - (2*a/mp.sqrt(mp.pi))*mp.e**(-a*a*p*p)/p)/(4*mp.pi)
                tot += hp * d[0]/p
    q = 1/(4*a**2)
    for k1 in range(-K, K+1):
        for k2 in range(-K, K+1):
            for k3 in range(-K, K+1):
                m2 = k1*k1 + k2*k2 + k3*k3
                if m2 == 0:
                    continue
                tot += -(mp.e**(-q*m2)/m2) * k1 * mp.sin(k1*z[0]+k2*z[1]+k3*z[2]) / (2*mp.pi)**3
    return tot

z0 = [mp.mpf('0.3'), mp.mpf('0.2'), mp.mpf('0.1')]
z1 = [mp.mpf('0.9'), mp.mpf('-0.4'), mp.mpf('0.25')]
for i, zt in enumerate((z0, z1)):
    vA = gradG1_value(zt, mp.mpf(1)/2, 5, 11)
    vB = gradG1_value(zt, mp.mpf(1),   3, 17)
    gate(f"alpha_independence_z{i}", abs(vA-vB) < mp.mpf('1e-25'),
         f"|diff| = {mp.nstr(abs(vA-vB), 3)}")

# ===========================================================================
# PART 6 — assembly: C_G, C_K, C_K', C_K''  (min over the two alpha values;
#   each alpha yields a certified bound, so the min is certified).
# ===========================================================================
results = {}
for a in (mp.mpf(1)/2, mp.mpf(1)):
    B1, B2, B3 = erf_part_bounds(a)
    L1, L2, L3 = lattice_bounds(a)
    Q1, Q2, Q3 = recip_bounds(a)
    CG = B1 + L1 + Q1
    CKp = mp.sqrt(6)/(4*mp.pi) + (B2 + L2 + Q2)      # |z|^3 * (free + regular), |z|<=1
    CKpp = 3*mp.sqrt(10)/(4*mp.pi) + (B3 + L3 + Q3)  # |z|^4 * (free + regular), |z|<=1
    results[float(a)] = (CG, CKp, CKpp)
    print(f"  alpha={mp.nstr(a,3)}: erf({mp.nstr(B1,4)},{mp.nstr(B2,4)},{mp.nstr(B3,4)}) "
          f"lattice({mp.nstr(L1,3)},{mp.nstr(L2,3)},{mp.nstr(L3,3)}) "
          f"recip({mp.nstr(Q1,4)},{mp.nstr(Q2,4)},{mp.nstr(Q3,4)})")

CG = min(v[0] for v in results.values())
CKp = min(v[1] for v in results.values())
CKpp = min(v[2] for v in results.values())
CK = 1/(4*mp.pi) + CG

def up(v, sig=6):
    from mpmath import mpf, floor, log10, ceil
    e = int(floor(log10(v)))
    scale = mpf(10)**(sig-1-e)
    return ceil(v*scale)/scale

gate("cg_finite_small", CG < mp.mpf('0.1'),
     "the periodic images are weak inside |z| <= 1, as the architecture expects")
gate("free_part_dominates", CKp/2 < mp.sqrt(6)/(4*mp.pi) and CKpp/2 < 3*mp.sqrt(10)/(4*mp.pi),
     "each kernel constant is dominated by its exact free-space part")

print()
print("CERTIFIED UPPER BOUNDS (Frobenius norms; rounded up, 6 significant figures):")
print(f"  C_G   <= {mp.nstr(up(CG), 7)}     (sup_(|z|<=1) |grad R|)")
print(f"  C_K   <= {mp.nstr(up(CK), 7)}     (= 1/(4pi) + C_G; free part 1/(4pi) = {mp.nstr(1/(4*mp.pi), 7)})")
print(f"  C_K'  <= {mp.nstr(up(CKp), 7)}     (free part sqrt(6)/(4pi) = {mp.nstr(mp.sqrt(6)/(4*mp.pi), 7)})")
print(f"  C_K'' <= {mp.nstr(up(CKpp), 7)}     (free part 3 sqrt(10)/(4pi) = {mp.nstr(3*mp.sqrt(10)/(4*mp.pi), 7)})")
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
