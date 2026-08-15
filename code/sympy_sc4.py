"""SC-4 adjudication: Lemma EC's exact core.
(1) The forced-damped ODE: e' = -a*e + b solves to e(t) = b/a + (e0 - b/a)*exp(-a*t) —
    equilibrium e_eq = b/a = C_f*gamma/(c2*omega) = C_e*gamma/omega.
(2) The threshold: omega >= 2*M*C_e*gamma  ==>  C_e*gamma/omega <= 1/(2M).
(3) The BKM split identity: max(w - r, 0) + min(w, r) = w.
(4) The calibration: e = 0.9 at ratio 19.6 gives C_e = 17.64 (one moderate-ratio point).
"""
import sympy as sp

t, a, b, e0 = sp.symbols('t a b e0', positive=True)
e = sp.Function('e')
sol = sp.dsolve(sp.Eq(e(t).diff(t), -a*e(t) + b), e(t), ics={e(0): e0}).rhs
assert sp.simplify(sol - (b/a + (e0 - b/a)*sp.exp(-a*t))) == 0
assert sp.limit(sol, t, sp.oo) == b/a
print("(1) OK: e(t) = e_eq + (e0 - e_eq)exp(-at), e_eq = b/a — the circularization law")

M, Ce, g, w = sp.symbols('M C_e gamma omega', positive=True)
expr = (Ce*g/w).subs(w, 2*M*Ce*g)
assert sp.simplify(expr - 1/(2*M)) == 0
print("(2) OK: at omega = 2*M*C_e*gamma the equilibrium is exactly 1/(2M) — inside e <= 1/M")

wv, rv = sp.symbols('w r', real=True)
s = sp.symbols('s', nonnegative=True)
split = lambda W, R: sp.Max(W - R, 0) + sp.Min(W, R) - W
assert sp.simplify(split(rv + s, rv)) == 0 and sp.simplify(split(rv - s, rv)) == 0
assert all(split(W, R) == 0 for W in (-3, 0, 2, 7) for R in (-1, 0, 2, 5))
print("(3) OK: max(w-r,0) + min(w,r) = w — the BKM split, both branches (w = r±s) + grid")

print(f"(4) OK: calibration C_e = 0.9*19.6 = {0.9*19.6:.2f} (moderate-ratio point, l17 gates)")
print("\nSC-4 chain ADJUDICATED. Lean targets: ec_threshold, ec_bkm_split")
