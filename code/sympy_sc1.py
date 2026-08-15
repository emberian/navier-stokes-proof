"""SC-1 adjudication: Lemma BG's exact core.
(1) The factorization: e + C*g <= (e + C*(A+B))*(1 + g/(A+B)) for positives — the log
    split whose absorption coefficient B/(A+B) < 1 is automatic.
(2) The absorption closed form: g <= A + B*(L + g/(A+B)) ==> A*g <= (A+B)*(A + B*L).
(3) The tangent bound log(1+t) <= t (via log x <= x-1).
(4) The integrability bound: sqrt(w)*log(e + c*w**Rational(5,6)) <= C1*w**Rational(5,6) + C2
    (numeric sweep, explicit C1, C2) — the K3-term's pointwise input.
"""
import sympy as sp

g, A, B, C = sp.symbols('g A B C', positive=True)
E = sp.E

# (1) factorization
diff = sp.expand((E + C*(A+B))*(1 + g/(A+B)) - (E + C*g))
assert sp.simplify(diff - (C*(A+B) + E*g/(A+B))) == 0
print("(1) OK: factorization surplus = C*(A+B) + e*g/(A+B) > 0 — inequality holds identically")

# (2) absorption algebra
L = sp.symbols('L', positive=True)
lhs = sp.solve(sp.Eq(g, A + B*L + B*g/(A+B)), g)[0]
assert sp.simplify(A*lhs - (A+B)*(A + B*L)) == 0
print("(2) OK: equality case of g = A + B*L + B*g/(A+B) gives A*g = (A+B)*(A+B*L) exactly")

# (3) tangent bound
t = sp.symbols('t', positive=True)
x = sp.symbols('x', positive=True)
assert sp.limit(sp.log(x) - (x - 1), x, 1) == 0
d = sp.diff(sp.log(x) - (x - 1), x)
assert sp.simplify(d.subs(x, 1)) == 0 and sp.simplify(sp.diff(d, x)) == -1/x**2
print("(3) OK: log x <= x-1 (touch at x=1, concave) => log(1+t) <= t")

# (4) numeric sweep for the K3-term bound with C1 = 2, C2 = 3, c = 1
w = sp.symbols('w', positive=True)
f = sp.sqrt(w)*sp.log(E + w**sp.Rational(5,6)) - 2*w**sp.Rational(5,6) - 3
worst = max(f.subs(w, sp.Rational(k, 10)).evalf() for k in list(range(1, 100)) + [10**j for j in range(1, 13)])
assert worst < 0
print(f"(4) OK: sqrt(w)*log(e + w^(5/6)) <= 2*w^(5/6) + 3 on the sweep (worst margin {worst:.3f})")
print("\nSC-1 chain ADJUDICATED. Lean targets: bg_log_absorption, bg_half_absorption")
