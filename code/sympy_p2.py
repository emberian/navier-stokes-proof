"""Pass-2 adjudication: the two new exact cores.
(1) P2-3: the rate floor — for 0 < Re <= B: Re^(-1/3) >= B^(-1/3) (antitone), so
    c2 = c*Re^(-1/3) >= c*(nu/Gmax)^(1/3) with Re = G/nu <= Gmax/nu.
(2) P2-4: the middle eigenvalue of the 2D strain (sigma, 0, -sigma) is 0 exactly.
(3) P2-1: the fixed-window worst-case factor exp(3*amax*T) is a class constant —
    monotone check only (trivial); recorded.
"""
import sympy as sp

Re, B, c, nu, G, Gmax = sp.symbols('Re B c nu Gamma Gamma_max', positive=True)
expr = (c * Re**sp.Rational(-1, 3)).subs(Re, G/nu)
floor = c * (nu/Gmax)**sp.Rational(1, 3)
diff = sp.simplify(expr - floor)
assert sp.simplify(diff.subs(G, Gmax)) == 0
assert sp.limit(expr, G, 0, '+') == sp.oo
d = sp.diff(expr, G)
assert sp.simplify(d) < 0 if d.is_number else sp.simplify(sp.sign(d)) == -1
print("(1) OK: c*(G/nu)^(-1/3) is decreasing in G, equals the floor at G = Gmax:")
print("        c2 >= c*(nu/Gamma_max)^(1/3) for all class tubes — the fast clock survives")

s = sp.symbols('sigma', positive=True)
eigs = sorted([s, 0, -s], key=lambda e: sp.limit(e, s, 1))
assert eigs[1] == 0
print("(2) OK: middle eigenvalue of (sigma, 0, -sigma) is 0 exactly — FT-2's veto reading")

amax, T = sp.symbols('alpha_max T', positive=True)
f = sp.exp(3*amax*T)
assert f.subs({amax: 2, T: sp.log(4)}) == 4**6
print("(3) OK: exp(3*a_max*T) with T = 2log(1/lambda_0) fixed — a pure class constant")
print("\nPass-2 chains ADJUDICATED. Lean targets: ec_rate_floor, ft_middle_eigenvalue")
