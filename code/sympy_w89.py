import sympy as sp
print("W8/W9 verification")
r, s = sp.symbols('r s', positive=True)
i1 = sp.integrate(4*sp.pi*s**-10*s**2, (s, r, sp.oo))
print(f"  W8 kernel tail: {i1}   (claim (4 pi/7) r^-7: match = {sp.simplify(i1 - sp.Rational(4,7)*sp.pi*r**-7) == 0})")
k = sp.symbols('k', integer=True, nonnegative=True)
ser = sp.summation(2**(-2*k), (k, 0, sp.oo))
print(f"  W9 shell series sum 2^(-2k) = {ser}   (claim 4/3: match = {ser == sp.Rational(4,3)})")
