import sympy as sp
print("W2/W3 verification")
r, s = sp.symbols('r s', positive=True)
# W2: int_{|y|<=r} |y|^2 |y|^{-3} dy = 4 pi int_0^r s^{-1} s^2 ds = 2 pi r^2
i1 = sp.integrate(4*sp.pi*(s**2)*(s**-3)*s**2, (s, 0, r))
print(f"  W2 integral: {i1}   (claim 2 pi r^2: match = {sp.simplify(i1 - 2*sp.pi*r**2) == 0})")
# W3: Gronwall integrating-factor check on the scalar model x' = (k-d) x + F, x(0)=x0
t, tt, k, d, F, x0 = sp.symbols('t s k d F x0', positive=True)
x = sp.exp((k-d)*t)*x0 + sp.integrate(sp.exp((k-d)*(t-tt))*F, (tt, 0, t))
chk = sp.simplify(sp.diff(x, t) - ((k-d)*x + F))
print(f"  W3 Gronwall solution check: residual = {chk}")
