import sympy as sp
print("W4 verification -- the Gram entries, exact")
r, d = sp.symbols('r delta2', positive=True)
W = 2*sp.exp(-r**2)
g_trans = sp.integrate(r**2*sp.diff(W, r), (r, 0, sp.oo))
print(f"  <r, W'> (measure r dr) = {g_trans}   (claim: exactly -2 -> match = {sp.simplify(g_trans + 2) == 0})")
U = sp.exp(-r**2/d)/(sp.pi*d)          # normalized Gaussian core, circulation 1
g_delta = sp.integrate(r**2*sp.diff(U, d)*2*sp.pi*r, (r, 0, sp.oo))
print(f"  g_delta = <r^2 moment, dU/d(delta2)> = {sp.simplify(g_delta)}   (nonzero, sign definite: claim 1)")
circ = sp.integrate(U*2*sp.pi*r, (r, 0, sp.oo))
print(f"  circulation normalization: {sp.simplify(circ)}   (claim 1)")
