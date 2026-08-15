import sympy as sp
print("sympy layer -- ruler mathematics: the calibration factor's closed form + the moment law")
u, r, t, nu, al = sp.symbols('u r t nu alpha', positive=True)
# 1) THE CALIBRATION FACTOR: omega^2-weighted truncated moment for Gaussian omega = e^{-r^2/d2},
#    mask omega >= peak/2  <=>  u := r^2/d2 <= ln 2.  Factor = <u> with weight e^{-2u}.
num = sp.integrate(u*sp.exp(-2*u), (u, 0, sp.log(2)))
den = sp.integrate(sp.exp(-2*u), (u, 0, sp.log(2)))
fac = sp.simplify(num/den)
closed = sp.Rational(1,2) - sp.log(2)/3
print(f"  calibration factor = {fac} = {sp.nsimplify(fac)}")
print(f"  closed form 1/2 - ln2/3: difference = {sp.simplify(fac - closed)}   value = {float(fac):.6f}")
# 2) THE MOMENT LAW on the Gaussian family (closed under the strained flow):
#    omega(r,t) = A(t) exp(-r^2/d2(t)); strained advection-diffusion (axial strain alpha):
#    w_t - (alpha/2) r w_r = nu (w_rr + w_r/r) + alpha w
A = sp.Function('A', positive=True)(t); d2 = sp.Function('d2', positive=True)(t)
w = A*sp.exp(-r**2/d2)
lhs = sp.diff(w, t) - (al/2)*r*sp.diff(w, r) - nu*(sp.diff(w, r, 2) + sp.diff(w, r)/r) - al*w
lhs = sp.simplify(lhs/w)                      # polynomial in r^2 / d2 with A', d2' coefficients
poly = sp.Poly(sp.expand(lhs), r)
eqs = [sp.Eq(c, 0) for c in poly.coeffs()]
sol = sp.solve(eqs, [sp.diff(A, t), sp.diff(d2, t)], dict=True)[0]
print(f"  Gaussian family under the strained flow:  d(d2)/dt = {sp.simplify(sol[sp.diff(d2, t)])}")
print(f"  (the moment law predicts d(d2)/dt = 4 nu - alpha d2;  m2 = d2 for the Gaussian)")
print(f"  match: {sp.simplify(sol[sp.diff(d2, t)] - (4*nu - al*d2)) == 0}")
