import sympy as sp
print("sympy layer -- QT-1 scaling algebra and moment-law by-parts, on exact decaying families")
r, y, d = sp.symbols('r y d', positive=True)
# 1) QT-1's by-parts fact in 3D: int y.grad f = -3 int f  (radial: int_0^inf r f'(r) 4pi r^2 dr
#    = -3 int f 4pi r^2 dr).  Verify exactly on the two-parameter family f = r^n e^{-r^2/d}:
ok = []
for n in (0, 2, 4):
    f = r**n*sp.exp(-r**2/d)
    lhs = sp.integrate(r*sp.diff(f, r)*r**2, (r, 0, sp.oo))
    rhs = -3*sp.integrate(f*r**2, (r, 0, sp.oo))
    ok.append(sp.simplify(lhs - rhs) == 0)
print(f"  QT-1 by-parts (int y.grad f = -3 int f), family r^n e^(-r^2/d), n=0,2,4: {ok}")
# 2) QT-1's coefficient chain: (1/2)e + (1/4)(y.grad|v|^2 integral) with the by-parts value
#    -3e gives -(1/4)e -- the scaling coefficient (tails dropped on full space):
e = sp.symbols('e')
print(f"  QT-1 coefficient: 1/2*e + 1/4*(-3*e) = {sp.simplify(sp.Rational(1,2)*e + sp.Rational(1,4)*(-3*e))}  (= -e/4, the -1/4 of QT-1)")
# 3) moment-law by-parts on the family omega = e^{-r^2/d} (2D transverse, measure 2 pi r dr):
w = sp.exp(-r**2/d)
a1 = sp.integrate(r**4*sp.diff(w, r), (r, 0, sp.oo))
a2 = -4*sp.integrate(r**3*w, (r, 0, sp.oo))
b1 = sp.integrate(r**3*(sp.diff(w, r, 2) + sp.diff(w, r)/r), (r, 0, sp.oo))
b2 = 4*sp.integrate(r*w, (r, 0, sp.oo))
print(f"  moment by-parts (a): int r^4 w' = -4 int r^3 w : {sp.simplify(a1 - a2) == 0}")
print(f"  moment by-parts (b): int r^3 (w'' + w'/r) = 4 int r w : {sp.simplify(b1 - b2) == 0}")
# 4) the assembly coefficients (advection -2a m2, stretching +a m2, viscous +4nu):
a_, m2_, nu_ = sp.symbols('a m2 nu')
print(f"  assembly: (-2*a + a)*m2 + 4*nu = {sp.simplify((-2*a_ + a_)*m2_ + 4*nu_)}  (= 4nu - a m2, the law)")
