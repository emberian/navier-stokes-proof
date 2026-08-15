import sympy as sp
print("W1 integral verification (corrected script -- first inline check had the volume element twice)")
r, s = sp.symbols('r s', positive=True)
# int_{|z|>=r} |z|^-8 dz = 4 pi int_r^inf s^-8 s^2 ds
i1 = sp.integrate(4*sp.pi*s**-8*s**2, (s, r, sp.oo))
# int_{r<=|z|<=2r} |z|^-6 dz = 4 pi int_r^2r s^-6 s^2 ds
i2 = sp.integrate(4*sp.pi*s**-6*s**2, (s, r, 2*r))
print(f"  main tail:    {i1}   (write-up claims (4 pi/5) r^-5: match = {sp.simplify(i1 - sp.Rational(4,5)*sp.pi*r**-5) == 0})")
print(f"  annulus:      {sp.simplify(i2)}   (write-up claims (7 pi/6) r^-3: match = {sp.simplify(i2 - sp.Rational(7,6)*sp.pi*r**-3) == 0})")
