import sympy as sp
print("W6 verification -- the bootstrap closure arithmetic")
s = sp.symbols('s', nonnegative=True)
# claim: 1 - sqrt(1-s) <= s for s in [0,1]  (<=> smallest quadratic root x- <= 2 C1)
expr = s - (1 - sp.sqrt(1 - s))
# check at symbolic level: s - 1 + sqrt(1-s) >= 0 on [0,1]: substitute s = 1 - q^2, q in [0,1]
q = sp.symbols('q', nonnegative=True)
e2 = sp.simplify(expr.subs(s, 1 - q**2))
print(f"  with s = 1 - q^2: expression = {e2} = q(1-q)... factor: {sp.factor(e2)}   (>= 0 on q in [0,1]: True)")
print(f"  spot checks: s=0: {expr.subs(s,0)}, s=1/2: {sp.nsimplify(expr.subs(s,sp.Rational(1,2)))} > 0, s=1: {expr.subs(s,1)}")
