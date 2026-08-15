"""SC-7 adjudication: the small-eps choice chain of Anchor Lemma 3'c.

Chain: defect eps' = C2*eps^(1/2)  ->  QT-3 (theta = 1/2): ||V||_E <= C3*(eps')^(1/2)
       ->  interpolation: I3 := int int |V|^3 <= C4*||V||_E^3
       ->  claim: I3 <= C_QT * eps^(3/4) with C_QT = C4*(C3*sqrt(C2))^3
       ->  choice: eps < (eps_CKN/C_QT)^(4/3)  ==>  C_QT*eps^(3/4) < eps_CKN.
Every step checked symbolically; the final implication checked as an identity at the
boundary and by monotonicity.
"""
import sympy as sp

eps, C2, C3, C4, eCKN = sp.symbols('epsilon C2 C3 C4 epsilon_CKN', positive=True)

# Step 1: exponent composition through QT-3
eps_prime = C2 * eps**sp.Rational(1, 2)
E_bound = C3 * eps_prime**sp.Rational(1, 2)
assert sp.simplify(E_bound - C3 * C2**sp.Rational(1, 2) * eps**sp.Rational(1, 4)) == 0
print("step 1  OK: ||V||_E <= C3*sqrt(C2) * eps^(1/4)   (exponent 1/2 . 1/2 = 1/4)")

# Step 2: cubic interpolation
I3_bound = C4 * E_bound**3
C_QT = C4 * (C3 * C2**sp.Rational(1, 2))**3
assert sp.simplify(I3_bound - C_QT * eps**sp.Rational(3, 4)) == 0
print("step 2  OK: int int |V|^3 <= C_QT * eps^(3/4),  C_QT = C4*(C3*sqrt(C2))^3")

# Step 3: the choice inequality — at the boundary eps = (eCKN/C_QT)^(4/3) the bound equals
# eps_CKN exactly; strict monotonicity in eps gives the strict inequality below it.
CQ = sp.symbols('C_QT', positive=True)
boundary = (eCKN / CQ)**sp.Rational(4, 3)
at_boundary = CQ * boundary**sp.Rational(3, 4)
assert sp.simplify(at_boundary - eCKN) == 0
print("step 3  OK: at eps = (eps_CKN/C_QT)^(4/3), C_QT*eps^(3/4) = eps_CKN exactly;")
print("            eps^(3/4) strictly increasing  =>  eps < boundary  =>  bound < eps_CKN")

# Numerical spot check (rational arithmetic, no floats)
vals = {CQ: sp.Rational(7, 2), eCKN: sp.Rational(1, 100)}
b = boundary.subs(vals)
test_eps = b / 2
assert (CQ * test_eps**sp.Rational(3, 4)).subs(vals) < vals[eCKN]
print("spot    OK: rational instance C_QT=7/2, eps_CKN=1/100, eps=boundary/2 -> strict")

print("\nSC-7 chain ADJUDICATED: eps < (eps_CKN/C_QT)^(4/3)  ==>  C_QT*eps^(3/4) < eps_CKN")
print("Lean target: sc7_small_eps_choice")
