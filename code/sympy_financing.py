import sympy as sp
print("sympy pre-Lean verification -- the financing identity's pointwise algebra (signs exact)")
s11,s12,s13,s22,s23,w1,w2,w3 = sp.symbols('s11 s12 s13 s22 s23 w1 w2 w3')
s33 = -s11 - s22                                   # trace-free
S = sp.Matrix([[s11,s12,s13],[s12,s22,s23],[s13,s23,s33]])
W = sp.Rational(1,2)*sp.Matrix([[0,-w3,w2],[w3,0,-w1],[-w2,w1,0]])   # Wv = (1/2) omega x v
A = S + W
om = sp.Matrix([w1,w2,w3])
L1 = sp.simplify(sp.trace(A**3) - (sp.trace(S**3) + 3*sp.trace(S*W*W)))
L2 = sp.simplify(sp.trace(S*W*W) - sp.Rational(1,4)*(om.T*S*om)[0])
L2b = sp.simplify(sp.trace(S*W*W) + sp.Rational(1,4)*(om.T*S*om)[0])
L3 = sp.simplify(sp.trace(S**3) - 3*S.det())
print(f"  L1: tr(A^3) - [tr(S^3) + 3 tr(S W^2)]      = {L1}")
print(f"  L2: tr(S W^2) - (1/4) om.S.om              = {L2}")
print(f"  L2b: tr(S W^2) + (1/4) om.S.om             = {L2b}")
print(f"  L3: tr(S^3) - 3 det(S)   (trace-free S)    = {L3}")
print("  chain: 0 = int tr(A^3) = int tr S^3 + 3 int tr(SW^2)")
print("  with the CORRECT L2 sign above  =>  int om.S.om = -(4/3) int tr S^3 = -4 int det S")
print("  (the recorded sec-119 statement: int om.S.om = -4 int l1 l2 l3 -- sign adjudicated)")
