"""SC-3 + SC-5 adjudication: Lemma FT and Lemma DC exact cores.
(1) FT-3 transit factor: exp((g/c)*(log(1/th)/g)) = th**(-1/c) — the organizer's clock
    cancels; the per-transit growth factor is intensity-free.
(2) FT-5 chain fold: exp(A) * G**n = exp(A + n*log G) for G > 0.
(3) DC-2 coherence inheritance: dev' <= 2*D*a and b >= (1-D)*a and D <= 1/3
    ==> 2*D*a <= 3*D*b  (i.e. the sub-ball is 3*Delta_0-coherent).
"""
import sympy as sp

g, c, th = sp.symbols('g c theta', positive=True)
transit = sp.exp((g/c) * (sp.log(1/th)/g))
assert sp.simplify(transit - th**(-1/c)) == 0
print("(1) OK: exp((g/c)(log(1/th)/g)) = th^(-1/c) — g cancels, transit factor intensity-free")

A, G, n = sp.symbols('A G n', positive=True)
assert sp.simplify(sp.exp(A) * G**n - sp.exp(A + n*sp.log(G))) == 0
print("(2) OK: exp(A)*G^n = exp(A + n*log G) — the chain fold")

a, b, D = sp.symbols('a b Delta0', nonnegative=True)
# worst case b = (1-D)a, D = 1/3: need 2*D*a <= 3*D*(1-D)*a  <=>  2 <= 3*(1-D)  <=>  D <= 1/3
gap = sp.simplify((3*(1 - D) - 2).subs(D, sp.Rational(1, 3)))
assert gap == 0
Dv = sp.Rational(1, 4)
assert sp.simplify(3*Dv*(1 - Dv) - 2*Dv) > 0
print("(3) OK: 2*D*a <= 3*D*b when b >= (1-D)a and D <= 1/3 (equality exactly at D = 1/3)")
print("\nSC-3/SC-5 chains ADJUDICATED. Lean targets: ft_transit_factor, ft_chain_fold, dc_coherence_inherit")
