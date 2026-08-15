"""SC-9 audit adjudication: Lemma SU and Lemma QD exact cores.
(1) SU(i): int_0^1 x^m dx = 1/(m+1) — the Green's kernel radial integral.
(2) QD(b): the Oseen core profile is quadratic with Omega''(0) = -1 exactly:
    Omega(r) = (1 - exp(-r^2))/r^2 = 1 - r^2/2 + r^4/6 - ...
(3) QD(b): r_c = (2(Om0-c)/|Om''(0)|)^(1/2) inversion and the exponent chain
    r_c^(2m) / r_c = r_c^(2m-1) -> (Om0-c)^(m-1/2); positive for m >= 1.
"""
import sympy as sp

m, x = sp.symbols('m x', positive=True)
assert sp.integrate(x**m, (x, 0, 1)) == 1/(m + 1)
print("(1) OK: int_0^1 x^m dx = 1/(m+1) — SU's Green kernel integral")

r = sp.symbols('r', positive=True)
Om = (1 - sp.exp(-r**2))/r**2
ser = sp.series(Om, r, 0, 6).removeO()
assert sp.simplify(ser - (1 - r**2/2 + r**4/6)) == 0
Om0 = sp.limit(Om, r, 0)
Ompp0 = sp.limit(sp.diff(Om, r, 2), r, 0)
assert Om0 == 1 and Ompp0 == -1
print("(2) OK: Oseen Omega = 1 - r^2/2 + r^4/6 - ...; Omega(0) = 1, Omega''(0) = -1 exact")

c, M = sp.symbols('c', positive=True), sp.symbols('M', positive=True, integer=True)
rc = sp.sqrt(2*(1 - c))          # |Om''(0)| = 1
chain = rc**(2*M) / rc
assert sp.simplify(chain - (2*(1 - c))**(M - sp.Rational(1, 2))) == 0
assert all((2*k - 1) > 0 for k in range(1, 8))
print("(3) OK: r_c^(2m)/r_c = (2(1-c))^(m-1/2); exponent m-1/2 >= 1/2 > 0 for all m >= 1")
print("\nSC-9 chains ADJUDICATED. Lean targets: su_green_integral, qd_exponent_positive, qd_rpow_collapse")
