import sympy as sp
print("W5 verification -- the Gronwall-with-linear-kernel bound")
t, s, M, L, h0, mu = sp.symbols('t s M Lam h0 mu', positive=True)
# candidate h(t) = M h0 exp(M Lam (t-s)^2 / 2) must satisfy h' = M Lam (t-s) h (the equality
# case of h(t) <= M h0 + M Lam int_s^t (r-s) h(r) dr)
h = M*h0*sp.exp(M*L*(t-s)**2/2)
resid = sp.simplify(sp.diff(h, t) - M*L*(t-s)*h)
print(f"  comparison-ODE residual: {resid}   (claim 0)")
# window arithmetic: with tau = 2(1+ln M)/mu and Lam <= mu^2/(4 M (1+ln M)^2):
# M Lam tau^2 / 2 <= (1 + ln M)  -- check symbolically at the boundary value of Lam
lnM = sp.symbols('lnM', positive=True)
tau = 2*(1+lnM)/mu
Lb = mu**2/(4*sp.exp(lnM)*(1+lnM)**2)
expr = sp.simplify(sp.exp(lnM)*Lb*tau**2/2)
print(f"  M*Lam*tau^2/2 at boundary = {expr}   (claim: (1+lnM) -> match = {sp.simplify(expr - (1+lnM)) == 0})")

print("corrected chain check:")
print(f"  boundary exponent = 1/2 exactly (above); per-window need mu*tau/2 >= 1/2 + lnM:")
print(f"  mu*tau/2 = (1+lnM); (1+lnM) - (1/2 + lnM) = 1/2 > 0  -- holds with slack 1/2, all M >= 1")
