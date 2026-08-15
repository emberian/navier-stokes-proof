"""SC-2 adjudication: Lemma CP's exact core.

(1) The shifted-2D-field veto: u(x,y,z) = (u1(x-hx(z), y-hy(z)), u2(...), 0) with u_2D
    solenoidal has div u = 0 and S_33 = d_z u_z = 0 IDENTICALLY, while its vorticity
    carries the first-order tilt (omega_perp != 0) — the bent companion's axial strain
    vanishes at first order in bend.
(2) The residue expansion: for symmetric S with S_33 = 0 and
    xi = (sin t cos p, sin t sin p, cos t), the pairing xi^T S xi has NO cos^2 t term —
    every term is >= first order in sin t, pairing against the off-axis entries (themselves
    first-order in tilt) — total residue quadratic.
(3) The payment algebra: theta_eq = C*g*d^2/G  ==>  theta_eq^2 * G/d^2 = C^2 g^2 d^2/G;
    at d^2 = G/g this is C^2 g exactly; and the band-sum gamma-cancellation:
    (g^2/Gmin) * (4*nu*Om/(c1*g*cE*Gmin^2*L)) * (Gmax/g) is gamma-free.
(4) The cell-shell series: sum 2^{3k} * 2^{-8k} * 2^{3k} = sum 4^{-k} = 4/3 — identical to
    w9_shell_series (certificate carries over).
"""
import sympy as sp

# ---- (1) shifted-2D-field veto (stream-function form: solenoidality built in) ----
x, y, z = sp.symbols('x y z')
psi = sp.Function('psi')
hx = sp.Function('hx')
hy = sp.Function('hy')
X, Y = x - hx(z), y - hy(z)
u = sp.Matrix([sp.diff(psi(X, Y), y), -sp.diff(psi(X, Y), x), 0])
div_u = sp.simplify(sp.diff(u[0], x) + sp.diff(u[1], y) + sp.diff(u[2], z))
assert div_u == 0
S33 = sp.diff(u[2], z)
assert S33 == 0
S13 = sp.simplify(sp.Rational(1, 2) * (sp.diff(u[0], z) + sp.diff(u[2], x)))
om_x = sp.simplify(sp.diff(u[2], y) - sp.diff(u[1], z))   # transverse vorticity = tilt
assert S13 != 0 and om_x != 0
# both are first order in the tilt h': they vanish identically when h' = 0
noh = {sp.Derivative(hx(z), z): 0, sp.Derivative(hy(z), z): 0}
assert sp.simplify(S13.subs(noh)) == 0 and sp.simplify(om_x.subs(noh)) == 0
print("(1) OK: shifted 2D field — div u = 0, S_33 = 0 EXACTLY; off-axis strain and")
print("        transverse vorticity are first-order in h' (vanish when h' = 0) — as claimed")

# ---- (2) residue expansion: no cos^2 term when S_33 = 0 ----
t, p = sp.symbols('theta phi')
S11, S12, S13s, S22, S23 = sp.symbols('S11 S12 S13 S22 S23')
S = sp.Matrix([[S11, S12, S13s], [S12, S22, S23], [S13s, S23, 0]])
xi = sp.Matrix([sp.sin(t) * sp.cos(p), sp.sin(t) * sp.sin(p), sp.cos(t)])
pairing = sp.expand_trig(sp.expand((xi.T * S * xi)[0]))
claimed = (2 * sp.sin(t) * sp.cos(t) * (S13s * sp.cos(p) + S23 * sp.sin(p))
           + sp.sin(t)**2 * (S11 * sp.cos(p)**2 + 2 * S12 * sp.cos(p) * sp.sin(p)
                             + S22 * sp.sin(p)**2))
assert sp.simplify(pairing - claimed) == 0
cos2_coeff = pairing.coeff(sp.cos(t), 2)
assert sp.simplify(cos2_coeff) == 0
print("(2) OK: xi^T S xi = 2 sc(S13 cp + S23 sp) + s^2(...) — NO cos^2(theta) term;")
print("        matches the displayed expansion exactly (Lean: cp_axial_residue)")

# ---- (3) payment algebra ----
g, d, G, C = sp.symbols('gamma d Gamma C', positive=True)
theta_eq = C * g * d**2 / G
payment = theta_eq**2 * G / d**2
assert sp.simplify(payment - C**2 * g**2 * d**2 / G) == 0
assert sp.simplify(payment.subs(d**2, G / g) - C**2 * g) == 0
nu, Om, c1, cE, Gmin, Gmax, L, Cv = sp.symbols(
    'nu Omega c1 c_E Gamma_min Gamma_max L C_v', positive=True)
N_band = 4 * nu * Om / (c1 * g * cE * Gmin**2 * L)
band_total = Cv * C**2 * (g**2 / Gmin) * N_band * (Gmax / g)
cancelled = sp.simplify(band_total)
assert g not in cancelled.free_symbols
assert sp.simplify(cancelled - 4 * Cv * C**2 * nu * Om * Gmax / (c1 * cE * Gmin**3 * L)) == 0
print("(3) OK: payment = C^2 g^2 d^2/G; = C^2 gamma at d^2 = G/gamma; band sum =")
print(f"        {cancelled} — GAMMA-FREE: C_n nu Omega form confirmed")

# ---- (4) cell-shell series ----
k = sp.symbols('k', integer=True, nonnegative=True)
series = sp.summation((sp.Rational(1, 4))**k, (k, 0, sp.oo))
assert series == sp.Rational(4, 3)
print("(4) OK: sum 4^{-k} = 4/3 — identical series, w9_shell_series certificate carries over")

print("\nSC-2 chain ADJUDICATED. Lean targets: cp_veto_shifted_field (matrix form),")
print("cp_axial_residue, cp_payment_algebra")
