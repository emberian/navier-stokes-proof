import numpy as np, time, sys
from scipy.linalg import solve_banded
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
print("=" * 112)
print("L14 DIRECT-RESIDUAL GATE -- measure Lemma 13's residual itself against nu^{1/3}L(nu)")
print("=" * 112)
print("""  The swept Lemma 13 claims: the matched approximation psi_app = (1-chi_ell) psi0 + chi_ell
  psi_lay (ell = nu^{1/6}) has FILTERED residual <= C nu^{1/3} L(nu) under the viscous operator.
  The banked gates measured the SOLUTION-level consequences; this instrument measures the
  RESIDUAL itself.  m = 2, s = 1.0 (interior band, r_c ~ 1.256), Lamb-Oseen column.
  Stream-function form: [(is - eps - im*Omega) Dm + im*diag(c)] phi = f  (banded), psi = Dm phi.

  REGISTERED, outcomes named:
    DR-1 ** relative filtered residual ||Dm^{-1}R||/||Dm^{-1}f|| decreases across Re = 2000 ->
         8000 -> 32000 with fitted exponent in nu of >= 0.25 (nu^{1/3} with log dilution;
         faster is consistent -- the lemma is an upper bound).  REFUTED if exponent <= 0.1 on
         the correct branch: the matched construction would be wrong. **
    DR-2 ** branch visibility: the outer solve with the WRONG limiting-absorption sign floors
         at O(1) mismatch (the layer's viscous branch disagrees) while the right sign decays --
         branch selection measured, not assumed. **
    DR-3 ** resolution control at the largest Re: doubling N changes the residual < 10%. **
""", flush=True)
t0 = time.time()
m, s, R0 = 2, 1.0, 10.0
Om = lambda r: (1 - np.exp(-r ** 2)) / r ** 2
cc = lambda r: -4 * np.exp(-r ** 2)


def build(N):
    dr = R0 / N
    r = (np.arange(1, N)) * dr                      # interior nodes, Dirichlet both ends
    lo = 1 / dr ** 2 - 1 / (2 * r * dr)
    di = -2 / dr ** 2 - m ** 2 / r ** 2
    up = 1 / dr ** 2 + 1 / (2 * r * dr)
    return r, dr, lo, di, up


def Dm_apply(psi, lo, di, up):
    out = di * psi
    out[1:] += lo[1:] * psi[:-1]
    out[:-1] += up[:-1] * psi[1:]
    return out


def banded_solve(diag_main, lo, up, rhs):
    n = len(diag_main)
    ab = np.zeros((3, n), complex)
    ab[0, 1:] = up[:-1]
    ab[1] = diag_main
    ab[2, :-1] = lo[1:]
    return solve_banded((1, 1), ab, rhs)


def run(Re, N, epsign):
    nu = 1.0 / Re
    r, dr, lo, di, up = build(N)
    Omr, cr = Om(r), cc(r)
    f = r ** 2 * np.exp(-r ** 2)
    # eps must RESOLVE the regularization layer on the grid (width eps/|v| >~ 3 dr) yet stay
    # subdominant to the nu^{1/3} ledger: eps = nu^{1/2} satisfies both at N >= 2000
    eps = nu ** 0.5 * epsign
    # inviscid outer: [(is - eps - i m Om) Dm + i m c] phi = f (banded), psi0 = Dm phi
    # row j of (a Dm): a_j*lo_j, a_j*di_j, a_j*up_j
    a = (1j * s - eps - 1j * m * Omr)
    ab = np.zeros((3, len(r)), complex)
    ab[0, 1:] = a[:-1] * up[:-1]
    ab[1] = a * di + 1j * m * cr
    ab[2, :-1] = a[1:] * lo[1:]
    phi0 = solve_banded((1, 1), ab, f)
    psi0 = Dm_apply(phi0, lo, di, up)
    # critical layer
    ic = np.argmin(np.abs(m * Omr - s))
    rc = r[ic]
    v = m * (Om(rc + 1e-6) - Om(rc - 1e-6)) / 2e-6
    frc = f[ic]
    ell = nu ** (1 / 6.0)
    w = 0.6
    win = np.abs(r - rc) <= w
    z = r[win] - rc
    nw = win.sum()
    # layer model, matching the TRUE operator near r_c: i(s-mOm)psi + nu psi'' ~ (-i v z + nu d2)
    # psi = frc, outer asymptote psi -> frc/(-i v z); BC at window ends
    abl = np.zeros((3, nw), complex)
    abl[0, 1:] = nu / dr ** 2
    abl[1] = -1j * v * z - 2 * nu / dr ** 2
    abl[2, :-1] = nu / dr ** 2
    rhsl = np.full(nw, frc, complex)
    rhsl[0] -= nu / dr ** 2 * (frc / (-1j * v * z[0]))
    rhsl[-1] -= nu / dr ** 2 * (frc / (-1j * v * z[-1]))
    psil_w = solve_banded((1, 1), abl, rhsl)
    psil = np.zeros_like(psi0)
    psil[win] = psil_w
    chi = np.exp(-((r - rc) / ell) ** 4) * win
    # ADDITIVE composite (the correct matched construction): keep the outer solution's regular
    # part everywhere; swap only its frozen singular part for the viscous layer.
    # psi_frozen = frc / (i(s - mOm)_lin + eps-term) = frc / (-i v z - eps), same branch as psi0.
    psi_froz = frc / (-1j * v * (r - rc) - eps)
    psi_app = psi0 + chi * (psil - psi_froz)
    # viscous residual: R = (-i m Om + i s) psi + i m c Dm^{-1} psi + nu Dm psi - f
    ab2 = np.zeros((3, len(r)), complex)
    ab2[0, 1:] = up[:-1]
    ab2[1] = di
    ab2[2, :-1] = lo[1:]
    phi_app = solve_banded((1, 1), ab2, psi_app)
    Rres = (1j * s - 1j * m * Omr) * psi_app + 1j * m * cr * phi_app \
        + nu * Dm_apply(psi_app, lo, di, up) - f
    phiR = solve_banded((1, 1), ab2, Rres)
    phif = solve_banded((1, 1), ab2, f)
    return np.abs(phiR).max() / np.abs(phif).max()


RES = [2000, 8000] if SMOKE else [2000, 8000, 32000]
NN = 2000 if SMOKE else 4000
print(f"{'Re':>8}{'nu^(1/3)':>10}{'rel resid (+eps)':>18}{'rel resid (-eps)':>18}", flush=True)
good, bad = [], []
for Re in RES:
    rp = run(Re, NN, +1.0)
    rm = run(Re, NN, -1.0)
    good.append(min(rp, rm))
    bad.append(max(rp, rm))
    print(f"{Re:>8}{(1/Re)**(1/3):>10.4f}{rp:>18.5f}{rm:>18.5f}", flush=True)
lnu = np.log([1.0 / Re for Re in RES])
expo = np.polyfit(lnu, np.log(good), 1)[0]
floor = bad[-1] / bad[0]
print(f"\n  DR-1 fitted exponent (correct branch = smaller residual): {expo:.3f}   "
      f"({'PASS' if expo >= 0.25 else ('REFUTED' if expo <= 0.1 else 'MARGINAL -- inspect')})",
      flush=True)
print(f"  DR-2 wrong-branch floor: residual ratio across Re = {floor:.2f} "
      f"({'floors/decays slowly -- branch visible' if floor > 0.5 else 'also decays -- NOT discriminating, inspect'})",
      flush=True)
if not SMOKE:
    rchk = run(RES[-1], 2 * NN, +1.0)
    rbase = run(RES[-1], NN, +1.0)
    dchg = abs(rchk - rbase) / rbase
    print(f"  DR-3 resolution control at Re={RES[-1]}: N {NN} -> {2*NN}: change {100*dchg:.1f}%   "
          f"({'PASS' if dchg < 0.10 else 'GRID ARTIFACT'})", flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
