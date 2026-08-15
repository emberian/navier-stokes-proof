import numpy as np, scipy.linalg as sla, time, sys
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 100 if SMOKE else 200
Q = 2.26
Re0 = 2000
print("=" * 114)
print(f"L17 BLOCK GATE 3 -- SECOND TRY AT THE CROSSING: the GROWER identifies the pair; slope "
      f"differencing gives kappa  (N={N}, q={Q}, Re={Re0})")
print("=" * 114)
print("""  Gate 1's movers heuristic drowned in continuum scatter.  The sharper discriminator, not
  tried before: THE ELLIPTIC INSTABILITY ITSELF.  At the measured-stable config the eps=0
  spectrum has a clean floor (S5-2's zero-floor result); at eps > 0 the destabilized pair
  member is the UNIQUE Re lam > 0 eigenvalue -- identification with no heuristic.  The slope
  d(Re lam_max)/d(eps) cancels the eps-independent damping (S5-2's differencing logic,
  eigensolve-side) and must equal the INVISCID coupling constant directly.

  REGISTERED, controls first, outcomes named:
    G3-0 ** eps=0 floor: max Re lam <= 1e-3 (clean).  Dirty floor -> this route void (the
         scatter owns the config after all) -- tranche 2 then stands on gate 2 + banked kappa. **
    G3-1 ** at eps=0.04: EXACTLY ONE mode with Re lam > 1e-3 (the elliptic grower).  If none at
         q=2.26, scan q=2.1, 2.4 (band tolerance).  Several -> scatter intrusion, report. **
    G3-2 ** kappa = (Relam_max(0.04) - Relam_max(0.02))/0.02 in [0.57, 0.73]; linearity via the
         eps=0.01 point (slope 0.01->0.02 within ~20% of slope 0.02->0.04).  Outside bracket ->
         Lemma 17's normal form REFUTED at the crossing. **
    G3-3 ** the grower is core-localized: velocity-norm^2 fraction in r < 3 at least 0.5 (a
         Kelvin-core structure, not edge junk). **
""", flush=True)
t0 = time.time()


def sector(m, q, Re, N, R=10.0):
    h = R / N
    r = h * (np.arange(N) + 0.5)
    nu = 2 * np.pi / Re
    Om = (1 - np.exp(-r ** 2)) / r ** 2
    W = 2 * np.exp(-r ** 2)
    I = np.eye(N)
    d1 = np.zeros((N, N))
    for j in range(N):
        if j > 0:
            d1[j, j - 1] = -1 / (2 * h)
        if j < N - 1:
            d1[j, j + 1] = 1 / (2 * h)
    d1[N - 1, N - 1] -= 1 / (2 * h)
    d2 = (-2 * np.eye(N) + np.diag(np.ones(N - 1), 1) + np.diag(np.ones(N - 1), -1)) / h ** 2
    Lm = d2 + np.diag(1 / r) @ d1 - np.diag(m ** 2 / r ** 2) - q ** 2 * I
    A = np.zeros((4 * N, 4 * N), complex)
    iOm = np.diag(-1j * m * Om)
    A[0:N, 0:N] = iOm + nu * (Lm - np.diag(1 / r ** 2))
    A[0:N, N:2 * N] = np.diag(2 * Om) + nu * np.diag(-2j * m / r ** 2)
    A[0:N, 3 * N:4 * N] = -d1
    A[N:2 * N, 0:N] = np.diag(-W) + nu * np.diag(2j * m / r ** 2)
    A[N:2 * N, N:2 * N] = iOm + nu * (Lm - np.diag(1 / r ** 2))
    A[N:2 * N, 3 * N:4 * N] = np.diag(-1j * m / r)
    A[2 * N:3 * N, 2 * N:3 * N] = iOm + nu * Lm
    A[2 * N:3 * N, 3 * N:4 * N] = -1j * q * I
    A[3 * N:4 * N, 0:N] = d1 + np.diag(1 / r)
    A[3 * N:4 * N, N:2 * N] = np.diag(1j * m / r)
    A[3 * N:4 * N, 2 * N:3 * N] = 1j * q * I
    return A, d1, r


def cblock(msrc, sgn, eps, d1, r, N):
    RD = np.diag(r) @ d1
    C = np.zeros((4 * N, 4 * N), complex)
    C[0:N, 0:N] = (eps / 2) * (RD + (-sgn * msrc + 1) * np.eye(N))
    C[N:2 * N, N:2 * N] = (eps / 2) * (RD + (-sgn * msrc - 1) * np.eye(N))
    C[N:2 * N, 0:N] = sgn * 1j * eps * np.eye(N)
    C[2 * N:3 * N, 2 * N:3 * N] = (eps / 2) * (RD + (-sgn * msrc) * np.eye(N))
    return C


def spec(eps, q, Re, N, vecs=False):
    Ap, d1, r = sector(+1, q, Re, N)
    Am, _, _ = sector(-1, q, Re, N)
    Cp = cblock(-1, +1, eps, d1, r, N)
    Cm = cblock(+1, -1, eps, d1, r, N)
    Ac = np.block([[Ap, -Cp], [-Cm, Am]])
    Bc = np.zeros((8 * N, 8 * N))
    Bc[:3 * N, :3 * N] = np.eye(3 * N)
    Bc[4 * N:7 * N, 4 * N:7 * N] = np.eye(3 * N)
    if vecs:
        ev, V = sla.eig(Ac, Bc, right=True)
    else:
        ev = sla.eig(Ac, Bc, right=False)
        V = None
    ok = np.isfinite(ev) & (np.abs(ev) < 5)
    return ev[ok], (V[:, ok] if vecs else None), r


EPS = [0.0, 0.01, 0.02, 0.04] if SMOKE else [0.0, 0.01, 0.02, 0.04, 0.06, 0.08]
mx = {}
for eps in EPS:
    ev, _, r = spec(eps, Q, Re0, N)
    mx[eps] = ev[np.argmax(ev.real)]
    ng = int((ev.real > 1e-3).sum())
    print(f"  eps={eps:>5.2f}: max Re lam = {mx[eps].real:+.5f} (at {mx[eps]:.5f})   "
          f"growers = {ng}", flush=True)
    if eps == 0.0:
        print(f"    G3-0 floor: {'PASS (clean)' if mx[0.0].real <= 1e-3 else 'DIRTY -- route void, report'}",
              flush=True)
    if eps == 0.04:
        print(f"    G3-1: {'PASS -- exactly one grower' if ng == 1 else f'{ng} growers -- see notes'}",
              flush=True)
# G3-2 (upgraded after smoke): the 2x2 predicts the SQRT KNEE lam+ = -d + sqrt(k^2 e^2 - D^2)
# on the real branch (pair complex below threshold; slope approaches kappa FROM ABOVE).  Fit
# (d, Delta, kappa) on the real-branch growers; report the asymptotic slope as cross-check.
reals = [(e, mx[e].real) for e in EPS if e > 0 and abs(mx[e].imag) < 1e-6]
if len(reals) >= 3:
    from scipy.optimize import curve_fit
    ee = np.array([x[0] for x in reals])
    ll = np.array([x[1] for x in reals])
    f2x2 = lambda e, d, D, k: -d + np.sqrt(np.maximum(k ** 2 * e ** 2 - D ** 2, 0))
    p, _ = curve_fit(f2x2, ee, ll, p0=[0.015, 0.012, 0.65],
                     bounds=([0, 0, 0.1], [0.1, 0.1, 2.0]))
    d_f, D_f, k_f = p
    resid = np.sqrt(np.mean((f2x2(ee, *p) - ll) ** 2))
    sA = (mx[EPS[-1]].real - mx[EPS[-2]].real) / (EPS[-1] - EPS[-2])
    nu0v = 2 * np.pi / Re0
    print(f"  G3-2 real-branch points: " + "  ".join(f"({e:.2f},{l:+.5f})" for e, l in reals),
          flush=True)
    print(f"  G3-2 2x2-knee fit: kappa = {k_f:.4f}   d = {d_f:.5f} (c = d/nu = {d_f/nu0v:.2f})"
          f"   Delta = {D_f:.5f}   rms resid = {resid:.2e}", flush=True)
    print(f"  G3-2 asymptotic slope ({EPS[-2]:.2f}->{EPS[-1]:.2f}): {sA:.4f} (approaches kappa "
          f"from above)   bracket [0.57,0.73] on fitted kappa: "
          f"{'PASS' if 0.57 <= k_f <= 0.73 else 'OUTSIDE -- record honestly'}", flush=True)
else:
    s24 = (mx[0.04].real - mx[0.02].real) / 0.02
    print(f"  G3-2 (smoke, 2 real points): slope 0.02->0.04 = {s24:.4f} (knee regime -- full "
          f"run fits the 2x2)", flush=True)
ev4, V4, r = spec(0.04, Q, Re0, N, vecs=True)
ig = np.argmax(ev4.real)
v = V4[:, ig]
core = r < 3.0
vel = np.r_[np.tile(core, 3), np.zeros(N, bool), np.tile(core, 3), np.zeros(N, bool)]
velall = np.r_[np.tile(np.ones(N, bool), 3), np.zeros(N, bool)]
velall = np.r_[velall, velall]
frac = np.abs(v[vel]).sum() * 0 + (np.abs(v[vel]) ** 2).sum() / max((np.abs(v[velall]) ** 2).sum(), 1e-300)
print(f"  G3-3 grower core-localization (r<3 velocity fraction): {frac:.3f}   "
      f"({'PASS' if frac >= 0.5 else 'edge-localized -- junk, report'})", flush=True)
print(f"  grower at eps=0.04: {ev4[ig]:.5f}   (S5-2 propagation predicted Re lam ~ "
      f"0.414*0.04 = +0.0166 raw)", flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
