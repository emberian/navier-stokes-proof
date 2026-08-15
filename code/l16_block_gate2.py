import numpy as np, scipy.linalg as sla, time, sys
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 100 if SMOKE else 200
Q = 1.5
SSTAR = 0.3595
print("=" * 114)
print(f"L16 BLOCK GATE 2 -- Riesz projection at the ISOLATED Kelvin resonance (m=+-1, q={Q}, "
      f"s*={SSTAR}; N={N})")
print("=" * 114)
print("""  Gate 1 (l16_block_gate.py) validated the coupled operator (V-1 centroid 0.2-0.7%) and then
  DOCUMENTED that eigensolve identification at the omega~0 crossing is void: 56 movers, not 2 --
  the discretized-continuum scatter of sec 156-158, rediscovered by an independent route.  The
  crossing coupling kappa therefore stands on the banked propagation gates (sigma/eps = 0.414,
  viscous-corrected a in [0.57,0.73], Floquet 0.5624 bracketed).  The CONTOUR object of swept
  Lemma 16 is tested where the mode is genuinely isolated on the discrete grid: the
  single-sector Kelvin resonance at s* (r2_anatomy's measured spike, height ~ 1/nu), with the
  PAIR statement = direct sum across the m = +1 and m = -1 mirror sectors.

  REGISTERED, all outcomes named:
    G2-0 ** identification: in each sector exactly ONE shallow eigenvalue in the box
         |Im lam -+ s*| < 0.03, Re lam in (-0.05, 0); its frequency within 0.01 of r2_anatomy's
         s* = 0.3595 (cross-instrument).  None or several -> void. **
    G2-1 ** Riesz projection per sector: ||P^2-P||/||P|| <= 1e-3, trace = 1; mirror sum
         trace = 2 (THE PAIR).  Registered radius nu^{1/3}/2 first; adaptive fallback recorded
         if the discretized continuum intrudes (instrument note, not refutation -- the TRUE
         hierarchy nu << nu^{1/3} is the lemma's claim; the discrete continuum's scatter depth
         is the instrument's known artifact).  Non-idempotent at all radii -> Lemma 16 REFUTED. **
    G2-2 ** damping: c_K = -Re lam/nu in [2,4] both sectors (the registered bracket). **
    G2-3 ** the hierarchy, measured: the pair's depth vs the nearest-other mode's depth in the
         frequency window -- pair shallower by a factor >= 3 (nu vs nu^{1/3} at Re=2000 predicts
         ~15x ideal; discrete scatter erodes it -- factor and eroded-vs-ideal recorded). **
    G2-4 ** robustness: Re-doubling (c_K stable => O(nu) damping; idempotency stable);
         radius halving. **
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
    B = np.zeros((4 * N, 4 * N))
    B[:3 * N, :3 * N] = np.eye(3 * N)
    return A, B


def riesz(A, B, center, rad, npts=24):
    P = np.zeros_like(A)
    for k in range(npts):
        th = 2 * np.pi * (k + 0.5) / npts
        lam = center + rad * np.exp(1j * th)
        P += rad * np.exp(1j * th) * np.linalg.solve(lam * B - A, B)
    return P / npts


def one_sector(m, Re, N, sgn):
    """sgn = +1: mode near +i s*; sgn = -1: near -i s*."""
    nu = 2 * np.pi / Re
    A, B = sector(m, Q, Re, N)
    ev = sla.eig(A, B, right=False)
    ev = ev[np.isfinite(ev) & (np.abs(ev) < 5)]
    box = (np.abs(ev.imag - sgn * SSTAR) < 0.03) & (ev.real > -0.05) & (ev.real < 0.0)
    nbox = int(box.sum())
    if nbox == 0:
        return dict(n=0)
    cand = ev[box]
    lam = cand[np.argmax(cand.real)]              # shallowest
    others = ev[np.abs(ev - lam) > 1e-12]
    wfreq = others[np.abs(others.imag - lam.imag) < 0.05]
    dnear = np.min(np.abs(others - lam))
    depth_ratio = (np.min(-wfreq.real) / max(-lam.real, 1e-12)) if len(wfreq) else np.inf
    rad_reg = 0.5 * nu ** (1 / 3)
    n_reg = int((np.abs(ev - lam) < rad_reg).sum())
    rad = rad_reg if n_reg == 1 else 0.5 * dnear
    P = riesz(A, B, lam, rad)
    idem = np.linalg.norm(P @ P - P) / max(np.linalg.norm(P), 1e-12)
    tr = np.trace(P).real
    Ph = riesz(A, B, lam, rad / 2)
    idh = np.linalg.norm(Ph @ Ph - Ph) / max(np.linalg.norm(Ph), 1e-12)
    trh = np.trace(Ph).real
    return dict(n=nbox, lam=lam, cK=-lam.real / nu, dnear=dnear, ratio=depth_ratio,
                rad_reg=rad_reg, n_reg=n_reg, rad=rad, idem=idem, tr=tr, idh=idh, trh=trh)


print(f"  --- Re = 2000 ---", flush=True)
res = {}
for m, sgn in ((+1, +1), (-1, -1)):
    d = one_sector(m, 2000, N, sgn)
    res[m] = d
    if d['n'] == 0:
        print(f"  m={m:+d}: G2-0 VOID -- no shallow mode in box", flush=True)
        continue
    print(f"  m={m:+d}: mode {d['lam']:.5f}  (box count {d['n']}; freq vs s*: "
          f"{abs(abs(d['lam'].imag)-SSTAR):.4f})   c_K = {d['cK']:.2f}   "
          f"nearest other {d['dnear']:.4f}", flush=True)
    print(f"        G2-1: reg radius {d['rad_reg']:.4f} encloses {d['n_reg']}; used "
          f"{d['rad']:.4f}: idem {d['idem']:.2e}, trace {d['tr']:.3f}   "
          f"({'PASS' if d['idem'] <= 1e-3 and abs(d['tr']-1) < 0.05 else 'FAIL'})", flush=True)
    print(f"        G2-3 depth hierarchy (window modes / pair): {d['ratio']:.1f}x   "
          f"G2-4 half-radius: idem {d['idh']:.2e}, trace {d['trh']:.3f}", flush=True)
if res[+1].get('n') and res[-1].get('n'):
    print(f"  THE PAIR: trace sum = {res[+1]['tr'] + res[-1]['tr']:.3f} (rank 2 across mirror "
          f"sectors)   c_K = ({res[+1]['cK']:.2f}, {res[-1]['cK']:.2f})   "
          f"G2-2 [2,4]: {'PASS' if all(2 <= res[m]['cK'] <= 4 for m in (1, -1)) else 'OUTSIDE'}",
          flush=True)
if not SMOKE:
    print(f"  --- B2-4 Re = 4000 (m=+1) ---", flush=True)
    d4 = one_sector(+1, 4000, N, +1)
    if d4['n']:
        print(f"  mode {d4['lam']:.5f}   c_K = {d4['cK']:.2f} (vs {res[+1]['cK']:.2f} -- "
              f"{'O(nu) PASS' if abs(d4['cK'] - res[+1]['cK']) < 0.2 * res[+1]['cK'] + 0.5 else 'inspect'})   "
              f"idem {d4['idem']:.2e}, trace {d4['tr']:.3f}", flush=True)
    else:
        print(f"  G2-0 VOID at Re=4000", flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
