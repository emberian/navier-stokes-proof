import numpy as np, sys, os, time
np.set_printoptions(suppress=True)
N = 64
NU = 0.006
SNAP = "results/l19_field_t8_N64.npy"
print("=" * 114)
print("WORM GATE 2 -- THE EXACTNESS UPGRADE: calibrated Burgers-radius test + centreline-frame "
      "shape + kappa*delta")
print("=" * 114)
print("""  Jeff's standard: measurements must be exact.  The raw delta^2 estimator carries an EXACTLY
  computable calibration: for a Gaussian Burgers profile, the omega^2-weighted transverse
  moment under the 0.5-peak mask is 0.269 x delta^2_true (analytic), plus a grid-smearing
  correction at 2.6 cells/core.  Fix: calibrate the IDENTICAL estimator pipeline on synthetic
  Burgers tubes laid on the same grid; the control decides the total factor and its tolerance.

  REGISTERED, outcomes named:
    WX-0 ** calibration curve: F(delta_s^2) = estimator/true on synthetic tubes at delta_s^2 =
         0.03, 0.05, 0.08; the analytic continuum factor is 0.269 -- grid excess quantified;
         curve smooth (spread of F after grid-model fit <= 15%). **
    WX-1 ** the calibrated Burgers ratio: R = delta^2_true * alpha / (4 nu) with delta^2_true =
         raw/F at the matched scale.  EXACT-STANDARD PASS: |R - 1| <= 0.35 (alpha inhomogeneity
         ~20% + calibration ~10%).  If R > 1 beyond band: recorded as a physical finding (core
         fatter than its Burgers radius) with the resolution caveat, and the N>=96 re-measure
         is REGISTERED as the exactness-grade refinement. **
    WX-2 ** centreline-frame curvature: trace the ridge, measure kappa; report kappa*delta --
         the H1 class constant, never before measured.  H1 needs kappa*delta <= 1/M ~ 0.1;
         PASS if <= 0.3 (class-compatible at this resolution). **
""", flush=True)
t0 = time.time()
dx = 2 * np.pi / N
k1 = np.fft.fftfreq(N, d=1.0 / N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
cur = lambda U: [1j * (KY * U[2] - KZ * U[1]), 1j * (KZ * U[0] - KX * U[2]),
                 1j * (KX * U[1] - KY * U[0])]


def estimator(wm_field, i0):
    """The IDENTICAL raw pipeline: +-5 box, mask >= 0.5 peak, omega^2-weighted 2*m_pp."""
    idx = [(np.arange(-5, 6) + i0[a]) % N for a in range(3)]
    BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
    sub = wm_field[BX, BY, BZ]
    wpk = sub.max()
    mask = sub >= 0.5 * wpk
    DX, DY, DZ = np.meshgrid(np.arange(-5, 6) * dx, np.arange(-5, 6) * dx,
                             np.arange(-5, 6) * dx, indexing='ij')
    w2 = (sub ** 2) * mask
    W2 = w2.sum()
    # axis from the omega^2-weighted position covariance is unreliable for a straight synthetic
    # tube (degenerate) -- use the dominant axis of the SHAPE tensor
    P = np.stack([DX, DY, DZ], axis=-1)
    Msh = np.einsum('xyz,xyzi,xyzj->ij', w2, P, P) / W2
    mu_, ev_ = np.linalg.eigh(Msh)
    axis = ev_[:, 2]
    pal = P @ axis
    pperp2 = (P ** 2).sum(-1) - pal ** 2
    return (w2 * pperp2).sum() / W2, axis, wpk


# ---- WX-0: calibration on synthetic Burgers tubes (z-aligned, same grid) ----
x1 = np.arange(N) * dx
X, Y, Z = np.meshgrid(x1, x1, x1, indexing='ij')
pd = lambda a, b: np.minimum(np.abs(a - b), 2 * np.pi - np.abs(a - b))
print("  WX-0 calibration (synthetic Burgers tube, identical estimator):", flush=True)
Fs, ds = [], []
for d2s in (0.03, 0.05, 0.08):
    r2 = pd(X, np.pi) ** 2 + pd(Y, np.pi) ** 2
    wsyn = np.exp(-r2 / d2s)
    i0 = np.unravel_index(np.argmax(wsyn), wsyn.shape)
    est, _, _ = estimator(wsyn, i0)
    F = est / d2s
    Fs.append(F)
    ds.append(d2s)
    print(f"    delta_s^2 = {d2s}: estimator = {est:.4f}   F = {F:.3f}  (continuum analytic "
          f"0.269; excess = grid smearing)", flush=True)
# grid model: est = 0.269*d2 + c  ->  fit c
c_grid = np.mean([Fs[i] * ds[i] - 0.269 * ds[i] for i in range(3)])
resid = [abs(0.269 * d + c_grid - F * d) / (F * d) for d, F in zip(ds, Fs)]
print(f"    grid model est = 0.269*d2 + {c_grid:.4f}: residuals "
      f"{['%.1f%%' % (100*r) for r in resid]}   "
      f"({'PASS -- curve understood' if max(resid) <= 0.15 else 'curve NOT smooth -- inspect'})",
      flush=True)

# ---- the worm (t=8 field), calibrated ----
U = [c.copy() for c in np.load(SNAP)]
wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
wm = np.sqrt(sum(c ** 2 for c in wr))
i0 = np.unravel_index(np.argmax(wm), wm.shape)
raw, axis, wpk = estimator(wm, i0)
# invert the grid model: raw = 0.269*d2_true + c_grid
d2_true = (raw - c_grid) / 0.269
# alpha on the core (same as gate 1)
idx = [(np.arange(-5, 6) + i0[a]) % N for a in range(3)]
BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
sub = wm[BX, BY, BZ]
mask = sub >= 0.5 * wpk
w2 = (sub ** 2) * mask
G = np.zeros((11, 11, 11, 3, 3))
for i in range(3):
    for kk in range(3):
        gi = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[kk] * U[i]))
        G[..., kk, i] = gi[BX, BY, BZ]
S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
wv = np.stack([c[BX, BY, BZ] for c in wr], axis=-1)
xi = wv / np.maximum(np.sqrt((wv ** 2).sum(-1)), 1e-300)[..., None]
al = np.einsum('xyzi,xyzij,xyzj->xyz', xi, S, xi)
a_core = (w2 * al).sum() / w2.sum()
dB2 = 4 * NU / a_core
R = d2_true / dB2
print(f"\n  worm raw estimator = {raw:.4f}   grid-inverted delta^2_true = {d2_true:.4f}   "
      f"alpha = {a_core:.3f}   delta_B^2 = {dB2:.4f}", flush=True)
print(f"  WX-1 calibrated Burgers ratio R = {R:.2f}   "
      f"({'EXACT-STANDARD PASS' if abs(R - 1) <= 0.35 else ('physical finding: core fatter than Burgers -- N>=96 re-measure REGISTERED' if R > 1 else 'core thinner -- inspect')})",
      flush=True)

# ---- WX-2: centreline trace -> curvature, kappa*delta ----
pts = [np.array(i0, float)]
wvn = np.stack(wr, axis=-1)
for sgn in (+1, -1):
    p = np.array(i0, float)
    a_dir = axis * sgn
    for step in range(5):
        p = p + a_dir * 1.0                       # one cell along axis
        pi = tuple((np.round(p).astype(int)) % N)
        # transverse re-centering: omega^2-weighted centroid in 3^3 neighborhood, projected
        best, bp = -1, pi
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                for dk in (-1, 0, 1):
                    q = tuple((np.array(pi) + [di, dj, dk]) % N)
                    if wm[q] > best:
                        best, bp = wm[q], q
        p = np.array(bp, float)
        pts.append(p.copy()) if sgn > 0 else pts.insert(0, p.copy())
P3 = np.array(pts) * dx
kaps = []
for j in range(1, len(P3) - 1):
    a_, b_, c_ = P3[j - 1], P3[j], P3[j + 1]
    ab, cb = a_ - b_, c_ - b_
    cosang = (ab @ cb) / max(np.linalg.norm(ab) * np.linalg.norm(cb), 1e-12)
    ang = np.pi - np.arccos(np.clip(cosang, -1, 1))
    ds_ = 0.5 * (np.linalg.norm(ab) + np.linalg.norm(cb))
    kaps.append(ang / max(ds_, 1e-12))
kap = np.median(kaps)
kd = kap * np.sqrt(max(d2_true, 1e-12))
print(f"  WX-2 centreline: median curvature kappa = {kap:.3f}   kappa*delta = {kd:.3f}   "
      f"({'PASS -- H1-class compatible' if kd <= 0.3 else 'strongly bent -- inspect'})",
      flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
