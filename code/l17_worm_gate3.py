import numpy as np, sys, os, time
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N0, N = 64, (64 if SMOKE else 128)
NU = 0.006
TSET = 0.1 if SMOKE else 0.5
SNAP = "results/l19_field_t8_N64.npy"
print("=" * 114)
print(f"WORM GATE 3 -- EXACTNESS AT RESOLUTION: spectral upsample to N={N}, settle {TSET}, "
      f"calibrated Burgers ratio + fixed centreline tracer")
print("=" * 114)
print("""  Gate 2's calibration control PROVED the N=64 estimator is mask-quantization-dominated
  (curve residuals to 27% at 2-3 cells/core) -- no calibration factor fixes quantization.
  Exactness path: zero-pad the t=8 field to N=128 (spectrally EXACT), settle 0.5 time units
  (~1 strain time, fine scales regenerate), re-calibrate the identical estimator on the finer
  grid, re-measure.  Tracer bug fixed (2-cell march, min-image segments, degenerates skipped).

  REGISTERED, outcomes named:
    Y-0 ** calibration curve at N=128 SMOOTH: grid-model residuals <= 10% across delta_s^2 =
        0.02/0.035/0.05 (quantization beaten).  Else resolution still insufficient -- report. **
    Y-1 ** calibrated Burgers ratio R = delta^2_true*alpha/(4nu): EXACT-STANDARD PASS
        |R - 1| <= 0.35.  R > 1.35: physical finding (core fatter than Burgers) -- then the
        settling-time control decides: if R DROPS from the unsettled value, the excess was
        upsample transient; report the settled number as the measurement. **
    Y-2 ** kappa*delta from the fixed tracer: <= 0.3 (H1-class compatible). **
""", flush=True)
t0 = time.time()
nu = NU
dx = 2 * np.pi / N
k1 = np.fft.fftfreq(N, d=1.0 / N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K2 = KX ** 2 + KY ** 2 + KZ ** 2
K2s = np.where(K2 == 0, 1, K2)
km = N // 3
dl = (np.abs(KX) <= km) & (np.abs(KY) <= km) & (np.abs(KZ) <= km)
cur = lambda U: [1j * (KY * U[2] - KZ * U[1]), 1j * (KZ * U[0] - KX * U[2]),
                 1j * (KX * U[1] - KY * U[0])]


def proj(U):
    d = (KX * U[0] + KY * U[1] + KZ * U[2]) / K2s
    return [U[i] - Kc * d for i, Kc in enumerate((KX, KY, KZ))]


def rhs(U):
    u = [np.real(np.fft.ifftn(c)) for c in U]
    w = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    cr = [u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0]]
    return [f - nu * K2 * U[i] for i, f in enumerate(proj([np.fft.fftn(c) * dl for c in cr]))]


def upsample(u64):
    """Zero-pad spectral upsample N0 -> N (exact)."""
    out = np.zeros((N, N, N), complex)
    h = N0 // 2
    ix = np.r_[0:h, N - h:N]
    src = np.r_[0:h, N0 - h:N0]
    out[np.ix_(ix, ix, ix)] = u64[np.ix_(src, src, src)] * (N / N0) ** 0  # coeff convention: fftn unnormalized -> scale by (N/N0)^3 on ifft; keep values: multiply by (N/N0)^3
    return out * (N / N0) ** 3


BOX = 10 if N == 128 else 5     # same physical size (+-5 cells at N=64 = +-10 at N=128)


def estimator(wm_field, i0):
    idx = [(np.arange(-BOX, BOX + 1) + i0[a]) % N for a in range(3)]
    BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
    sub = wm_field[BX, BY, BZ]
    wpk = sub.max()
    mask = sub >= 0.5 * wpk
    ar = np.arange(-BOX, BOX + 1) * dx
    DX, DY, DZ = np.meshgrid(ar, ar, ar, indexing='ij')
    w2 = (sub ** 2) * mask
    W2 = w2.sum()
    P = np.stack([DX, DY, DZ], axis=-1)
    Msh = np.einsum('xyz,xyzi,xyzj->ij', w2, P, P) / W2
    mu_, ev_ = np.linalg.eigh(Msh)
    axis = ev_[:, 2]
    pal = P @ axis
    pperp2 = (P ** 2).sum(-1) - pal ** 2
    return (w2 * pperp2).sum() / W2, axis, wpk, (BX, BY, BZ)


# ---- Y-0: calibration at this N ----
x1 = np.arange(N) * dx
X, Y = np.meshgrid(x1, x1, indexing='ij')
pd = lambda a, b: np.minimum(np.abs(a - b), 2 * np.pi - np.abs(a - b))
print(f"  Y-0 calibration at N={N}:", flush=True)
Fs, ds = [], []
for d2s in (0.02, 0.035, 0.05):
    r2 = pd(X, np.pi) ** 2 + pd(Y, np.pi) ** 2
    wsyn = np.repeat(np.exp(-r2 / d2s)[:, :, None], N, axis=2)
    i0 = (N // 2, N // 2, N // 2)
    est, _, _, _ = estimator(wsyn, i0)
    Fs.append(est / d2s)
    ds.append(d2s)
    print(f"    delta_s^2 = {d2s}: est = {est:.5f}   F = {est/d2s:.3f}", flush=True)
c_grid = np.mean([Fs[i] * ds[i] - 0.269 * ds[i] for i in range(3)])
resid = [abs(0.269 * d + c_grid - F * d) / (F * d) for d, F in zip(ds, Fs)]
y0 = max(resid) <= 0.10
print(f"    grid model est = 0.269*d2 + {c_grid:.5f}: residuals "
      f"{['%.1f%%' % (100*r) for r in resid]}   "
      f"({'PASS -- quantization beaten' if y0 else 'still rough -- report'})", flush=True)

# ---- upsample + settle ----
U64 = np.load(SNAP)
U = [upsample(c) for c in U64] if N != N0 else [c.copy() for c in U64]
t = 0.0
dt = 1e-3 if N == 128 else 2e-3
while t < TSET - 1e-12:
    h = min(dt, TSET - t)
    a_ = rhs(U)
    Um = [U[i] + 0.5 * h * a_[i] for i in range(3)]
    b_ = rhs(Um)
    U = [U[i] + h * b_[i] for i in range(3)]
    t += h
print(f"  settled to t = 8 + {TSET} at N={N} ({time.time()-t0:.0f}s)", flush=True)

# ---- Y-1: the worm, calibrated ----
wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
wm = np.sqrt(sum(c ** 2 for c in wr))
i0 = np.unravel_index(np.argmax(wm), wm.shape)
raw, axis, wpk, (BX, BY, BZ) = estimator(wm, i0)
d2_true = (raw - c_grid) / 0.269
sub = wm[BX, BY, BZ]
mask = sub >= 0.5 * wpk
w2 = (sub ** 2) * mask
nb = 2 * BOX + 1
G = np.zeros((nb, nb, nb, 3, 3))
for i in range(3):
    for kk in range(3):
        gi = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[kk] * U[i]))
        G[..., kk, i] = gi[BX, BY, BZ]
S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
wv = np.stack([c[BX, BY, BZ] for c in wr], axis=-1)
xi = wv / np.maximum(np.sqrt((wv ** 2).sum(-1)), 1e-300)[..., None]
al = np.einsum('xyzi,xyzij,xyzj->xyz', xi, S, xi)
a_core = (w2 * al).sum() / w2.sum()
dB2 = 4 * nu / a_core
R = d2_true / dB2
print(f"  Y-1: raw = {raw:.5f}   delta^2_true = {d2_true:.4f}   alpha = {a_core:.3f}   "
      f"delta_B^2 = {dB2:.4f}   R = {R:.2f}   "
      f"({'EXACT-STANDARD PASS' if abs(R-1) <= 0.35 else ('physical: fatter than Burgers' if R > 1 else 'thinner -- inspect')})",
      flush=True)

# ---- Y-2: fixed centreline tracer ----
def minimg(v):
    return (v + N // 2) % N - N // 2


pts = [np.array(i0, float)]
for sgn in (+1, -1):
    p = np.array(i0, float)
    prev = tuple(np.round(p).astype(int) % N)
    a_dir = axis * sgn
    for step in range(6):
        p = p + a_dir * 2.0
        pi = np.round(p).astype(int) % N
        # SUB-CELL centreline point: omega^2-weighted centroid over the 5^3 neighborhood
        # (continuous coordinates -- voxel zigzag was dominating the curvature at cell scale)
        wsum, csum, wmax = 0.0, np.zeros(3), 0.0
        for di in range(-2, 3):
            for dj in range(-2, 3):
                for dk in range(-2, 3):
                    off = np.array([di, dj, dk])
                    q = tuple((pi + off) % N)
                    w_ = wm[q] ** 2
                    wsum += w_
                    csum += w_ * (pi + off)
                    wmax = max(wmax, wm[q])
        if wmax < 0.3 * wpk:
            break
        p = csum / wsum
        pts.append(p.copy()) if sgn > 0 else pts.insert(0, p.copy())
kaps = []
for j in range(1, len(pts) - 1):
    a_ = minimg(pts[j - 1] - pts[j]) * dx
    c_ = minimg(pts[j + 1] - pts[j]) * dx
    na, nc = np.linalg.norm(a_), np.linalg.norm(c_)
    if na < 0.5 * dx or nc < 0.5 * dx:
        continue
    ang = np.pi - np.arccos(np.clip((a_ @ c_) / (na * nc), -1, 1))
    kaps.append(ang / (0.5 * (na + nc)))
if kaps:
    kap = float(np.median(kaps))
    kd = kap * np.sqrt(max(d2_true, 1e-12))
    print(f"  Y-2: centreline points = {len(pts)}, median kappa = {kap:.3f}, kappa*delta = "
          f"{kd:.3f}   ({'PASS -- H1-class compatible' if kd <= 0.3 else 'strongly bent'})",
          flush=True)
else:
    print("  Y-2: tracer degenerate -- report", flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
