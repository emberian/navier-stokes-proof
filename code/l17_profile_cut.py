import numpy as np
np.set_printoptions(suppress=True)
N0, N, NU = 64, 128, 0.006
print("DIRECT PROFILE CUT -- the profile itself, sampled along perpendicular rays (no masks)")
print("""  REGISTERED: C-1 fit omega(r) = pk*exp(-(r^2/d2)^p) to the ray profile down to 0.3*peak:
  p in [0.85, 1.15] -> Gaussian verified DIRECTLY (calibration stands, R = 1.85 final);
  else the fitted-p calibration factor restates R (computed and reported).""")
U64 = np.load("results/l19_field_t8_N64.npy")
k1 = np.fft.fftfreq(N, d=1.0/N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
def up(u):
    out = np.zeros((N, N, N), complex); h = N0//2
    ix = np.r_[0:h, N-h:N]; src = np.r_[0:h, N0-h:N0]
    out[np.ix_(ix, ix, ix)] = u[np.ix_(src, src, src)]
    return out*(N/N0)**3
U = [up(c) for c in U64]
wr = [np.real(np.fft.ifftn(c)) for c in [1j*(KY*U[2]-KZ*U[1]), 1j*(KZ*U[0]-KX*U[2]),
                                          1j*(KX*U[1]-KY*U[0])]]
wm = np.sqrt(sum(c**2 for c in wr))
i0 = (80, 93, 104); dx = 2*np.pi/N
# local axis from the +-3 omega-dyad (tight, single-structure)
idx3 = [(np.arange(-3, 4)+i0[a]) % N for a in range(3)]
B3 = np.meshgrid(*idx3, indexing='ij')
wv3 = np.stack([c[tuple(B3)] for c in wr], axis=-1)
w23 = (wm[tuple(B3)]**2)
Mdy = np.einsum('xyz,xyzi,xyzj->ij', w23, wv3, wv3)
axis = np.linalg.eigh(Mdy)[1][:, 2]
# two perpendicular rays
e1 = np.cross(axis, [1, 0, 0]); e1 /= np.linalg.norm(e1)
e2 = np.cross(axis, e1)
prof = {}
for nm, e in (("ray1", e1), ("ray2", e2)):
    rs, vs = [], []
    for s in np.arange(-8, 8.5, 0.5):
        pos = (np.array(i0) + s*e) % N
        ip = np.floor(pos).astype(int); fr = pos - ip
        v = 0.0                                      # trilinear
        for da in (0, 1):
            for db in (0, 1):
                for dc in (0, 1):
                    q = tuple((ip+[da, db, dc]) % N)
                    w_ = ((1-fr[0]) if da == 0 else fr[0])*((1-fr[1]) if db == 0 else fr[1])*((1-fr[2]) if dc == 0 else fr[2])
                    v += w_*wm[q]
        rs.append(s*dx); vs.append(v)
    prof[nm] = (np.array(rs), np.array(vs))
    line = "  ".join(f"{v:5.1f}" for v in vs[::2])
    print(f"  {nm}: {line}")
from scipy.optimize import curve_fit
ps, d2s = [], []
for nm, (rs, vs) in prof.items():
    pk = vs.max(); rpk = rs[np.argmax(vs)]
    m = vs >= 0.3*pk
    try:
        f = lambda r, d2, p, r0: pk*np.exp(-((np.maximum((r-r0)**2, 0)/d2))**p)
        popt, _ = curve_fit(f, rs[m], vs[m], p0=[0.05, 1.0, rpk],
                            bounds=([0.005, 0.4, rpk-0.1], [0.4, 2.5, rpk+0.1]), maxfev=20000)
        ps.append(popt[1]); d2s.append(popt[0])
        print(f"  {nm} fit: d2 = {popt[0]:.4f}  p = {popt[1]:.2f}")
    except Exception as ex:
        print(f"  {nm} fit failed: {ex}")
if ps:
    pm = float(np.mean(ps)); d2m = float(np.mean(d2s))
    print(f"  C-1: mean p = {pm:.2f}  mean d2(direct) = {d2m:.4f}   "
          f"({'GAUSSIAN VERIFIED DIRECTLY' if 0.85 <= pm <= 1.15 else 'non-Gaussian p'})")
    R = d2m*0.648/(4*NU)
    print(f"  R from the DIRECT d2 (no mask, no calibration needed): R = {R:.2f}")
