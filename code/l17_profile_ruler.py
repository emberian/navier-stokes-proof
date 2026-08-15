import numpy as np
np.set_printoptions(suppress=True)
N0, N, NU = 64, 128, 0.006
print("PROFILE-FREE RULER -- the omega-weighted moment law is EXACT for ANY profile")
print("""  DESK (exact, any axisymmetric profile, uniform axial strain): d(m2)/dt = 4nu - alpha*m2
  with m2 = omega-WEIGHTED transverse second moment; equilibrium m2 = 4nu/alpha, profile-free.
  The previous ruler's omega^2 weighting was the profile-dependent step.  REGISTERED:
    P-1 ** m2 vs mask threshold {0.5, 0.25, 0.125}x peak converges (extrapolation spread
        <= 15%) -- truncation removed. **
    P-2 ** R_m = m2_extrap * alpha_w / (4nu): EXACT-STANDARD |R_m - 1| <= 0.35 -- W-2 exact,
        profile-free.  Else: the core is genuinely off-equilibrium; the dynamic m2-budget is
        the registered follow-on. **
    P-3 ** the profile question answered directly: flatness F4 = <r^4>/<r^2>^2 (omega-weighted,
        Gaussian = 2.0) -- reported with the verdict. **""")
U64 = np.load("results/l19_field_t8_N64.npy")
k1 = np.fft.fftfreq(N, d=1.0/N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
def up(u):
    out = np.zeros((N, N, N), complex); h = N0//2
    ix = np.r_[0:h, N-h:N]; src = np.r_[0:h, N0-h:N0]
    out[np.ix_(ix, ix, ix)] = u[np.ix_(src, src, src)]
    return out*(N/N0)**3
U = [up(c) for c in U64]
cur = lambda V: [1j*(KY*V[2]-KZ*V[1]), 1j*(KZ*V[0]-KX*V[2]), 1j*(KX*V[1]-KY*V[0])]
wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
wm = np.sqrt(sum(c**2 for c in wr))
i0 = (80, 93, 104)
dx = 2*np.pi/N
BOX = 12
idx = [(np.arange(-BOX, BOX+1)+i0[a]) % N for a in range(3)]
BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
sub = wm[BX, BY, BZ]; wpk = sub.max()
ar = np.arange(-BOX, BOX+1)*dx
DX, DY, DZ = np.meshgrid(ar, ar, ar, indexing='ij')
P = np.stack([DX, DY, DZ], axis=-1)
# axis from the omega^2-shape tensor at the tightest mask (robust), then omega-WEIGHTED moments
m0 = sub >= 0.5*wpk
w2s = (sub**2)*m0
Msh = np.einsum('xyz,xyzi,xyzj->ij', w2s, P, P)/w2s.sum()
axis = np.linalg.eigh(Msh)[1][:, 2]
pal = P @ axis
pperp2 = (P**2).sum(-1) - pal**2
# alpha, omega-weighted on the 0.5 core (consistent weight)
G = np.zeros((2*BOX+1,)*3 + (3, 3))
for i in range(3):
    for kk in range(3):
        gi = np.real(np.fft.ifftn(1j*(KX, KY, KZ)[kk]*U[i]))
        G[..., kk, i] = gi[BX, BY, BZ]
S = 0.5*(G+np.transpose(G, (0, 1, 2, 4, 3)))
wv = np.stack([c[BX, BY, BZ] for c in wr], axis=-1)
xi = wv/np.maximum(np.sqrt((wv**2).sum(-1)), 1e-300)[..., None]
alf = np.einsum('xyzi,xyzij,xyzj->xyz', xi, S, xi)
aw = (sub*m0*alf).sum()/(sub*m0).sum()
print(f"  omega-weighted core alpha = {aw:.3f}")
m2s = []
for thr in (0.5, 0.25, 0.125):
    mk = sub >= thr*wpk
    w1 = sub*mk
    m2 = (w1*pperp2).sum()/w1.sum()
    m2s.append(m2)
    print(f"  mask {thr:>5}: m2 = {m2:.4f}   cells = {int(mk.sum())}")
# linear extrapolation in threshold -> 0
m2x = np.polyfit([0.5, 0.25, 0.125], m2s, 1)
m2_0 = np.polyval(m2x, 0.0)
spread = abs(m2s[-1]-m2_0)/m2_0
print(f"  P-1: m2 extrapolated to zero threshold = {m2_0:.4f} (last-point gap {100*spread:.1f}%)   "
      f"({'PASS' if spread <= 0.15 else 'not converged -- report'})")
Rm = m2_0*aw/(4*NU)
print(f"  P-2: R_m = {Rm:.2f}   "
      f"({'EXACT-STANDARD PASS -- W-2 exact, profile-free' if abs(Rm-1) <= 0.35 else 'off-equilibrium/inspect -- dynamic m2-budget is the follow-on'})")
mk = sub >= 0.125*wpk
w1 = sub*mk
r4 = (w1*pperp2**2).sum()/w1.sum()
F4 = r4/((w1*pperp2).sum()/w1.sum())**2
print(f"  P-3: flatness F4 = {F4:.2f} (Gaussian = 2.0)   verdict: "
      f"{'consistent with Gaussian' if abs(F4-2) <= 0.4 else ('FLATTER than Gaussian (top-hat-ish)' if F4 < 2 else 'HEAVIER-TAILED than Gaussian')}")
