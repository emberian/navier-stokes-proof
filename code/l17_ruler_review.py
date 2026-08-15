import numpy as np
np.set_printoptions(suppress=True)
N0, N, NU = 64, 128, 0.006
print("RULER REVIEW (Jeff's directive) -- correct truncated references, contamination-resistant")
print("""  DESK (exact, computed fresh): a TRUE Gaussian profile measured under our masks gives
    F4(omega^2-weight, 0.5-mask)   = 0.1085/0.269^2      = 1.499   (NOT 2.0 -- the 2.0
        reference in sec-178's P-3 was the UNtruncated value: reasoning error, corrected)
    moment-ratio <r2>(0.5)/<r2>(0.25) (omega^2 weights)  = 0.269/0.407 = 0.661
  REGISTERED: V-1 both worm statistics within 12% of the truncated-Gaussian references ->
  Gaussian verified WITH THE RIGHT REFERENCES (calibration stands, R = 1.85 stands).  Else:
  fit generalized-Gaussian exp(-(r2/d2)^p), recompute the calibration factor for fitted p,
  restate R.  V-2 strain-split self-consistency: alpha from BS(full omega) = alpha from U
  directly, to < 1% (the split ruler exact).""")
U64 = np.load("results/l19_field_t8_N64.npy")
k1 = np.fft.fftfreq(N, d=1.0/N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K2 = KX**2 + KY**2 + KZ**2
K2s = np.where(K2 == 0, 1, K2)
def up(u):
    out = np.zeros((N, N, N), complex); h = N0//2
    ix = np.r_[0:h, N-h:N]; src = np.r_[0:h, N0-h:N0]
    out[np.ix_(ix, ix, ix)] = u[np.ix_(src, src, src)]
    return out*(N/N0)**3
U = [up(c) for c in U64]
cur = lambda V: [1j*(KY*V[2]-KZ*V[1]), 1j*(KZ*V[0]-KX*V[2]), 1j*(KX*V[1]-KY*V[0])]
Wh = cur(U)
wr = [np.real(np.fft.ifftn(c)) for c in Wh]
wm = np.sqrt(sum(c**2 for c in wr))
i0 = (80, 93, 104); dx = 2*np.pi/N; BOX = 12
idx = [(np.arange(-BOX, BOX+1)+i0[a]) % N for a in range(3)]
BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
sub = wm[BX, BY, BZ]; wpk = sub.max()
ar = np.arange(-BOX, BOX+1)*dx
DX, DY, DZ = np.meshgrid(ar, ar, ar, indexing='ij')
P = np.stack([DX, DY, DZ], axis=-1)
m5 = sub >= 0.5*wpk
w2s = (sub**2)*m5
axis = np.linalg.eigh(np.einsum('xyz,xyzi,xyzj->ij', w2s, P, P)/w2s.sum())[1][:, 2]
pperp2 = (P**2).sum(-1) - (P @ axis)**2
def mom(thr, k):
    mk = sub >= thr*wpk
    w = (sub**2)*mk
    return (w*pperp2**k).sum()/w.sum()
r2_5, r2_25 = mom(0.5, 1), mom(0.25, 1)
F4m = mom(0.5, 2)/r2_5**2
ratm = r2_5/r2_25
print(f"  V-1 worm: F4(w2,.5) = {F4m:.3f} (Gauss-trunc ref 1.499)   ratio = {ratm:.3f} "
      f"(ref 0.661)")
ok1 = abs(F4m-1.499)/1.499 <= 0.12 and abs(ratm-0.661)/0.661 <= 0.12
print(f"  V-1: {'PASS -- Gaussian verified with correct references' if ok1 else 'DEVIATES -- generalized-Gaussian refit below'}")
if not ok1:
    from scipy.integrate import quad
    best = None
    for p in np.linspace(0.5, 2.5, 41):
        f0 = quad(lambda u: np.exp(-2*u**p), 0, (np.log(2))**(1/p))[0]
        f1 = quad(lambda u: u*np.exp(-2*u**p), 0, (np.log(2))**(1/p))[0]
        f1b = quad(lambda u: u*np.exp(-2*u**p), 0, (np.log(4))**(1/p))[0]
        f0b = quad(lambda u: np.exp(-2*u**p), 0, (np.log(4))**(1/p))[0]
        rat_p = (f1/f0)/(f1b/f0b)
        if best is None or abs(rat_p-ratm) < abs(best[1]-ratm):
            best = (p, rat_p, f1/f0)
    p, ratp, c5 = best
    print(f"  refit: p = {p:.2f} (Gaussian p=1) reproduces ratio {ratp:.3f}; calibration "
          f"factor at 0.5-mask = {c5:.3f} (Gaussian 0.269)")
    d2_new = (0.0734*0.269)/c5   # rescale the tracked delta^2 by the corrected factor
    Rnew = d2_new*0.648/(4*NU)
    print(f"  restated: delta^2 = {d2_new:.4f} -> R = {Rnew:.2f} (was 1.85 under Gaussian)")
# V-2
Ubs = [1j*(KY*Wh[2]-KZ*Wh[1])/K2s, 1j*(KZ*Wh[0]-KX*Wh[2])/K2s, 1j*(KX*Wh[1]-KY*Wh[0])/K2s]
def alpha_of(V):
    G = np.zeros((2*BOX+1,)*3+(3, 3))
    for i in range(3):
        for kk in range(3):
            G[..., kk, i] = np.real(np.fft.ifftn(1j*(KX, KY, KZ)[kk]*V[i]))[BX, BY, BZ]
    S = 0.5*(G+np.transpose(G, (0, 1, 2, 4, 3)))
    wv = np.stack([c[BX, BY, BZ] for c in wr], axis=-1)
    xi = wv/np.maximum(np.sqrt((wv**2).sum(-1)), 1e-300)[..., None]
    a = np.einsum('xyzi,xyzij,xyzj->xyz', xi, S, xi)
    return (w2s*a).sum()/w2s.sum()
aU, aBS = alpha_of(U), alpha_of(Ubs)
print(f"  V-2 alpha direct = {aU:.4f}  via BS(full omega) = {aBS:.4f}  diff = "
      f"{100*abs(aU-aBS)/aU:.2f}%   ({'PASS -- split ruler exact' if abs(aU-aBS)/aU < 0.01 else 'FAIL'})")
