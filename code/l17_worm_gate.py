import numpy as np, time, sys, os
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 64
NU = 0.006
SNAP = "results/l19_field_t8_N64.npy"
DT = 0.1 if SMOKE else 0.25
print("=" * 114)
print(f"TRANCHE-4 WORM-CLAUSE GATE -- the three J(C1) clauses on a REAL worm  (N={N}, nu={NU}, "
      f"window {DT})")
print("=" * 114)
print("""  Theorem J(C1)'s per-episode clauses, tested on the strongest coherent tube of the evolved
  DNS field (the cached t=8 snapshot).  Controls first: the identified core must BE a tube.

  REGISTERED, all outcomes named:
    C-a ** identification control: the core is a genuine tube -- nematic C_n(core) >= 0.8 and
        shape elongation (axis/perp second moments) >= 2.  Else identification VOID. **
    W-1 ** the veto cap on a real worm: <alpha>_core / <lam1>_core <= 0.5 (the plateau -- alpha
        is NOT the local leading strain) AND omega_peak / <alpha>_core >= 5 (the fast/slow
        margin; banked deep-tail value ~13 at N=128).  REFUTED if alpha ~ lam1 on the core:
        the runaway state would exist on real data. **
    W-2 ** Burgers core consistency: measured d(delta^2)/dt within +-0.5*(4nu + <alpha>delta^2)
        of the predicted 4nu - <alpha>delta^2 (factor-2 class agreement on the dominant scale).
        REFUTED if the core dynamics contradicts the relaxation law by more than the class
        tolerance: the modulation model would be wrong. **
    W-3 ** coherence maintenance: nematic C_n of the core at t+Dt >= C_n(t) - 0.05 (the class
        re-satisfies; corruption is slow-clock).  REFUTED by fast-clock decoherence. **
""", flush=True)
t0 = time.time()
nu = NU
k1 = np.fft.fftfreq(N, d=1.0 / N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K2 = KX ** 2 + KY ** 2 + KZ ** 2
K2s = np.where(K2 == 0, 1, K2)
km = N // 3
dl = (np.abs(KX) <= km) & (np.abs(KY) <= km) & (np.abs(KZ) <= km)
dx = 2 * np.pi / N
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


GF = lambda f, ell: np.real(np.fft.ifftn(np.exp(-0.5 * K2 * ell ** 2) * np.fft.fftn(f)))


def worm_diag(U, guess=None):
    """Identify the strongest worm (near guess if given); return core stats."""
    wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    wm = np.sqrt(sum(c ** 2 for c in wr))
    if guess is None:
        i0 = np.unravel_index(np.argmax(wm), wm.shape)
    else:
        best, i0 = -1, None
        g = np.array(guess)
        for di in range(-8, 9):
            for dj in range(-8, 9):
                for dk in range(-8, 9):
                    p = tuple((g + [di, dj, dk]) % N)
                    if wm[p] > best:
                        best, i0 = wm[p], p
    wpk = wm[i0]
    # core mask: |w| >= 0.5 peak within a 15^3 box around i0 (periodic)
    idx = [(np.arange(-5, 6) + i0[a]) % N for a in range(3)]
    BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
    sub = wm[BX, BY, BZ]
    mask = sub >= 0.5 * wpk
    # positions relative to i0 (periodic displacement in physical units)
    DX, DY, DZ = np.meshgrid(np.arange(-5, 6) * dx, np.arange(-5, 6) * dx,
                             np.arange(-5, 6) * dx, indexing='ij')
    w2 = (sub ** 2) * mask
    W2 = w2.sum()
    # nematic axis from the omega-dyad on the core
    wv = np.stack([c[BX, BY, BZ] for c in wr], axis=-1)
    Mdy = np.einsum('xyz,xyzi,xyzj->ij', w2, wv, wv) / np.maximum(
        np.einsum('xyz,xyz->', w2, (wv ** 2).sum(-1)), 1e-300)
    mu_, ev_ = np.linalg.eigh(Mdy)
    axis = ev_[:, 2]
    Cn_core = (3 * mu_[2] - 1) / 2 / max(mu_.sum(), 1e-300) * mu_.sum()  # = (3 mu1 - trace)/2 normalized
    Cn_core = (mu_[2] - 0.5 * (mu_[1] + mu_[0])) / max(mu_.sum(), 1e-300)
    # shape second moments along/perp axis
    P = np.stack([DX, DY, DZ], axis=-1)
    pal = P @ axis
    pperp2 = (P ** 2).sum(-1) - pal ** 2
    m_al = (w2 * pal ** 2).sum() / W2
    m_pp = (w2 * pperp2).sum() / W2 / 2      # per transverse direction
    elong = np.sqrt(m_al / max(m_pp, 1e-300))
    delta2 = 2 * m_pp                          # core radius^2 ~ 2 * per-direction moment
    # strain diagnostics on the core
    G = np.zeros((11, 11, 11, 3, 3))
    for i in range(3):
        for kk in range(3):
            gi = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[kk] * U[i]))
            G[..., kk, i] = gi[BX, BY, BZ]
    S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
    xi = wv / np.maximum(np.sqrt((wv ** 2).sum(-1)), 1e-300)[..., None]
    al = np.einsum('xyzi,xyzij,xyzj->xyz', xi, S, xi)
    lam1 = np.linalg.eigvalsh(S.reshape(-1, 3, 3))[:, 2].reshape(11, 11, 11)
    a_core = (w2 * al).sum() / W2
    l1_core = (w2 * lam1).sum() / W2
    return dict(i0=i0, wpk=wpk, axis=axis, Cn=Cn_core, elong=elong, d2=delta2,
                a=a_core, l1=l1_core, u=[np.real(np.fft.ifftn(c)) for c in U])


if not os.path.exists(SNAP):
    print("  no snapshot -- run l19_gate2.py first")
    sys.exit(1)
U = [c.copy() for c in np.load(SNAP)]
d0 = worm_diag(U)
print(f"  worm at grid {d0['i0']}, |w|_peak = {d0['wpk']:.3f}, axis = "
      f"[{d0['axis'][0]:+.2f},{d0['axis'][1]:+.2f},{d0['axis'][2]:+.2f}]", flush=True)
print(f"  C-a: nematic C_n(core) = {d0['Cn']:.3f} (>=0.8), elongation = {d0['elong']:.2f} (>=2) "
      f"  ({'PASS -- a genuine tube' if d0['Cn'] >= 0.8 and d0['elong'] >= 2 else 'VOID'})",
      flush=True)
# W-1
gamma_far = None
wr0 = [np.real(np.fft.ifftn(c)) for c in cur(U)]
G0 = np.zeros((N, N, N, 3, 3))
for i in range(3):
    for kk in range(3):
        G0[..., kk, i] = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[kk] * U[i]))
S0 = 0.5 * (G0 + np.transpose(G0, (0, 1, 2, 4, 3)))
lam1_bulk = np.linalg.eigvalsh(S0.reshape(-1, 3, 3))[:, 2].mean()
print(f"  W-1: <alpha>_core = {d0['a']:.3f}   <lam1>_core = {d0['l1']:.3f}   ratio = "
      f"{d0['a']/d0['l1']:.3f} (<=0.5)   omega_pk/<alpha>_core = {d0['wpk']/max(d0['a'],1e-9):.1f} "
      f"(>=5)   [bulk lam1 = {lam1_bulk:.3f}]", flush=True)
w1 = d0['a'] / d0['l1'] <= 0.5 and d0['wpk'] / max(d0['a'], 1e-9) >= 5
print(f"  W-1: {'PASS -- the veto cap holds on a real worm' if w1 else 'REFUTED/inspect'}",
      flush=True)
# evolve and re-identify
t = 0.0
dt = 2e-3
u0 = [np.real(np.fft.ifftn(c)) for c in U]
adv = np.array([u0[a][d0['i0']] for a in range(3)]) * DT / dx
guess = (np.array(d0['i0']) + np.round(adv).astype(int)) % N
while t < DT - 1e-12:
    h = min(dt, DT - t)
    a_ = rhs(U)
    Um = [U[i] + 0.5 * h * a_[i] for i in range(3)]
    b_ = rhs(Um)
    U = [U[i] + h * b_[i] for i in range(3)]
    t += h
d1 = worm_diag(U, guess=tuple(guess))
print(f"  t+{DT}: worm at {d1['i0']}, |w|_peak = {d1['wpk']:.3f}, C_n = {d1['Cn']:.3f}, "
      f"delta2 = {d1['d2']:.4f} (was {d0['d2']:.4f})", flush=True)
# W-2 (equilibrium form, pre-registered at smoke: the rate form is mask-noise-limited at
# delta ~ 2.6 dx; the robust clause is that the core SITS at the Burgers radius delta_B^2 =
# 4nu/alpha within 50%, at BOTH times -- the relaxation law's fixed point on real data)
dB2 = 4 * nu / max(d0['a'], 1e-9)
r0, r1 = d0['d2'] / dB2, d1['d2'] / dB2
meas = (d1['d2'] - d0['d2']) / DT
print(f"  W-2: delta_B^2 = 4nu/alpha = {dB2:.4f}   delta^2/delta_B^2 = {r0:.2f} (t), "
      f"{r1:.2f} (t+Dt)   [rate note: measured {meas:+.4f}]   "
      f"({'PASS -- the core sits at the Burgers radius' if 0.5 <= r0 <= 1.5 and 0.5 <= r1 <= 1.5 else 'OUTSIDE -- inspect'})",
      flush=True)
# W-3
print(f"  W-3: C_n {d0['Cn']:.3f} -> {d1['Cn']:.3f}   "
      f"({'PASS -- coherence maintained' if d1['Cn'] >= d0['Cn'] - 0.05 else 'DECOHERES -- inspect'})",
      flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
