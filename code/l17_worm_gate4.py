import numpy as np, sys, time
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N0, N = 64, (64 if SMOKE else 128)
NU = 0.006
SNAP = "results/l19_field_t8_N64.npy"
TS = [0.0, 0.1, 0.2] if SMOKE else [0.0, 0.1, 0.2, 0.3, 0.4]
I0_64 = (40, 47, 52)                       # the sec-175 worm, position-locked
print("=" * 114)
print(f"WORM GATE 4 -- EXACTNESS REDO ITEM 1: the Burgers LAW in budget form on the TRACKED "
      f"worm (N={N}, snapshots {TS})")
print("=" * 114)
print("""  The exact form of W-2 is the law itself, all terms measured, one exact prediction:
      E := (d(delta^2)/dt + alpha * delta^2) / (4 nu) = 1
  -- valid on AND off equilibrium (what J(C1)'s modulation system consumes).  Identity is
  POSITION-LOCKED: start from the sec-175 worm's coordinates, advect the tracking point with
  the local velocity between snapshots, identify by local max in a +-6 cell ball.  delta^2 via
  the N=128-calibrated estimator (gate 3: est = 0.269 d2 + 0.00055, curve residuals <= 5.3%).

  REGISTERED, outcomes named:
    Z-0 ** tracking lock: peak within 5 cells of the advected guess each window AND peak value
        continuous (+-20%) -- the SAME worm, certified.  Else identity lost -> void. **
    Z-1 ** context: calibrated equilibrium ratio R = delta^2 alpha/(4nu) per snapshot. **
    Z-2 ** THE EXACT TEST: per-interval budget E = (Ddelta^2/Dt + abar*d2bar)/(4nu); median
        over intervals in [0.65, 1.35].  PASS = the Burgers law measured exactly on a tracked
        real worm.  Named alternative: E ~ 1 with R stably > 1.35 = the worm OBEYS the law
        while off-equilibrium (fat core, contracting) -- recorded as the exact result (the law,
        not the fixed point, is what the theorem uses). **
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
    out = np.zeros((N, N, N), complex)
    h = N0 // 2
    ix = np.r_[0:h, N - h:N]
    src = np.r_[0:h, N0 - h:N0]
    out[np.ix_(ix, ix, ix)] = u64[np.ix_(src, src, src)]
    return out * (N / N0) ** 3


BOX = 10 if N == 128 else 5
CGRID = 0.00055 if N == 128 else 0.0006


def diag_at(U, guess):
    wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    wm = np.sqrt(sum(c ** 2 for c in wr))
    g = np.array(guess)
    best, i0 = -1, None
    for di in range(-6, 7):
        for dj in range(-6, 7):
            for dk in range(-6, 7):
                p = tuple((g + [di, dj, dk]) % N)
                if wm[p] > best:
                    best, i0 = wm[p], p
    dist = np.linalg.norm((np.array(i0) - g + N // 2) % N - N // 2)
    idx = [(np.arange(-BOX, BOX + 1) + i0[a]) % N for a in range(3)]
    BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
    sub = wm[BX, BY, BZ]
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
    raw = (w2 * ((P ** 2).sum(-1) - pal ** 2)).sum() / W2
    d2 = (raw - CGRID) / 0.269
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
    a_core = (w2 * al).sum() / W2
    uvel = [np.real(np.fft.ifftn(c)) for c in U]
    uloc = np.array([uvel[a][i0] for a in range(3)])
    return dict(i0=i0, wpk=wpk, d2=d2, a=a_core, u=uloc, dist=dist)


U64 = np.load(SNAP)
U = [upsample(c) for c in U64] if N != N0 else [c.copy() for c in U64]
guess = tuple(int(v * N / N0) for v in I0_64)
snaps = []
t = 0.0
dt = 1e-3 if N == 128 else 2e-3
for tv in TS:
    while t < tv - 1e-12:
        h = min(dt, tv - t)
        a_ = rhs(U)
        Um = [U[i] + 0.5 * h * a_[i] for i in range(3)]
        b_ = rhs(Um)
        U = [U[i] + h * b_[i] for i in range(3)]
        t += h
    d = diag_at(U, guess)
    snaps.append((tv, d))
    R = d['d2'] * d['a'] / (4 * nu)
    print(f"  t' = {tv:.2f}: worm {d['i0']} (drift {d['dist']:.1f} cells)  |w|_pk = "
          f"{d['wpk']:.2f}  d2 = {d['d2']:.4f}  alpha = {d['a']:.3f}  Z-1 R = {R:.2f}",
          flush=True)
    guess = tuple((np.array(d['i0']) + np.round(d['u'] * ((TS[min(len(snaps), len(TS)-1)] -
                   tv) if tv != TS[-1] else 0) / dx).astype(int)) % N)
# Z-0
locks = all(d['dist'] <= 5 for _, d in snaps[1:])
pks = [d['wpk'] for _, d in snaps]
cont = all(abs(pks[i + 1] - pks[i]) / pks[i] <= 0.2 for i in range(len(pks) - 1))
print(f"\n  Z-0 tracking: drifts OK = {locks}, peak continuity OK = {cont}   "
      f"({'PASS -- same worm' if locks and cont else 'IDENTITY LOST -- void'})", flush=True)
# Z-2
Es = []
for i in range(len(snaps) - 1):
    (ta, da), (tb, db) = snaps[i], snaps[i + 1]
    dd2dt = (db['d2'] - da['d2']) / (tb - ta)
    abar = 0.5 * (da['a'] + db['a'])
    d2bar = 0.5 * (da['d2'] + db['d2'])
    E = (dd2dt + abar * d2bar) / (4 * nu)
    Es.append(E)
    print(f"  interval {ta:.2f}-{tb:.2f}: d(d2)/dt = {dd2dt:+.4f}   alpha*d2 = "
          f"{abar*d2bar:.4f}   E = {E:.2f}", flush=True)
Em = float(np.median(Es))
print(f"\n  Z-2 THE EXACT TEST: median budget E = {Em:.2f}   "
      f"({'PASS -- the Burgers law measured exactly on the tracked worm' if 0.65 <= Em <= 1.35 else 'OUTSIDE -- report honestly'})",
      flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
