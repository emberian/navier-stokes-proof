import numpy as np, time, sys
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 32 if SMOKE else 64
NU = 0.006
TIMES = [0.5] if SMOKE else [2.0, 4.0, 8.0]
print("=" * 118)
print(f"LEMMA 19 GATE -- does production ride COHERENCE, and is the coherent fixed point the "
      f"VETO point (e2), not e1?   (N={N}, nu={NU})")
print("=" * 118)
print("""  LEMMA 19 (classification): production-carrying organization at high intensity is tube-class.
  Desk engine (exact): D_t omega = S omega (W omega = 0), so xi flows PROJECTIVELY under S ->
  alignment with e1 at rate lam1-lam2 (production self-maximizing, the w'~w^2 caricature).  What
  stops it: the eigenframe at intense points is SLAVED to the local omega-arrangement (self-strain
  dominates, |S_far| <= C r^-3/2 ||omega||_2), and for a COHERENT arrangement the self-strain has
  xi as an exact NULL eigenvector (the veto, Lemma 3 / sec 120).  So e1-alignment is
  self-destroying: aligning parallelizes, parallelizing activates the veto, the veto demotes xi's
  eigenvalue to gamma_far -- the middle of the (+c.omega, gamma_far, -c.omega) sandwich.  The only
  self-consistent persistent alignment at high intensity is xi = e2 with alpha = gamma_far: the
  TUBE CLASS.  Tangles cannot persist (they parallelize on their own production clock); e1-locked
  runaway cannot persist (frame slaving).  This gate tests the mechanism per-flow.

  INSTRUMENT: coherence C(x) = |G_ell * omega| / (G_ell * |omega|) in [0,1] -- local vorticity
  polarization at core scale ell (1 = locally parallel, small = direction-tangled).  The
  phase-randomized control has the SAME spectrum, so any C-difference and any C-production
  correlation is pure phase organization.

  REGISTERED, all outcomes named, controls first:
    V-0a ** instrument validation: straight-tube forest (axis-aligned, random positions) must give
         omega-weighted <C> > 0.95 on its support; the instrument sees parallel structure. **
    V-0b ** evolved vs phase-randomized: in the top-|omega| decile the evolved C-distribution must
         sit ABOVE the randomized one (worms more coherent than the Gaussian baseline with the
         identical spectrum).  No separation => instrument void, gates do not proceed. **
    G19-1 ** production rides coherence: binning the top decile by C, the per-unit-enstrophy
         normalized production must be positive and increasing with C, and ~0 (|.| small) in the
         low-C (tangle) bins.  REFUTED if a low-C bin carries O(1) production share at high rate:
         a producing tangle. **
    G19-2 ** the fixed point is the veto point: in the high-C intense bins, |xi.e2| dominates
         (>= ~0.7) and alpha/lam1 stays at or below the known plateau ~0.5 in EVERY bin.
         REFUTED if high-C bins are e1-dominated or alpha/lam1 -> 1 anywhere: the frozen-frame
         attractor would be winning and production would run at the uncapped rate. **
    G19-3 ** control: the phase-randomized field must show per-unit production ~0 in ALL C-bins
         (no organization, no production -- Lemma 18a localized).  Dirty control => gates void. **
""", flush=True)
t0 = time.time()
nu = NU
k1 = np.fft.fftfreq(N, d=1.0 / N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K2 = KX ** 2 + KY ** 2 + KZ ** 2
K2s = np.where(K2 == 0, 1, K2)
K = np.sqrt(K2)
km = N // 3
dl = (np.abs(KX) <= km) & (np.abs(KY) <= km) & (np.abs(KZ) <= km)
dx = 2 * np.pi / N
cur = lambda U: [1j * (KY * U[2] - KZ * U[1]), 1j * (KZ * U[0] - KX * U[2]),
                 1j * (KX * U[1] - KY * U[0])]


def proj(U):
    d = (KX * U[0] + KY * U[1] + KZ * U[2]) / K2s
    return [U[i] - Kc * d for i, Kc in enumerate((KX, KY, KZ))]


# ---- identical banked IC: seed 5, band-limited k<=3, u_rms = 1 (depletion2/3, org_production) ----
rng = np.random.default_rng(5)
U = proj([np.fft.fftn(c) for c in [rng.normal(size=(N,) * 3) for _ in range(3)]])
U = [c * np.where((K > 0) & (K <= 3), K ** -1.0, 0.0) for c in U]
urms = np.sqrt(np.mean(sum(np.real(np.fft.ifftn(c)) ** 2 for c in U)))
U = [c / urms for c in U]
print(f"  setup: N={N}, nu={nu}, u_rms=1, IC = banked seed-5 band-limited field, "
      f"Re ~ {2*np.pi/nu:.0f}", flush=True)


def rhs(U):
    u = [np.real(np.fft.ifftn(c)) for c in U]
    w = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    cr = [u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0]]
    return [f - nu * K2 * U[i] for i, f in enumerate(proj([np.fft.fftn(c) * dl for c in cr]))]


# ---- the coherence instrument ----
def coherence(wr, ell):
    """C = |G_ell * omega| / (G_ell * |omega|), Gaussian filter width ell (physical units)."""
    g = np.exp(-0.5 * K2 * ell ** 2)
    wm = np.sqrt(sum(c ** 2 for c in wr))
    num = np.sqrt(sum(np.real(np.fft.ifftn(g * np.fft.fftn(c))) ** 2 for c in wr))
    den = np.real(np.fft.ifftn(g * np.fft.fftn(wm)))
    return num / np.maximum(den, 1e-14), wm


# ---- V-0a: forest validation (static, kinematic) ----
x1 = np.arange(N) * dx
X, Y, Z = np.meshgrid(x1, x1, x1, indexing='ij')
def pd2(a, b):  # periodic squared distance of coordinate arrays
    d = np.abs(a - b)
    return np.minimum(d, 2 * np.pi - d) ** 2
rngf = np.random.default_rng(7)
sig = 0.3
wf = [np.zeros((N,) * 3) for _ in range(3)]
for ax in [0, 0, 0, 1, 1, 2]:                     # 3 x-tubes, 2 y-tubes, 1 z-tube
    c1, c2 = rngf.uniform(0, 2 * np.pi, 2)
    if ax == 0:
        r2 = pd2(Y, c1) + pd2(Z, c2)
    elif ax == 1:
        r2 = pd2(X, c1) + pd2(Z, c2)
    else:
        r2 = pd2(X, c1) + pd2(Y, c2)
    wf[ax] += np.exp(-r2 / (2 * sig ** 2))
Cf, wmf = coherence(wf, 2 * dx)
mf = wmf > 0.3 * wmf.max()
v0a = (Cf * wmf ** 2)[mf].sum() / (wmf ** 2)[mf].sum()
print(f"  V-0a forest: omega^2-weighted <C> on support = {v0a:.4f}   "
      f"({'PASS (>0.95)' if v0a > 0.95 else 'FAIL -- instrument void'})\n", flush=True)

CBINS = [(0.0, 0.5), (0.5, 0.7), (0.7, 0.85), (0.85, 0.95), (0.95, 1.0)]


def table(wr, U, label):
    """The gate table: top-|omega| decile binned by coherence C (ell = 2 dx)."""
    C, wm = coherence(wr, 2 * dx)
    G = np.zeros((N, N, N, 3, 3))
    for i in range(3):
        for k in range(3):
            G[..., k, i] = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[k] * U[i]))
    S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
    Sf = S.reshape(-1, 3, 3)
    ev, evec = np.linalg.eigh(Sf)
    ev = ev[:, ::-1]
    evec = evec[:, :, ::-1]                        # lam1 >= lam2 >= lam3
    wv = np.stack(wr, axis=-1).reshape(-1, 3)
    wmf_ = wm.ravel()
    xf = wv / np.maximum(wmf_, 1e-300)[:, None]
    al = np.einsum('ni,nij,nj->n', xf, Sf, xf)
    cs = np.abs(np.einsum('ni,nij->nj', xf, evec))
    Cr = C.ravel()
    s2m = np.sqrt(np.einsum('nij,nji->n', Sf, Sf).mean())     # global (trS^2)^1/2 yardstick
    Ptot = (wmf_ ** 2 * al).sum()
    hi = wmf_ >= np.quantile(wmf_, 0.90)
    Phi = (wmf_[hi] ** 2 * al[hi]).sum()
    pwC = (wmf_ ** 2 * al * Cr).sum() / Ptot if Ptot != 0 else np.nan
    ewC = (wmf_[hi] ** 2 * Cr[hi]).sum() / (wmf_[hi] ** 2).sum()
    print(f"  [{label}]  P_tot = {Ptot/ (len(wmf_)*s2m**3):+.5f} (normalized)   "
          f"top-decile share of P = {Phi/Ptot if Ptot!=0 else np.nan:.3f}   "
          f"production-weighted <C> = {pwC:.4f}  vs  enstrophy-weighted <C> (hi) = {ewC:.4f}",
          flush=True)
    print(f"{'C bin':>12}{'pop %':>8}{'ens %':>8}{'P share':>9}{'per-unit P':>12}{'a/l1':>8}"
          f"{'|xi.e1|':>9}{'|xi.e2|':>9}{'|xi.e3|':>9}", flush=True)
    rows = []
    for lo, hic in CBINS:
        m = hi & (Cr >= lo) & (Cr < hic if hic < 1.0 else Cr <= 1.0)
        if m.sum() < 8:
            print(f"{f'{lo:.2f}-{hic:.2f}':>12}{100*m.sum()/hi.sum():>8.2f}   (empty)", flush=True)
            continue
        ens = (wmf_[m] ** 2).sum() / (wmf_[hi] ** 2).sum()
        Psh = (wmf_[m] ** 2 * al[m]).sum() / Ptot if Ptot != 0 else np.nan
        pu = ((wmf_[m] ** 2 * al[m]).sum() / (wmf_[m] ** 2).sum()) / s2m
        rat = (al[m] / np.maximum(ev[m, 0], 1e-14)).mean()
        e1, e2, e3 = cs[m, 0].mean(), cs[m, 1].mean(), cs[m, 2].mean()
        rows.append(dict(lo=lo, hi=hic, pu=pu, rat=rat, e1=e1, e2=e2, e3=e3, Psh=Psh,
                         pop=m.sum() / hi.sum()))
        print(f"{f'{lo:.2f}-{hic:.2f}':>12}{100*m.sum()/hi.sum():>8.2f}{100*ens:>8.2f}"
              f"{Psh:>9.3f}{pu:>12.5f}{rat:>8.3f}{e1:>9.4f}{e2:>9.4f}{e3:>9.4f}", flush=True)
    return rows, pwC, ewC


# ---- evolve, diagnose at TIMES ----
t = 0.0
dt = 2e-3
for tv in TIMES:
    while t < tv - 1e-12:
        h = min(dt, tv - t)
        a = rhs(U)
        Um = [U[i] + 0.5 * h * a[i] for i in range(3)]
        b = rhs(Um)
        U = [U[i] + h * b[i] for i in range(3)]
        t += h
    wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    print(f"\n  t = {t:.1f}   max|w| = {np.sqrt(sum(c**2 for c in wr)).max():.3f}", flush=True)
    rows, pwC, ewC = table(wr, U, f"evolved t={t:.0f}")

# robustness: ell = 4 dx at final time
print(f"\n  robustness ell = 4 dx (final time):", flush=True)


def table_ell(wr, U, ell, label):
    C, wm = coherence(wr, ell)
    wmf_ = wm.ravel()
    Cr = C.ravel()
    hi = wmf_ >= np.quantile(wmf_, 0.90)
    G = np.zeros((N, N, N, 3, 3))
    for i in range(3):
        for k in range(3):
            G[..., k, i] = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[k] * U[i]))
    S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
    Sf = S.reshape(-1, 3, 3)
    wv = np.stack(wr, axis=-1).reshape(-1, 3)
    xf = wv / np.maximum(wmf_, 1e-300)[:, None]
    al = np.einsum('ni,nij,nj->n', xf, Sf, xf)
    s2m = np.sqrt(np.einsum('nij,nji->n', Sf, Sf).mean())
    Ptot = (wmf_ ** 2 * al).sum()
    print(f"  [{label}] per-unit P by C bin:", end="", flush=True)
    for lo, hic in CBINS:
        m = hi & (Cr >= lo) & (Cr < hic if hic < 1.0 else Cr <= 1.0)
        if m.sum() < 8:
            print(f"   {lo:.2f}-{hic:.2f}: --", end="")
            continue
        pu = ((wmf_[m] ** 2 * al[m]).sum() / (wmf_[m] ** 2).sum()) / s2m
        print(f"   {lo:.2f}-{hic:.2f}: {pu:+.4f}", end="")
    print(flush=True)


table_ell(wr, U, 4 * dx, "evolved ell=4dx")

# ---- V-0b + G19-3: phase-randomized control (spectrum identical, org_production's map) ----
print(f"\n  control: phase-randomized field (same spectrum as evolved t={t:.0f}):", flush=True)
phi = rng.uniform(0, 2 * np.pi, size=(N, N, N))
I = np.arange(N)
negidx = lambda a: (-a) % N
phin = phi[np.ix_(negidx(I), negidx(I), negidx(I))]
phia = (phi - phin) / 2
Urand = [c * np.exp(1j * phia) for c in U]
wrr = [np.real(np.fft.ifftn(c)) for c in cur(Urand)]
Ce, wme = coherence(wr, 2 * dx)
Crnd, wmr = coherence(wrr, 2 * dx)
he = wme >= np.quantile(wme, 0.90)
hr = wmr >= np.quantile(wmr, 0.90)
me_, md_ = (Ce[he] * wme[he] ** 2).sum() / (wme[he] ** 2).sum(), np.median(Ce[he])
mr_, mdr = (Crnd[hr] * wmr[hr] ** 2).sum() / (wmr[hr] ** 2).sum(), np.median(Crnd[hr])
print(f"  V-0b top-decile coherence:  evolved <C> = {me_:.4f} (median {md_:.4f})   "
      f"randomized <C> = {mr_:.4f} (median {mdr:.4f})   "
      f"({'PASS -- evolved above baseline' if me_ > mr_ + 0.02 else 'NO SEPARATION -- instrument void'})",
      flush=True)
rows_r, pwCr, ewCr = table(wrr, Urand, "randomized")
print(f"""
  READ-OFF:
    G19-1: per-unit P positive & rising with C in evolved bins; ~0 in low-C bins => production
           rides coherence.  A low-C bin with large P share at high rate would REFUTE.
    G19-2: high-C bins e2-dominant with a/l1 <= ~0.5 everywhere => the veto fixed point, capped.
           e1-dominance or a/l1 -> 1 would REFUTE (frozen-frame runaway).
    G19-3: randomized per-unit P ~ 0 in all bins => the correlation is organization, not artifact.
  total {time.time()-t0:.0f}s""", flush=True)
