import numpy as np, time, sys, os
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 32 if SMOKE else 64
NU = 0.006
T = 0.5 if SMOKE else 8.0
SNAP = f"results/l19_field_t8_N{N}.npy"
print("=" * 118)
print(f"LEMMA 19 GATE 2 -- the NEMATIC discriminator: true tangles vs antiparallel organization   "
      f"(N={N}, nu={NU}, t={T})")
print("=" * 118)
print("""  Gate 1's finding: polarization coherence C = |G*omega|/(G*|omega|) is SPECTRUM-DETERMINED
  (V-0b: evolved 0.706 vs randomized 0.715 -- no separation) and conflates direction-TANGLED
  regions with antiparallel-ORGANIZED ones (the financing zones): its low-C bins read
  |xi.e2| = 0.76-0.89 -- maximally aligned, not tangled.  The correct discriminator for the
  classification's dichotomy (coherent-class vs tangle) must be SIGN-BLIND:

  NEMATIC coherence: M(x) = G_ell * (omega x omega)  (filtered dyad, PSD), eigenvalues
  mu1 >= mu2 >= mu3, C_n = (mu1 - (mu2+mu3)/2)/tr(M) in [0,1].  C_n = 1 for a locally parallel
  OR antiparallel line field; C_n small for direction chaos.  The tangle's independent signature
  (Lemma 18 mechanism, measured in gate 1's control): ISOTROPIC alignment moments ~(.5,.5,.5).

  REGISTERED, all outcomes named, controls first:
    V2-0a ** discriminator validation: an ANTIPARALLEL tube pair must give omega^2-weighted
          <C_n> > 0.95 on support while the polar C drops in the interaction zone; and the
          crossing-forest C_n stays high on isolated support. **
    V2-0b ** evolved vs phase-randomized top-decile C_n: evolved must sit ABOVE the randomized
          baseline (nematic order is phase-borne, unlike polarization).  If no separation,
          report honestly and classify by the alignment-signature instead. **
    G19-1' ** the dichotomy per-flow: binning the top decile by C_n -- low-C_n bins (true tangle
          candidates) must be (i) small population in the evolved flow, (ii) isotropic-signature
          if present, (iii) per-unit production ~ 0.  Production must be carried by high-C_n
          (organized) bins at the CAPPED rate.  REFUTED if a low-C_n bin with isotropic moments
          carries O(1) production share at high rate: a producing tangle. **
    G19-2' ** the fixed point: e2-dominance and a/l1 <= ~0.5 in every populated evolved bin
          (no frozen-frame runaway anywhere).  REFUTED by e1-dominance or a/l1 -> 1. **
    G19-3' ** control: randomized field -- per-unit production ~ 0 in ALL C_n bins, isotropic
          moments everywhere.  Dirty control => gates void. **
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


def rhs(U):
    u = [np.real(np.fft.ifftn(c)) for c in U]
    w = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    cr = [u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0]]
    return [f - nu * K2 * U[i] for i, f in enumerate(proj([np.fft.fftn(c) * dl for c in cr]))]


GF = lambda f, ell: np.real(np.fft.ifftn(np.exp(-0.5 * K2 * ell ** 2) * np.fft.fftn(f)))


def nematic(wr, ell):
    """C_n from the filtered dyad M = G_ell*(w x w); also polar C for comparison."""
    Mf = np.zeros((N, N, N, 3, 3))
    for i in range(3):
        for j in range(i, 3):
            Mf[..., i, j] = Mf[..., j, i] = GF(wr[i] * wr[j], ell)
    mu = np.linalg.eigvalsh(Mf.reshape(-1, 3, 3))[:, ::-1]
    tr = np.maximum(mu.sum(1), 1e-14)
    Cn = ((mu[:, 0] - 0.5 * (mu[:, 1] + mu[:, 2])) / tr).reshape(N, N, N)
    wm = np.sqrt(sum(c ** 2 for c in wr))
    num = np.sqrt(sum(GF(c, ell) ** 2 for c in wr))
    Cp = num / np.maximum(GF(wm, ell), 1e-14)
    return Cn, Cp, wm


# ---- V2-0a: antiparallel pair + crossing forest ----
x1 = np.arange(N) * dx
X, Y, Z = np.meshgrid(x1, x1, x1, indexing='ij')
pd2 = lambda a, b: np.minimum(np.abs(a - b), 2 * np.pi - np.abs(a - b)) ** 2
sig = 0.3
d0 = 3 * sig
wp = [np.zeros((N,) * 3) for _ in range(3)]
wp[2] = (np.exp(-(pd2(X, np.pi - d0 / 2) + pd2(Y, np.pi)) / (2 * sig ** 2))
         - np.exp(-(pd2(X, np.pi + d0 / 2) + pd2(Y, np.pi)) / (2 * sig ** 2)))
Cn_p, Cp_p, wm_p = nematic(wp, 2 * dx)
sup = wm_p > 0.3 * wm_p.max()
mid = (np.abs(X - np.pi) < d0 / 2) & (pd2(Y, np.pi) < sig ** 2) & sup
v2n = (Cn_p * wm_p ** 2)[sup].sum() / (wm_p ** 2)[sup].sum()
v2p = Cp_p[mid].mean() if mid.sum() > 0 else np.nan
print(f"  V2-0a antiparallel pair: <C_n> on support = {v2n:.4f}  (polar C in interaction zone = "
      f"{v2p:.4f})   ({'PASS' if v2n > 0.95 else 'FAIL -- discriminator void'})", flush=True)
rngf = np.random.default_rng(7)
wf = [np.zeros((N,) * 3) for _ in range(3)]
for ax in [0, 0, 0, 1, 1, 2]:
    c1, c2 = rngf.uniform(0, 2 * np.pi, 2)
    r2 = (pd2(Y, c1) + pd2(Z, c2)) if ax == 0 else (pd2(X, c1) + pd2(Z, c2)) if ax == 1 \
        else (pd2(X, c1) + pd2(Y, c2))
    wf[ax] += np.exp(-r2 / (2 * sig ** 2)) * rngf.choice([-1, 1])
Cn_f, _, wm_f = nematic(wf, 2 * dx)
supf = wm_f > 0.3 * wm_f.max()
v2f = (Cn_f * wm_f ** 2)[supf].sum() / (wm_f ** 2)[supf].sum()
print(f"  V2-0a signed crossing forest: <C_n> on support = {v2f:.4f}   "
      f"({'PASS (>0.9)' if v2f > 0.9 else 'note: crossings depress -- inspect'})\n", flush=True)

# ---- evolved field: load snapshot if present, else evolve and save ----
if os.path.exists(SNAP):
    U = [c.copy() for c in np.load(SNAP)]
    print(f"  loaded evolved snapshot {SNAP}", flush=True)
else:
    rng0 = np.random.default_rng(5)
    U = proj([np.fft.fftn(c) for c in [rng0.normal(size=(N,) * 3) for _ in range(3)]])
    U = [c * np.where((K > 0) & (K <= 3), np.where(K == 0, 1, K) ** -1.0, 0.0) for c in U]
    urms = np.sqrt(np.mean(sum(np.real(np.fft.ifftn(c)) ** 2 for c in U)))
    U = [c / urms for c in U]
    t = 0.0
    dt = 2e-3
    while t < T - 1e-12:
        h = min(dt, T - t)
        a = rhs(U)
        Um = [U[i] + 0.5 * h * a[i] for i in range(3)]
        b = rhs(Um)
        U = [U[i] + h * b[i] for i in range(3)]
        t += h
    np.save(SNAP, np.stack(U))
    print(f"  evolved to t={T} and saved snapshot ({time.time()-t0:.0f}s)", flush=True)

CBINS = [(0.0, 0.5), (0.5, 0.7), (0.7, 0.85), (0.85, 0.95), (0.95, 1.0)]


def table(U, label):
    wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    Cn, Cp, wm = nematic(wr, 2 * dx)
    G = np.zeros((N, N, N, 3, 3))
    for i in range(3):
        for k in range(3):
            G[..., k, i] = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[k] * U[i]))
    S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
    Sf = S.reshape(-1, 3, 3)
    ev, evec = np.linalg.eigh(Sf)
    ev = ev[:, ::-1]
    evec = evec[:, :, ::-1]
    wv = np.stack(wr, axis=-1).reshape(-1, 3)
    wmf = wm.ravel()
    xf = wv / np.maximum(wmf, 1e-300)[:, None]
    al = np.einsum('ni,nij,nj->n', xf, Sf, xf)
    cs = np.abs(np.einsum('ni,nij->nj', xf, evec))
    Cr = Cn.ravel()
    s2m = np.sqrt(np.einsum('nij,nji->n', Sf, Sf).mean())
    Ptot = (wmf ** 2 * al).sum()
    hi = wmf >= np.quantile(wmf, 0.90)
    pwC = (wmf ** 2 * al * Cr).sum() / Ptot if Ptot != 0 else np.nan
    ewC = (wmf[hi] ** 2 * Cr[hi]).sum() / (wmf[hi] ** 2).sum()
    print(f"  [{label}]  P_tot = {Ptot/(len(wmf)*s2m**3):+.5f} (normalized)   "
          f"production-weighted <C_n> = {pwC:.4f}  vs  enstrophy-weighted <C_n> (hi) = {ewC:.4f}",
          flush=True)
    print(f"{'C_n bin':>12}{'pop %':>8}{'ens %':>8}{'P share':>9}{'per-unit P':>12}{'a/l1':>8}"
          f"{'|xi.e1|':>9}{'|xi.e2|':>9}{'|xi.e3|':>9}", flush=True)
    for lo, hic in CBINS:
        m = hi & (Cr >= lo) & (Cr < hic if hic < 1.0 else Cr <= 1.0)
        if m.sum() < 8:
            print(f"{f'{lo:.2f}-{hic:.2f}':>12}{100*m.sum()/hi.sum():>8.2f}   (empty)", flush=True)
            continue
        ens = (wmf[m] ** 2).sum() / (wmf[hi] ** 2).sum()
        Psh = (wmf[m] ** 2 * al[m]).sum() / Ptot if Ptot != 0 else np.nan
        pu = ((wmf[m] ** 2 * al[m]).sum() / (wmf[m] ** 2).sum()) / s2m
        rat = (al[m] / np.maximum(ev[m, 0], 1e-14)).mean()
        print(f"{f'{lo:.2f}-{hic:.2f}':>12}{100*m.sum()/hi.sum():>8.2f}{100*ens:>8.2f}"
              f"{Psh:>9.3f}{pu:>12.5f}{rat:>8.3f}{cs[m,0].mean():>9.4f}{cs[m,1].mean():>9.4f}"
              f"{cs[m,2].mean():>9.4f}", flush=True)
    return Cr, wmf, hi


print(f"\n  evolved flow (t={T}):", flush=True)
Ce, wme, he = table(U, f"evolved t={T:.0f}")

# ---- control: phase-randomized (org_production's exact map; same rng stream position rule:
#      fresh generator, documented seed) ----
rngp = np.random.default_rng(11)
phi = rngp.uniform(0, 2 * np.pi, size=(N, N, N))
I = np.arange(N)
negidx = lambda a: (-a) % N
phia = (phi - phi[np.ix_(negidx(I), negidx(I), negidx(I))]) / 2
Urand = [c * np.exp(1j * phia) for c in U]
print(f"\n  control: phase-randomized (same spectrum):", flush=True)
Cr_, wmr, hr = table(Urand, "randomized")
me_ = (Ce[he] * wme[he] ** 2).sum() / (wme[he] ** 2).sum()
mr_ = (Cr_[hr] * wmr[hr] ** 2).sum() / (wmr[hr] ** 2).sum()
print(f"\n  V2-0b top-decile nematic coherence:  evolved <C_n> = {me_:.4f}   "
      f"randomized <C_n> = {mr_:.4f}   "
      f"({'PASS -- nematic order is phase-borne' if me_ > mr_ + 0.02 else 'NO SEPARATION -- report honestly'})",
      flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
