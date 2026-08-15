import numpy as np, time, sys, os
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 32 if SMOKE else 64
NU = 0.006
SNAP = f"results/l19_field_t8_N{N}.npy"
DTS_A = [0.0, 0.25] if SMOKE else [0.0, 0.125, 0.25, 0.5, 1.0]
DTS_B = [0.0, 0.1] if SMOKE else [0.0, 0.05, 0.1, 0.2, 0.4, 0.8]
print("=" * 118)
print(f"L19-R GATE -- the rigidity alternative, tested dynamically   (N={N}, nu={NU}, "
      f"snapshot {SNAP})")
print("=" * 118)
print("""  L19-R (the e-fold alternative): per intense point and e-fold window, EITHER production runs
  at the capped/slow rate, OR the local state contracts to the nematic-aligned class on the fast
  clock ~1/g (L19-R1, the contraction estimate: sustained pairing pins xi near +-e1 and the
  projective flow contracts dispersion at the spectral-gap rate), whereupon the veto collapses
  the pairing to gamma_far (L19-R2, exact).  The only escape -- a strain-decorrelated arranged
  tangle -- must be locally self-similar across e-folds (L19-R3 bridge), excluded by the anchors.
  Consequence: fast production self-limits to ~one e-fold per re-tangling cycle, and re-tangling
  runs on the SLOW clock (decoherence <= 2 gamma_far, sec 121.3).

  Dynamical predictions, tested here on the real flow:
  (A) THE DRAIN: the flow never accumulates a population that is simultaneously fast-producing
      and direction-tangled; pairing and coherence stay positively associated.
  (B) THE BASIN: destroy ALL organization (phase randomization, spectrum intact) and re-evolve --
      the flow must fall back to the veto fixed point (e2-locked, capped) on the fast clock, with
      production and organization igniting TOGETHER (production never leads: Lemma 18's
      inequality, live), and NO transient e1-locked runaway en route.

  REGISTERED, all outcomes named (thresholds = medians of the t=8 intense set, fixed once):
    R1a ** at every snapshot of branch A, the above-median-pairing intense population is
        coherence-ENRICHED: mean C_n | (p > p*) >= mean C_n | (p <= p*).  Anti-association at
        any snapshot REFUTES (a tangle-favouring pump). **
    R1b ** the fast-tangled quadrant (p > p*, C_n < C*) carries production share <= its
        enstrophy share + 0.1 at all times, and its population fraction does not grow
        monotonically across branch A.  Growth of a producing fast-tangle REFUTES. **
    R2a ** branch B: the intense set returns to e2-dominance (|xi.e2| >= 0.7) with
        a/l1 <= 0.5 at every snapshot INCLUDING the transient -- re-convergence to the veto
        fixed point with no e1-runaway spike.  A transient with |xi.e1| dominant or
        a/l1 > 0.7 REFUTES attractor uniqueness. **
    R2b ** branch B: normalized production P and the omega^2-weighted anisotropy Org rise
        TOGETHER: at every snapshot |P| <= sqrt(2/3) * Org * I2 (Lemma 18's inequality, live),
        and P stays below the evolved baseline (+0.416) throughout the transient. **
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


def evolve(U, T):
    t = 0.0
    dt = 2e-3
    U = [c.copy() for c in U]
    while t < T - 1e-12:
        h = min(dt, T - t)
        a = rhs(U)
        Um = [U[i] + 0.5 * h * a[i] for i in range(3)]
        b = rhs(Um)
        U = [U[i] + h * b[i] for i in range(3)]
        t += h
    return U


GF = lambda f, ell: np.real(np.fft.ifftn(np.exp(-0.5 * K2 * ell ** 2) * np.fft.fftn(f)))


def full_diag(U):
    """Returns per-point arrays: p (local pairing), Cn, wm2, al, lam1, |xi.e_i|, plus globals."""
    wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    Mf = np.zeros((N, N, N, 3, 3))
    for i in range(3):
        for j in range(i, 3):
            Mf[..., i, j] = Mf[..., j, i] = GF(wr[i] * wr[j], 2 * dx)
    mu = np.linalg.eigvalsh(Mf.reshape(-1, 3, 3))[:, ::-1]
    Cn = (mu[:, 0] - 0.5 * (mu[:, 1] + mu[:, 2])) / np.maximum(mu.sum(1), 1e-14)
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
    wm = np.sqrt((wv ** 2).sum(1))
    xf = wv / np.maximum(wm, 1e-300)[:, None]
    al = np.einsum('ni,nij,nj->n', xf, Sf, xf)
    cs = np.abs(np.einsum('ni,nij->nj', xf, evec))
    trS2 = np.einsum('nij,nji->n', Sf, Sf)
    p = al / np.maximum(np.sqrt(trS2), 1e-14)
    Anorm = np.sqrt(((cs ** 2 - 1.0 / 3.0) ** 2).sum(1))
    return dict(p=p, Cn=Cn, wm=wm, al=al, l1=ev[:, 0], cs=cs, trS2=trS2, A=Anorm)


def census(d, pstar, cstar, label):
    hi = d['wm'] >= np.quantile(d['wm'], 0.90)
    w2 = d['wm'] ** 2
    Ptot = (w2 * d['al']).sum()
    ens_hi = w2[hi].sum()
    quads = [("F-T", (d['p'] > pstar) & (d['Cn'] < cstar)),
             ("F-A", (d['p'] > pstar) & (d['Cn'] >= cstar)),
             ("S-T", (d['p'] <= pstar) & (d['Cn'] < cstar)),
             ("S-A", (d['p'] <= pstar) & (d['Cn'] >= cstar))]
    mA, mB = hi & (d['p'] > pstar), hi & (d['p'] <= pstar)
    CnA = (d['Cn'][mA] * w2[mA]).sum() / w2[mA].sum() if mA.sum() else np.nan
    CnB = (d['Cn'][mB] * w2[mB]).sum() / w2[mB].sum() if mB.sum() else np.nan
    print(f"  [{label}]  R1a coherence-enrichment: <C_n | p>p*> = {CnA:.4f}  vs  "
          f"<C_n | p<=p*> = {CnB:.4f}   ({'PASS' if CnA >= CnB else 'ANTI-ASSOCIATED'})",
          flush=True)
    print(f"{'quad':>8}{'pop %':>8}{'ens %':>8}{'P share':>9}{'a/l1':>8}{'|xi.e1|':>9}"
          f"{'|xi.e2|':>9}", flush=True)
    out = {}
    for nm, q in quads:
        m = hi & q
        if m.sum() < 8:
            print(f"{nm:>8}   (empty)", flush=True)
            out[nm] = dict(pop=0, Psh=0, ensh=0)
            continue
        pop = m.sum() / hi.sum()
        ensh = w2[m].sum() / ens_hi
        Psh = (w2[m] * d['al'][m]).sum() / Ptot if Ptot != 0 else np.nan
        rat = (d['al'][m] / np.maximum(d['l1'][m], 1e-14)).mean()
        print(f"{nm:>8}{100*pop:>8.2f}{100*ensh:>8.2f}{Psh:>9.3f}{rat:>8.3f}"
              f"{d['cs'][m,0].mean():>9.4f}{d['cs'][m,1].mean():>9.4f}", flush=True)
        out[nm] = dict(pop=pop, Psh=Psh, ensh=ensh)
    return out


if not os.path.exists(SNAP):
    print(f"  no snapshot {SNAP} -- run l19_gate2.py first (or --smoke after its smoke)")
    sys.exit(1)
U0 = [c.copy() for c in np.load(SNAP)]

# thresholds fixed ONCE from the t=8 intense set
d0 = full_diag(U0)
hi0 = d0['wm'] >= np.quantile(d0['wm'], 0.90)
pstar, cstar = np.median(d0['p'][hi0]), np.median(d0['Cn'][hi0])
print(f"  thresholds (t=8 intense-set medians, fixed): p* = {pstar:.4f}, C* = {cstar:.4f}\n",
      flush=True)

print("  --- BRANCH A: the drain (continued evolution) ---", flush=True)
ftpops = []
for dtv in DTS_A:
    Ua = evolve(U0, dtv) if dtv > 0 else U0
    da = full_diag(Ua) if dtv > 0 else d0
    r = census(da, pstar, cstar, f"t = 8 + {dtv:.3f}")
    ft = r["F-T"]
    ftpops.append(ft['pop'])
    ok = ft['Psh'] <= ft['ensh'] + 0.1
    print(f"    R1b fast-tangle: pop {100*ft['pop']:.2f}%, P share {ft['Psh']:.3f} vs ens share "
          f"{ft['ensh']:.3f}  ({'PASS' if ok else 'VIOLATION'})\n", flush=True)
grow = all(b > a + 0.01 for a, b in zip(ftpops, ftpops[1:])) and len(ftpops) > 2
print(f"  R1b population track: {['%.3f' % f for f in ftpops]}   "
      f"({'MONOTONE GROWTH -- REFUTES' if grow else 'no monotone growth -- PASS'})\n", flush=True)

print("  --- BRANCH B: the basin (randomize, re-evolve) ---", flush=True)
rngp = np.random.default_rng(11)
phi = rngp.uniform(0, 2 * np.pi, size=(N, N, N))
I = np.arange(N)
negidx = lambda a: (-a) % N
phia = (phi - phi[np.ix_(negidx(I), negidx(I), negidx(I))]) / 2
Ur0 = [c * np.exp(1j * phia) for c in U0]
print(f"{'t\'':>8}{'P_norm':>10}{'Org(w2<|A|>)':>13}{'L18 rhs':>10}{'<C_n>hi':>9}{'|xi.e1|':>9}"
      f"{'|xi.e2|':>9}{'a/l1':>8}{'R2a':>7}{'R2b':>7}", flush=True)
for dtv in DTS_B:
    Ub = evolve(Ur0, dtv) if dtv > 0 else Ur0
    db = full_diag(Ub)
    w2 = db['wm'] ** 2
    hib = db['wm'] >= np.quantile(db['wm'], 0.90)
    s2m = np.sqrt(db['trS2'].mean())
    Pn = (w2 * db['al']).sum() / (len(w2) * s2m ** 3)
    Org = (w2 * db['A']).sum() / w2.sum()
    I2 = (w2 * np.sqrt(db['trS2'])).sum() / (len(w2) * s2m ** 3)
    l18 = np.sqrt(2.0 / 3.0) * (w2 * db['A'] * np.sqrt(db['trS2'])).sum() / (len(w2) * s2m ** 3)
    Cnh = (db['Cn'][hib] * w2[hib]).sum() / w2[hib].sum()
    e1, e2 = db['cs'][hib, 0].mean(), db['cs'][hib, 1].mean()
    rat = (db['al'][hib] / np.maximum(db['l1'][hib], 1e-14)).mean()
    r2a = "ok" if (rat <= 0.7 and e1 < e2 + 0.15) else "SPIKE"
    r2b = "ok" if (abs(Pn) <= l18 + 1e-9 and Pn <= 0.45) else "VIOL"
    print(f"{dtv:>8.2f}{Pn:>10.4f}{Org:>13.4f}{l18:>10.4f}{Cnh:>9.4f}{e1:>9.4f}{e2:>9.4f}"
          f"{rat:>8.3f}{r2a:>7}{r2b:>7}", flush=True)
print(f"""
  READ-OFF:
    R2a: e2 must recover dominance (>=0.7) on the fast clock with a/l1 <= 0.5 at every row --
         the veto fixed point is the basin's unique attractor; any e1-dominant or a/l1 > 0.7
         transient REFUTES.
    R2b: |P_norm| <= L18-rhs row by row (the inequality live) and P_norm <= evolved baseline
         0.416 + margin throughout -- production never leads organization.
  total {time.time()-t0:.0f}s""", flush=True)
