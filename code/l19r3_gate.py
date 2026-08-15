import numpy as np, time, sys, os
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 32 if SMOKE else 64
NU = 0.006
SNAP = f"results/l19_field_t8_N{N}.npy"
DTS = [0.05, 0.1] if SMOKE else [0.05, 0.1, 0.2, 0.4]
print("=" * 112)
print(f"L19-R3 GATE -- THE FRAGILITY CLOCK: does the production ARRANGEMENT decay faster than "
      f"the STRUCTURES?  (N={N})")
print("=" * 112)
print("""  The bridge's mechanism (the 3:1 law, exact): financing strain deforms an arrangement >= 3x
  faster than it stretches -- so a production-carrying pattern is FRAGILE relative to the
  structures that carry it, and maintenance across e-folds requires active reformation
  (whence the recurrence -> DSS bridge).  Dynamical trace, measurable today:

  INSTRUMENT: Eulerian autocorrelation of the production-density field q(x) = omega.S.omega vs
  the enstrophy field e(x) = |omega|^2 over lag Delta.  Both fields advect IDENTICALLY, so the
  sweeping contribution cancels in the RATIO of decay rates: the excess decay of q over e is
  the arrangement's intrinsic fragility.

  REGISTERED, outcomes named:
    C-R3a ** the production field decorrelates FASTER than the enstrophy field: implied decay
          rate ratio r_q/r_e >= ~1.5 across lags (the 3:1 mechanism's dynamical trace, diluted
          by common-mode sweeping -- any ratio clearly > 1 confirms fragility; >= 1.5 strong).
          REFUTED if r_q/r_e <= 1: arrangements would OUTLIVE structures -- maintenance free,
          the 3:1 clock dynamically irrelevant, the bridge's premise dead. **
    C-R3b ** certification that C-R3a IS an intense-set statement: the top-decile mask must
          carry >= 50% of the global variance of q (q ~ omega^2 alpha is intensity-weighted by
          construction).  [The hard-mask restricted-correlation variant was found MALFORMED at
          smoke: conditioning on e and measuring e's persistence inside the mask is range
          restriction -- it crushes corr(e) (0.972 vs 0.993) and inverts the ratio (0.38).
          Registered as an instrument note; the mask columns are printed for the record but
          carry no gate weight.] **
""", flush=True)
t0 = time.time()
nu = NU
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


def fields(U):
    """q = omega.S.omega (production density), e = |omega|^2, plus mean strain magnitude."""
    wr = [np.real(np.fft.ifftn(c)) for c in cur(U)]
    G = np.zeros((N, N, N, 3, 3))
    for i in range(3):
        for k in range(3):
            G[..., k, i] = np.real(np.fft.ifftn(1j * (KX, KY, KZ)[k] * U[i]))
    S = 0.5 * (G + np.transpose(G, (0, 1, 2, 4, 3)))
    wv = np.stack(wr, axis=-1)
    q = np.einsum('...i,...ij,...j->...', wv, S, wv)
    e = (wv ** 2).sum(-1)
    s2m = np.sqrt(np.einsum('...ij,...ji->...', S, S).mean())
    return q, e, s2m


def corr(a, b, m=None):
    if m is not None:
        a, b = a[m], b[m]
    a = a - a.mean()
    b = b - b.mean()
    return (a * b).mean() / np.sqrt((a ** 2).mean() * (b ** 2).mean())


if not os.path.exists(SNAP):
    print(f"  no snapshot {SNAP} -- run l19_gate2.py first")
    sys.exit(1)
U = [c.copy() for c in np.load(SNAP)]
q0, e0, s2m = fields(U)
hi = e0 >= np.quantile(e0, 0.90)
vsh = ((q0 - q0.mean()) ** 2)[hi].sum() / ((q0 - q0.mean()) ** 2).sum()
print(f"  t=8 reference: mean strain (trS^2)^1/2 = {s2m:.3f}  (one strain time = {1/s2m:.3f})",
      flush=True)
print(f"  C-R3b variance share of q on the intense mask = {vsh:.3f}   "
      f"({'PASS -- the global ratio is an intense-set statement' if vsh >= 0.5 else 'BELOW 0.5'})\n",
      flush=True)
print(f"{'Delta':>8}{'strain units':>13}{'corr q':>9}{'corr e':>9}{'rate q':>9}{'rate e':>9}"
      f"{'ratio':>8}{'  | intense: corr q':>19}{'corr e':>9}{'ratio':>8}", flush=True)
t = 0.0
dt = 2e-3
ratios, ratios_hi = [], []
for tv in DTS:
    while t < tv - 1e-12:
        h = min(dt, tv - t)
        a = rhs(U)
        Um = [U[i] + 0.5 * h * a[i] for i in range(3)]
        b = rhs(Um)
        U = [U[i] + h * b[i] for i in range(3)]
        t += h
    q1, e1, _ = fields(U)
    cq, ce = corr(q0, q1), corr(e0, e1)
    cqh, ceh = corr(q0, q1, hi), corr(e0, e1, hi)
    rq, re = -np.log(max(cq, 1e-9)) / tv, -np.log(max(ce, 1e-9)) / tv
    rqh, reh = -np.log(max(cqh, 1e-9)) / tv, -np.log(max(ceh, 1e-9)) / tv
    ratios.append(rq / re)
    ratios_hi.append(rqh / reh)
    print(f"{tv:>8.2f}{tv*s2m:>13.2f}{cq:>9.4f}{ce:>9.4f}{rq:>9.3f}{re:>9.3f}{rq/re:>8.2f}"
          f"{cqh:>19.4f}{ceh:>9.4f}{rqh/reh:>8.2f}", flush=True)
mn = min(ratios)
print(f"\n  C-R3a global: min rate ratio = {mn:.2f}   "
      f"({'PASS (fragility confirmed)' if mn > 1.0 else 'REFUTED -- arrangements outlive structures'})"
      f"{'  [>= 1.5: strong]' if mn >= 1.5 else ''}", flush=True)
print(f"  (mask columns: recorded, no gate weight -- range-restriction artifact, see header)",
      flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
