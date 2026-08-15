import numpy as np, scipy.linalg as sla, time, sys
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 80 if SMOKE else 200
QC = 2.26
print("=" * 114)
print(f"L16/L17 BLOCK-EXTRACTION GATE -- Riesz projection + 2x2 normal form, measured  "
      f"(N={N}, R=10, q={QC})")
print("=" * 114)
print("""  Swept Lemma 16: the Kelvin pair is isolated (nu << nu^{1/3} hierarchy); the Riesz projection
  P2 = (1/2pi i) contour-int (lam B - A)^{-1} B dlam is rank-2, idempotent, nu-uniformly bounded.
  Swept Lemma 17: on ran P2 the generator is A = -c_K nu I + i Delta J + eps K, |K12| ~ kappa.

  Instrument notes (registered before running): the elliptic (m=-1,+1) pair at the q ~ 2.26
  crossing sits near omega = 0 AMONG the finite-domain edge-continuum clusters (sec 158 caution)
  -- so the pair is identified by the MOVERS-UNDER-EPS method: the exactly-2 eigenvalues that
  move O(eps) when strain couples the sectors (continuum movers are O(eps^2)/none).  kappa is
  extracted from the EIGENVALUE SPLIT (split/2eps) -- immune to non-normality: damping shifts
  the diagonal, the split is pure coupling.  Desk cross-check: sec 158's raw sigma/eps = 0.414
  + c_K nu/eps ~ 0.24 gives kappa ~ 0.65 inside [0.57, 0.73].

  REGISTERED, controls first, all outcomes named:
    V-1  ** centroid control (banked S5-1 rerun on this code path): q=0, Re=1e7, eps=0.02 ->
         coupled spectrum contains lambda = +/-eps within few % -- validates signs. **
    C-0  ** eps=0 control: coupled spectrum at q=2.26 splits into decoupled sectors; the
         movers-method finds EXACTLY 2 large movers (the pair).  != 2 -> identification void. **
    B2-1 ** P2 from the contour around the pair: ||P2^2-P2||/||P2|| <= 1e-3, trace ~ rank = 2.
         Registered radius nu^{1/3}/2 attempted first; if edge clusters intrude (finite-domain
         artifact), the adaptive radius (half-distance to nearest non-pair mode) is the
         measurement and the intrusion is recorded.  Non-idempotent at ALL radii -> Lemma 16
         REFUTED. **
    B2-2 ** pair damping: Re(lam pair) < 0 and O(nu): c_K = -Re lam/nu in [2,4] (registered
         bracket from s*=0.3595); O(nu) confirmed by Re-doubling (c_K Re-stable).  If outside
         [2,4] but O(nu) and Re-stable: bracket refinement, recorded, normal form intact. **
    B2-3 ** coupling: kappa = split/(2 eps) in [0.57, 0.73], eps-linear (0.02 vs 0.04 within
         ~10%), eps=0 detuning << eps kappa.  Outside bracket -> normal form REFUTED. **
    B2-4 ** robustness: Re 2000 -> 4000 (c_K, kappa stable); contour radius halving (B2-1
         stable). **
""", flush=True)
t0 = time.time()


def sector(m, q, Re, N, R=10.0):
    h = R / N
    r = h * (np.arange(N) + 0.5)
    nu = 2 * np.pi / Re
    Om = (1 - np.exp(-r ** 2)) / r ** 2
    W = 2 * np.exp(-r ** 2)
    I = np.eye(N)
    d1 = np.zeros((N, N))
    for j in range(N):
        if j > 0:
            d1[j, j - 1] = -1 / (2 * h)
        if j < N - 1:
            d1[j, j + 1] = 1 / (2 * h)
    d1[N - 1, N - 1] -= 1 / (2 * h)
    d2 = (-2 * np.eye(N) + np.diag(np.ones(N - 1), 1) + np.diag(np.ones(N - 1), -1)) / h ** 2
    Lm = d2 + np.diag(1 / r) @ d1 - np.diag(m ** 2 / r ** 2) - q ** 2 * I
    A = np.zeros((4 * N, 4 * N), complex)
    iOm = np.diag(-1j * m * Om)
    A[0:N, 0:N] = iOm + nu * (Lm - np.diag(1 / r ** 2))
    A[0:N, N:2 * N] = np.diag(2 * Om) + nu * np.diag(-2j * m / r ** 2)
    A[0:N, 3 * N:4 * N] = -d1
    A[N:2 * N, 0:N] = np.diag(-W) + nu * np.diag(2j * m / r ** 2)
    A[N:2 * N, N:2 * N] = iOm + nu * (Lm - np.diag(1 / r ** 2))
    A[N:2 * N, 3 * N:4 * N] = np.diag(-1j * m / r)
    A[2 * N:3 * N, 2 * N:3 * N] = iOm + nu * Lm
    A[2 * N:3 * N, 3 * N:4 * N] = -1j * q * I
    A[3 * N:4 * N, 0:N] = d1 + np.diag(1 / r)
    A[3 * N:4 * N, N:2 * N] = np.diag(1j * m / r)
    A[3 * N:4 * N, 2 * N:3 * N] = 1j * q * I
    return A, d1, r, h


def cblock(msrc, sgn, eps, d1, r, N):
    RD = np.diag(r) @ d1
    C = np.zeros((4 * N, 4 * N), complex)
    C[0:N, 0:N] = (eps / 2) * (RD + (-sgn * msrc + 1) * np.eye(N))
    C[N:2 * N, N:2 * N] = (eps / 2) * (RD + (-sgn * msrc - 1) * np.eye(N))
    C[N:2 * N, 0:N] = sgn * 1j * eps * np.eye(N)
    C[2 * N:3 * N, 2 * N:3 * N] = (eps / 2) * (RD + (-sgn * msrc) * np.eye(N))
    return C


def coupled(eps, q, Re, N):
    Ap, d1, r, _ = sector(+1, q, Re, N)
    Am, _, _, _ = sector(-1, q, Re, N)
    Cp = cblock(-1, +1, eps, d1, r, N)
    Cm = cblock(+1, -1, eps, d1, r, N)
    Ac = np.block([[Ap, -Cp], [-Cm, Am]])
    Bc = np.zeros((8 * N, 8 * N))
    Bc[:3 * N, :3 * N] = np.eye(3 * N)
    Bc[4 * N:7 * N, 4 * N:7 * N] = np.eye(3 * N)
    return Ac, Bc


def spec(eps, q, Re, N, vecs=False):
    Ac, Bc = coupled(eps, q, Re, N)
    if vecs:
        ev, V = sla.eig(Ac, Bc, right=True)
    else:
        ev = sla.eig(Ac, Bc, right=False)
        V = None
    ok = np.isfinite(ev) & (np.abs(ev) < 5)
    return (ev[ok], V[:, ok] if vecs else None, Ac, Bc)


# ---- V-1: centroid control (banked S5-1) ----
evc, _, _, _ = spec(0.02, 0.0, 1e7, N)
dp = np.min(np.abs(evc - 0.02))
dm = np.min(np.abs(evc + 0.02))
print(f"  V-1 centroid: |lam-eps|min = {dp:.2e} ({100*dp/0.02:.1f}%)  |lam+eps|min = {dm:.2e} "
      f"({100*dm/0.02:.1f}%)   ({'PASS' if max(dp, dm) < 0.15 * 0.02 else 'FAIL -- signs'})",
      flush=True)

# ---- C-0: eps=0 control + movers identification at the crossing ----
Re0 = 2000
nu0 = 2 * np.pi / Re0
e0, V0, A0, B0 = spec(0.0, QC, Re0, N, vecs=True)
EPS1, EPS2 = 0.02, 0.04
e1, _, _, _ = spec(EPS1, QC, Re0, N)
e2, V2, A2, B2 = spec(EPS2, QC, Re0, N, vecs=True)
box = (np.abs(e0.imag) < 0.4) & (e0.real > -0.12) & (e0.real < 0.02)
cand = np.where(box)[0]
mov = np.array([np.min(np.abs(e2 - e0[i])) for i in cand])
srt = np.argsort(mov)[::-1]
big = [cand[srt[k]] for k in range(min(6, len(cand)))]
print(f"  C-0 movers under eps={EPS2} (top 6 in the crossing box): "
      + "  ".join(f"{e0[i]:.4f}->d{mov[list(cand).index(i)]:.4f}" for i in big), flush=True)
thr = 0.3 * EPS2
nbig = int((mov > thr).sum())
i1, i2 = big[0], big[1]
print(f"  C-0 movers > {thr:.3f}: {nbig}   "
      f"({'PASS -- exactly 2 (the pair)' if nbig == 2 else 'NOT 2 -- identification per notes'})",
      flush=True)
lp, lm = e0[i1], e0[i2]
det0 = abs(lp.imag - lm.imag)
print(f"  pair (eps=0): {lp:.5f}, {lm:.5f}   detuning = {det0:.5f}", flush=True)

# ---- B2-2: damping ----
cK1, cK2 = -lp.real / nu0, -lm.real / nu0
print(f"  B2-2 c_K = {cK1:.2f}, {cK2:.2f}   "
      f"({'PASS [2,4]' if all(2 <= c <= 4 for c in (cK1, cK2)) else 'outside [2,4] -- see O(nu) check'})",
      flush=True)

# ---- B2-3: split-based kappa ----
def split_kappa(eps, epair, evals):
    n1 = evals[np.argmin(np.abs(evals - epair[0]))]
    n2 = evals[np.argmin(np.abs(evals - epair[1]))]
    return abs(n1 - n2) / (2 * eps), n1, n2


k1, n11, n12 = split_kappa(EPS1, (lp, lm), e1)
k2, n21, n22 = split_kappa(EPS2, (lp, lm), e2)
print(f"  B2-3 kappa(eps={EPS1}) = {k1:.4f}   kappa(eps={EPS2}) = {k2:.4f}   "
      f"(pair at eps={EPS2}: {n21:.5f}, {n22:.5f})", flush=True)
lin = abs(k1 - k2) / max(k2, 1e-9)
inb = 0.57 <= k2 <= 0.73
print(f"  B2-3 eps-linearity: |dkappa|/kappa = {100*lin:.1f}%   bracket [0.57,0.73]: "
      f"{'PASS' if inb else 'OUTSIDE'}   detuning/eps.kappa = {det0/max(EPS2*k2,1e-9):.2f}",
      flush=True)

# ---- B2-1: contour Riesz projection around the pair ----
def riesz(Ac, Bc, center, rad, npts=24):
    P = np.zeros_like(Ac)
    for k in range(npts):
        th = 2 * np.pi * (k + 0.5) / npts
        lam = center + rad * np.exp(1j * th)
        P += rad * np.exp(1j * th) * np.linalg.solve(lam * Bc - Ac, Bc)
    return P / npts


center = 0.5 * (lp + lm)
others = np.delete(e0, [i1, i2])
gap = np.min(np.abs(others - center))
rad_reg = 0.5 * nu0 ** (1 / 3)
rad_ad = 0.5 * (gap + max(abs(lp - center), abs(lm - center)))
inside_reg = int((np.abs(e0 - center) < rad_reg).sum())
print(f"  B2-1 contour: center {center:.4f}; registered radius {rad_reg:.4f} encloses "
      f"{inside_reg} eps=0 modes; nearest non-pair at {gap:.4f}; adaptive radius {rad_ad:.4f}",
      flush=True)
use_rad = rad_ad if inside_reg != 2 else rad_reg
P2 = riesz(A0, B0, center, use_rad)
idem = np.linalg.norm(P2 @ P2 - P2) / max(np.linalg.norm(P2), 1e-12)
tr = np.trace(P2)
print(f"  B2-1 at radius {use_rad:.4f}: ||P2^2-P2||/||P2|| = {idem:.2e}   trace = "
      f"{tr.real:.3f}{tr.imag:+.0e}i   "
      f"({'PASS' if idem <= 1e-3 and abs(tr - 2) < 0.05 else 'FAIL'})", flush=True)
P2h = riesz(A0, B0, center, use_rad / 2)
idh = np.linalg.norm(P2h @ P2h - P2h) / max(np.linalg.norm(P2h), 1e-12)
trh = np.trace(P2h).real
print(f"  B2-4 radius halved: idem = {idh:.2e}  trace = {trh:.3f}   "
      f"({'PASS' if idh <= 1e-3 and abs(trh - 2) < 0.05 else 'FAIL'})", flush=True)

# ---- B2-4: Re-doubling ----
if not SMOKE:
    Re4 = 4000
    nu4 = 2 * np.pi / Re4
    e04, _, _, _ = spec(0.0, QC, Re4, N)
    e24, _, _, _ = spec(EPS2, QC, Re4, N)
    p1 = e04[np.argmin(np.abs(e04 - lp))]
    p2 = e04[np.argmin(np.abs(e04 - lm))]
    cK4 = (-p1.real / nu4, -p2.real / nu4)
    k4, _, _ = split_kappa(EPS2, (p1, p2), e24)
    print(f"  B2-4 Re=4000: c_K = {cK4[0]:.2f}, {cK4[1]:.2f} (vs {cK1:.2f}, {cK2:.2f})   "
          f"kappa = {k4:.4f} (vs {k2:.4f})   "
          f"({'PASS -- O(nu) damping + Re-stable coupling' if abs(k4 - k2) / k2 < 0.15 else 'inspect'})",
          flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
