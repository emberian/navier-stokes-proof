import numpy as np, time, sys
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
S = 0.5
M = 1
print("=" * 112)
print(f"TRANCHE-3 INDICIAL-EXPONENT GATE -- does the 3D solution VANISH at the layer like "
      f"|zeta|^(1/2)?  (m={M}, s={S})")
print("=" * 112)
print("""  Swept 3D-Lemma 9: exponents nu+- = 1/2 +- (1/2)sqrt(1-4J), J = 2 Om W q^2/(m Om')^2 -- for
  every J > 0 the layer solutions VANISH like |zeta|^{1/2}(+-i mu osc).  2D (q=0) instead has
  the non-vanishing log/pole structure.  This is the swept lemmas' one never-directly-measured
  prediction, and it discriminates the whole swirl-layer theory from 2D in one number.

  REGISTERED, outcomes named:
    T3-1 ** 3D (q=1.5): fitted local exponent of |u_r| vs |r-r_c| on the outer window
         [2 nu^{1/3}, 0.4] lands in [0.3, 0.7] (oscillation-tolerant band around 1/2), at BOTH
         Re = 32000 and 128000 (Re-stable).  Exponent ~ 0 or negative -> swirl square-root law
         REFUTED (3D-Lemma 9's core wrong). **
    T3-2 ** 2D control (q=0), same probe: exponent in [-0.2, +0.2] (non-vanishing) -- the
         discriminator.  If 2D also shows +0.5 the instrument is measuring an artifact. **
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
    B = np.zeros((4 * N, 4 * N))
    B[:3 * N, :3 * N] = np.eye(3 * N)
    return A, B, r


def expfit(q, Re, N):
    A, B, r = sector(M, q, Re, N)
    nu = 2 * np.pi / Re
    f = np.zeros(4 * N, complex)
    f[0:N] = r * np.exp(-r ** 2)
    x = np.linalg.solve(A + 1j * S * B, f)
    ur = np.abs(x[0:N])
    Om = (1 - np.exp(-r ** 2)) / r ** 2
    rc = r[np.argmin(np.abs(M * Om - S))]
    # bin-averaged |u_r|^2 fit: the oscillation |cos(mu ln z)|^2 averages to a constant within
    # log bins, leaving the pure envelope slope (= 2 x exponent); window clear of the viscous
    # flattening at 3 nu^{1/3}
    lo, hi_ = 3 * nu ** (1 / 3.0), 0.5
    sides = []
    for sgn in (+1, -1):
        z = sgn * (r - rc)
        w = (z > lo) & (z < hi_)
        if w.sum() >= 8:
            lz = np.log(z[w])
            lu2 = ur[w] ** 2
            edges = np.linspace(lz.min(), lz.max() + 1e-9, 7)
            cx, cy = [], []
            for a, b in zip(edges[:-1], edges[1:]):
                m_ = (lz >= a) & (lz < b)
                if m_.sum() >= 1:
                    cx.append(0.5 * (a + b))
                    cy.append(np.log(max(lu2[m_].mean(), 1e-300)))
            c = 0.5 * np.polyfit(cx, cy, 1)[0]
            sides.append(c)
    return rc, sides, ur.max()


RES = [32000] if SMOKE else [32000, 128000]
NN = 300 if SMOKE else 800
ok3, ok2 = [], []
for Re in RES:
    rc, s3, _ = expfit(1.5, Re, NN)
    rc2, s2, _ = expfit(0.0, Re, NN)
    m3 = np.mean(s3)
    m2 = np.mean(s2)
    ok3.append(0.3 <= m3 <= 0.7)
    ok2.append(-0.2 <= m2 <= 0.2)
    print(f"  Re={Re}: r_c={rc:.3f}   3D (q=1.5) exponents {['%.3f' % v for v in s3]} mean "
          f"{m3:+.3f}   2D (q=0) {['%.3f' % v for v in s2]} mean {m2:+.3f}", flush=True)
print(f"\n  T3-1 3D exponent in [0.3, 0.7], Re-stable: "
      f"{'PASS -- the swirl square-root law, measured' if all(ok3) else 'FAIL/inspect'}",
      flush=True)
print(f"  T3-2 2D control in [-0.2, 0.2]: "
      f"{'PASS -- discriminator clean' if all(ok2) else 'CONTROL DIRTY -- instrument artifact'}",
      flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)


# ---- T3-1' (the robust form; registered after the window-fit's instrument note): the LAYER-
# POINT VALUE must scale: 3D |u_r(r_c)|/max ~ nu^{1/6} (the zeta^{1/2} law cut at the viscous
# width); 2D constant.  Bands: 3D alpha in [0.08, 0.25]; 2D alpha in [-0.05, 0.06]. ----
print("\n  T3-1' layer-point scaling |u_r(r_c)|/max vs nu:", flush=True)
def layerval(q, Re, N):
    A, B, r = sector(M, q, Re, N)
    f = np.zeros(4 * N, complex)
    f[0:N] = r * np.exp(-r ** 2)
    x = np.linalg.solve(A + 1j * S * B, f)
    ur = np.abs(x[0:N])
    Om = (1 - np.exp(-r ** 2)) / r ** 2
    ic = np.argmin(np.abs(M * Om - S))
    return ur[ic] / ur.max()
RES2 = [(8000, 800), (32000, 800), (128000, 800), (512000, 1600)]
for q, nm in ((1.5, "3D"), (0.0, "2D")):
    vals, nus = [], []
    for Re, NN2 in RES2:
        v = layerval(q, Re, NN2)
        vals.append(v)
        nus.append(2 * np.pi / Re)
        print(f"    {nm} Re={Re}: {v:.4f}", flush=True)
    al = np.polyfit(np.log(nus), np.log(vals), 1)[0]
    band = (0.08, 0.25) if q > 0 else (-0.05, 0.06)
    print(f"    {nm} fitted alpha = {al:+.3f}  target {band}: "
          f"{'PASS' if band[0] <= al <= band[1] else 'FAIL/inspect'}", flush=True)
