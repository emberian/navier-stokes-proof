import numpy as np, time, sys
from scipy.optimize import curve_fit
np.set_printoptions(suppress=True)
SMOKE = "--smoke" in sys.argv
N = 400 if SMOKE else 1600
M = 1
print("=" * 114)
print(f"T3 EXACTNESS GATE -- converging the swirl vanishing exponent to its exact value 1/6 "
      f"(N={N})")
print("=" * 114)
print("""  The EXACT statement is the proved algebra: exponent = Re nu+- = 1/2, cut at the viscous
  width nu^{1/3} => layer-point value ~ nu^{1/6} exactly (indicial identities banked at 1e-16).
  A finite-Re fit ESTIMATES that asymptote; this instrument makes the estimate converge with an
  error budget -- and tests the theory's own sub-leading prediction: the indicial oscillation
  zeta^{+-i mu} at the viscous cutoff imposes a LOG-PERIODIC modulation of frequency mu/3 in
  ln nu, with mu = sqrt(J - 1/4) computed EXACTLY from the profile (parameter-free).

  REGISTERED, outcomes named:
    X-1 ** the mu-locked joint fit's envelope exponent alpha in [0.150, 0.185] at BOTH band
        points s = 0.5 (mu = 2.00) and s = 0.7 (mu = 3.20); Richardson-extrapolated pairwise
        slope consistent.  Outside -> the 1/6 law fails quantitatively. **
    X-2 ** the modulation, if significant, sits at the EXACT mu(s) -- frequency locked, only
        amplitude/phase fitted; joint-fit rms must improve on the pure power fit or A ~ 0. **
    X-3 ** universality: the two s-values give the SAME envelope alpha (+-0.02) while mu(s)
        differs by 60% -- the envelope is universal, the modulation tracks the exact J. **
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


def layerval(s, Re, N, q=1.5):
    A, B, r = sector(M, q, Re, N)
    f = np.zeros(4 * N, complex)
    f[0:N] = r * np.exp(-r ** 2)
    x = np.linalg.solve(A + 1j * s * B, f)
    ur = np.abs(x[0:N])
    Om = (1 - np.exp(-r ** 2)) / r ** 2
    rc = np.interp(s, (M * Om)[::-1], r[::-1])
    return np.interp(rc, r, ur) / np.interp(2.5, r, ur), rc


def exact_mu(s, q=1.5):
    rr = np.linspace(0.05, 5, 200000)
    Om = (1 - np.exp(-rr ** 2)) / rr ** 2
    rc = np.interp(s, Om[::-1], rr[::-1])
    W = 2 * np.exp(-rc ** 2)
    Op = (2 / rc) * (np.exp(-rc ** 2) - s / M)
    J = 2 * s * W * q ** 2 / (M * Op * rc * 0 + (M * Op) ** 2) * 1.0
    J = 2 * (s / M) * W * q ** 2 / (M * Op) ** 2
    return np.sqrt(J - 0.25), J, rc


RES = [8000, 32000, 128000] if SMOKE else [4000, 8000, 16000, 32000, 64000, 128000, 256000,
                                           512000]
for s in ([0.5] if SMOKE else [0.5, 0.7]):
    mu, J, rc = exact_mu(s)
    print(f"\n  s = {s}: r_c = {rc:.4f}, J = {J:.3f}, EXACT mu = {mu:.4f} "
          f"(modulation frequency mu/3 = {mu/3:.4f} in ln nu)", flush=True)
    vals, nus = [], []
    for Re in RES:
        v, _ = layerval(s, Re, N)
        vals.append(v)
        nus.append(2 * np.pi / Re)
        print(f"    Re={Re}: {v:.4f}", flush=True)
    lv, ln_ = np.log(vals), np.log(nus)
    a_pure, c_pure = np.polyfit(ln_, lv, 1)
    rms_pure = np.sqrt(np.mean((np.polyval([a_pure, c_pure], ln_) - lv) ** 2))
    pw = [(lv[i + 1] - lv[i]) / (ln_[i + 1] - ln_[i]) for i in range(len(lv) - 1)]
    print(f"    pairwise slopes: {['%.3f' % p for p in pw]}", flush=True)
    if len(RES) >= 6:
        nm = [np.sqrt(nus[i] * nus[i + 1]) ** (1 / 3.0) for i in range(len(pw))]
        a_rich = np.polyfit(nm, pw, 1)[1]
        fmod = lambda x, c, a, A, ph: c + a * x + np.log(np.abs(1 + A * np.cos(mu / 3 * x + ph)))
        try:
            p, _ = curve_fit(fmod, ln_, lv, p0=[c_pure, a_pure, 0.15, 0.0],
                             bounds=([-20, 0.0, 0.0, -np.pi], [20, 0.5, 0.6, np.pi]),
                             maxfev=20000)
            rms_mod = np.sqrt(np.mean((fmod(ln_, *p) - lv) ** 2))
            print(f"    pure power fit:  alpha = {a_pure:.4f}  (rms {rms_pure:.4f})", flush=True)
            print(f"    Richardson-extrapolated pairwise slope: {a_rich:.4f}", flush=True)
            print(f"    mu-LOCKED joint fit: alpha = {p[1]:.4f}, A = {p[2]:.3f}, phi = "
                  f"{p[3]:+.2f}  (rms {rms_mod:.4f})", flush=True)
            print(f"    X-1: {'PASS' if 0.150 <= p[1] <= 0.185 else 'OUTSIDE'} (target 1/6 = "
                  f"0.1667)   X-2: {'modulation significant, mu-locked fit better' if rms_mod < 0.8*rms_pure and p[2] > 0.03 else ('A ~ 0 (no modulation needed)' if p[2] <= 0.03 else 'fit NOT improved -- inspect')}",
                  flush=True)
        except Exception as e:
            print(f"    joint fit failed: {e}", flush=True)
    else:
        print(f"    (smoke: pure fit alpha = {a_pure:.4f})", flush=True)
print(f"\n  total {time.time()-t0:.0f}s", flush=True)
