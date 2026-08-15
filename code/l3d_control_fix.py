import numpy as np, time
print("=" * 100)
print("T3-1' CONTROL FIX -- registered: same-N scan, interpolated r_c value, fixed-reference norm")
print("""  The dirty 2D control had three artifacts: N changed mid-scan (800->1600), nearest-point
  sampling, max-normalization (the max migrates with Re).  Fix: N=1600 throughout, linear
  interpolation at r_c, normalize by |u_r(2.5)| (fixed reference radius away from the layer).
  REGISTERED: F-1 2D alpha in [-0.08, +0.08] (constant -- clean control);
              F-2 3D alpha stays in [0.08, 0.25] under the identical improvements.""")
t0 = time.time()
exec(open("code/l3d_indicial_gate.py").read().split("def expfit")[0].split('""", flush=True)')[1])
S, M = 0.5, 1


def layerval2(q, Re, N):
    A, B, r = sector(M, q, Re, N)
    f = np.zeros(4 * N, complex)
    f[0:N] = r * np.exp(-r ** 2)
    x = np.linalg.solve(A + 1j * S * B, f)
    ur = np.abs(x[0:N])
    Om = (1 - np.exp(-r ** 2)) / r ** 2
    rc = np.interp(S, (M * Om)[::-1], r[::-1])
    v = np.interp(rc, r, ur)
    ref = np.interp(2.5, r, ur)
    return v / ref


for q, nm, band in ((1.5, "3D", (0.08, 0.25)), (0.0, "2D", (-0.08, 0.08))):
    vals, nus = [], []
    for Re in (8000, 32000, 128000, 512000):
        v = layerval2(q, Re, 1600)
        vals.append(v)
        nus.append(2 * np.pi / Re)
        print(f"  {nm} Re={Re}: |u_r(r_c)|/|u_r(2.5)| = {v:.4f}", flush=True)
    al = np.polyfit(np.log(nus), np.log(vals), 1)[0]
    print(f"  {nm} fitted alpha = {al:+.3f}   band {band}: "
          f"{'PASS' if band[0] <= al <= band[1] else 'FAIL/inspect'}", flush=True)
print(f"  total {time.time()-t0:.0f}s", flush=True)
