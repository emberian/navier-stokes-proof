import numpy as np, scipy.linalg as sla, time
np.set_printoptions(suppress=True)
print("KAPPA-BARE Q-SCAN -- locate the band center (Delta -> 0), then the exact slope")
print("""  REGISTERED: Q-1 interior max of the grower rate over q in {2.0,2.1,2.2,2.3,2.4}
  (eps=0.04, Re=2000, N=200); Q-2 kappa_bare = (sigma(0.04)-sigma(0.02))/0.02 at q* -- the
  detuning-free coupling (replaces the provisional 1.13; Floquet ideal 0.5624 + finite-core
  corrections expected).""")
t0 = time.time()
src = open("code/l16_block_gate3.py").read()
body = src.split("EPS = ")[0]                      # defs: sector, cblock, spec
body = body[body.index("def sector"):]
exec(body)
Re0, N = 2000, 200
best = (None, -1)
for q in (2.0, 2.1, 2.2, 2.3, 2.4):
    ev, _, _ = spec(0.04, q, Re0, N)
    s = ev.real.max()
    print(f"  q={q}: max Re lam = {s:+.5f}", flush=True)
    if s > best[1]:
        best = (q, s)
qs, smax = best
ev2, _, _ = spec(0.02, qs, Re0, N)
s2 = ev2.real.max()
kb = (smax - s2) / 0.02
print(f"  Q-1 band center q* = {qs}   ({'PASS -- interior' if qs not in (2.0, 2.4) else 'EDGE -- widen'})")
print(f"  Q-2 kappa_bare at q* = {kb:.4f}   (provisional fit 1.13; Floquet ideal 0.5624)")
print(f"  total {time.time()-t0:.0f}s")
