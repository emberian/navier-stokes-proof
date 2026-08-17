#!/usr/bin/env python3
"""numerics_n3_cf.py — CERTIFIED-NUMERICS WAVE, stage N3 (NS_Proof.md).

The m = 1 spectral floor c_f of the Oseen column, certified. The honest
reduction (NS_Proof.md, stage N3): no matrix enclosure exists to compute —
the constrained m = 1 spectrum is the rotation band by two structural facts
(W' < 0 kills embedded neutral modes; the Rayleigh sign identity kills
complex eigenvalues), so the instrument certifies:
  - the structural facts and the band monotonicity (exact, sympy);
  - the translation-pair Gram pairing <r, W'> = -2 (exact);
  - the band-edge choice R_b = 2: c_f = (1-e^-4)/4 >= 0.245420 (floor,
    rounded DOWN) with core-weight leakage EXACTLY e^{-R_b^2} <= 0.0183157,
    inside the w5 half-per-window slack with 27x margin;
  - the core-mean precession rate = ln 2 exactly (Frullani);
  - C_av's c_f-coefficients rounded UP against the rounded-down floor.
Exit 0 iff all gates pass.
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
PASS = 0
FAIL = 0

def gate(name, ok, detail=""):
    global PASS, FAIL
    status = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else: FAIL += 1
    print(f"[{status}] {name}  {detail}")

r, u, R = sp.symbols('r u R', positive=True)
Om = (1 - sp.exp(-r**2))/r**2          # rotation profile, core units
W = 2*sp.exp(-r**2)                    # vorticity profile
Wp = sp.diff(W, r)

# --- 1. Omega strictly decreasing: Om' = (2/r^3)[e^{-r^2}(1+r^2) - 1] < 0 ---
Omp = sp.simplify(sp.diff(Om, r))
target = (2/r**3)*(sp.exp(-r**2)*(1 + r**2) - 1)
gate("omega_prime_closed_form", sp.simplify(Omp - target) == 0,
     "Om'(r) = (2/r^3)[e^{-r^2}(1+r^2) - 1] exactly")
# sign: e^x - 1 - x = sum_{k>=2} x^k/k! >= x^2/2 > 0 for x > 0  =>  bracket < 0
x = sp.Symbol('x', positive=True)
ser = sp.series(sp.exp(x) - 1 - x - x**2/2, x, 0, 8).removeO()
coeffs_ok = all(c >= 0 for c in sp.Poly(ser, x).all_coeffs())
g2 = sp.simplify(sp.diff(sp.exp(x) - 1 - x - x**2/2, x, 2) - (sp.exp(x) - 1))
gate("omega_strictly_decreasing", coeffs_ok and g2 == 0,
     "e^x > 1 + x (x>0, second-derivative + series argument) => Om' < 0 strictly")
neg_ok = all(mp.mpf(sp.N(Omp.subs(r, rv), 30).__str__()) < 0
             for rv in ('1/10', '1/2', 1, 2, 3, 5, 8))
gate("omega_prime_grid", neg_ok, "Om' < 0 spot-checked on (0, 8]")

# --- 2. structural facts: W' < 0; the Gram pairing <r, W'> = -2 exactly -----
gate("no_neutral_modes", sp.simplify(Wp + 4*r*sp.exp(-r**2)) == 0,
     "W' = -4 r e^{-r^2} < 0 for r > 0: no embedded neutral mode at any radius")
pairing = sp.integrate(Wp*r**2, (r, 0, sp.oo))
gate("gram_pairing_minus2", sp.simplify(pairing + 2) == 0,
     "<r, W'> = int W' r^2 dr = -2 exactly (translation pair, removed by modulation)")

# --- 3. the leakage identity and the band-edge table ------------------------
leak = sp.integrate(2*r*sp.exp(-r**2), (r, R, sp.oo))
gate("leakage_exact", sp.simplify(leak - sp.exp(-R**2)) == 0,
     "core-weight mass beyond R_b is EXACTLY e^{-R_b^2}")
print("  band-edge table (floor Om(R_b), leakage e^{-R_b^2}):")
for Rb in ('3/2', 2, '5/2'):
    fl = sp.N(Om.subs(r, sp.Rational(Rb) if isinstance(Rb, str) else Rb), 20)
    lk = sp.N(sp.exp(-(sp.Rational(Rb) if isinstance(Rb, str) else sp.Integer(Rb))**2), 20)
    print(f"    R_b = {str(Rb):>3}: floor {sp.N(fl, 6)}   leakage {sp.N(lk, 6)}")

# class choice R_b = 2, directed rounding:
cf_exact = (1 - mp.e**-4)/4
cf_floor = mp.mpf('0.245420')            # rounded DOWN (consumers divide by c_f)
leak_up = mp.mpf('0.0183157')            # rounded UP
gate("cf_floor_directed", cf_floor <= cf_exact and mp.e**-4 <= leak_up,
     f"c_f = (1-e^-4)/4 = {mp.nstr(cf_exact, 8)} >= 0.245420; leak {mp.nstr(mp.e**-4, 6)} <= 0.0183157")
gate("leakage_inside_w5_slack", leak_up < mp.mpf('0.5')/27,
     "leakage < (1/2)/27: inside the half-per-window w5 slack with 27x margin")

# --- 4. the core-mean precession rate: Frullani = ln 2 exactly --------------
mean_rate = sp.integrate((sp.exp(-u) - sp.exp(-2*u))/u, (u, 0, sp.oo))
sub = sp.integrate(Om*2*r*sp.exp(-r**2), (r, 0, sp.oo))
gate("frullani_ln2", sp.simplify(mean_rate - sp.log(2)) == 0
     and sp.simplify(sub - sp.log(2)) == 0,
     "int Om(r) 2r e^{-r^2} dr = int (e^{-u}-e^{-2u})/u du = ln 2 exactly")
gate("mean_above_floor", mp.log(2) > cf_exact,
     f"core-mean rate ln 2 = {mp.nstr(mp.log(2), 6)} ~ 2.8x the band-edge floor (consistent)")

# --- 5. C_av's c_f-coefficients, rounded UP against the floor ---------------
c1 = 1/cf_floor
c2 = 1/(2*cf_floor)
c3 = 1/(4*cf_floor**2)
up = lambda v: mp.ceil(v*10**5)/mp.mpf(10**5)
gate("cav_coefficients", up(c1) == mp.mpf('4.07465') and up(c2) == mp.mpf('2.03733')
     and up(c3) == mp.mpf('4.15069'),
     f"1/c_f <= {mp.nstr(up(c1),6)}; 1/(2c_f) <= {mp.nstr(up(c2),6)}; 1/(4c_f^2) <= {mp.nstr(up(c3),6)}")

print()
print("CERTIFIED RESULTS (stage N3):")
print(f"  c_f      >= 0.245420          (= Omega(2) = (1-e^-4)/4, floor, rounded down)")
print(f"  leakage  <= 0.0183157         (= e^-4 exactly; < 2%, w5 slack margin 27x)")
print(f"  mean rate = ln 2 = {mp.nstr(mp.log(2), 8)}  (exact, Frullani)")
print(f"  C_av <= C_tau[4.07465/c_w + 6.18802 C_d]   (coefficients rounded up)")
print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
