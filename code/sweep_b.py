import os
print("SWEEP B -- the number trace: every headline figure in NS_Proof.md walked to its log line")
print("  verdicts: FOUND (string present in the canonical log) / MISSING (flag, triage)")
CHECKS = [
 # (claimed figure, canonical log, context)
 ("0.387", "l14_residual_gate.log", "R-1b residual exponent"),
 ("2.39522", "l14_residual_gate.log", "wrong-branch Plemelj floor"),
 ("0.35988", "l16_block_gate2.log", "resonance frequency vs r2_anatomy"),
 ("idem 4.54e-15", "l16_block_gate2.log", "Riesz idempotency machine precision"),
 ("3.26", "l16_block_gate2.log", "c_K isolated resonance"),
 ("0.01655", "l16_block_gate3.log", "grower rate (vs S5-2 0.0166)"),
 ("3.38", "l16_block_gate3.log", "crossing damping c"),
 ("0.0366", "l16_block_gate3.log", "detuning Delta"),
 ("0.175", "l3d_control_fix.log", "3D layer exponent (superseded by exact)"),
 ("0.0028", "l3d_exact_fit2.log", "locked-exact rms s=0.5"),
 ("0.0183", "l3d_exact_fit2.log", "free rms s=0.7"),
 ("b = 2.14", "l3d_exact_fit2.log", "1/6-locked correction coeff s=0.5"),
 ("b = 2.78", "l3d_exact_fit2.log", "1/6-locked correction coeff s=0.7"),
 ("1.9710", "l3d_exact_gate.log", "exact mu at s=0.5"),
 ("0.286", "l17_worm_gate.log", "W-1 veto ratio on the worm"),
 ("19.6", "l17_worm_gate.log", "fast/slow margin"),
 ("0.887", "l17_worm_gate.log", "core nematic C_n"),
 ("alpha_self = 0.074", "l17_strain_split.log", "the veto split (11%)"),
 ("alpha_total = 0.648", "l17_strain_split.log", "total alpha"),
 ("1.87", "l17_profile_ruler.log", "F4 (retracted claim's raw number, kept as data)"),
 ("p = 0.87", "l17_profile_cut.log", "direct-cut profile exponent ray1"),
 ("R = 1.32", "l17_profile_cut.log", "W-2 exact-standard ratio (canonical)"),
 ("0.4242", "l19r_gate.log", "basin P recovery"),
 ("0.6793", "l19r_gate.log", "basin C_n recovery"),
 ("1.44", "l19r3_gate.log", "fragility ratio (first lag)"),
 ("0.818", "l19r3_gate.log", "production variance share"),
 ("-2", "sympy_w4.log", "Gram <r,W'> = -2 exact"),
 ("g_delta = <r^2 moment, dU/d(delta2)> = 1", "sympy_w4.log", "Gram dilation = 1"),
 ("1/2 - log(2)/3", "sympy_rulers.log", "calibration closed form"),
 ("match: True", "sympy_rulers.log", "moment law from the strained flow"),
 ("2*pi*r**2", "sympy_w23.log", "W2 parity integral"),
 ("4*pi/(5*r**5)", "sympy_w1.log", "W1 main tail"),
 ("7*pi/(6*r**3)", "sympy_w1.log", "W1 annulus"),
 ("4*pi/(7*r**7)", "sympy_w89.log", "W8 kernel tail"),
 ("4/3", "sympy_w89.log", "W9 shell series"),
 ("q*(1 - q)", "sympy_w6.log", "W6 closure factored form"),
 ("0.680", "l16_block_gate3.log", "effective (sigma+d)/eps in banked bracket"),
]
found = missing = 0
for num, log, ctx in CHECKS:
    path = os.path.join("results", log)
    ok = os.path.exists(path) and (num in open(path, errors="ignore").read())
    tag = "FOUND  " if ok else "MISSING"
    found += ok; missing += (not ok)
    if not ok:
        print(f"  {tag} | {num:<42} | {log:<26} | {ctx}")
print(f"\n  SWEEP B: {found}/{len(CHECKS)} traced to canonical logs; {missing} flagged")
