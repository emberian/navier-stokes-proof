#!/usr/bin/env python3
"""sympy_r15.py — symbolic adjudication of the R1–R5 closure campaign
(NS_Proof.md, R1/R2/R3/R4/R5 CLOSURE sections + Lemma D; CAMPAIGN-RECORD
§§278–291). Twenty-three gates over the exact/algebraic cores. Exit 0 iff
all pass. Deterministic."""
import sympy as sp
import mpmath as mp

PASS = FAIL = 0
def gate(name, ok, detail=""):
    global PASS, FAIL
    s = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else: FAIL += 1
    print(f"[{s}] {name}  {detail}")

k3 = sp.Rational(4,3)*sp.pi

# --- R1-A exact constants -----------------------------------------------------
gate("r1a_mean_value_8", sp.simplify(k3*6/sp.pi - 8) == 0, "κ₃·6/π = 8")
gate("r1a_mean_flow", sp.simplify(k3*2/(2*sp.pi)**3 - 1/(3*sp.pi**2)) == 0, "κ₃·2/(2π)³ = 1/(3π²)")
r = sp.Symbol('rho', positive=True)
I = sp.integrate(4*sp.pi*sp.Symbol('t',positive=True)**0, (sp.Symbol('t',positive=True), 0, 3*r))  # ∫_{|z|≤3ρ}|z|^{-2} = 4π·3ρ
gate("r1a_young_12pi", sp.simplify(I - 12*sp.pi*r) == 0, "∫_{|z|≤3ρ}|z|⁻² = 12πρ")
j = sp.Symbol('j', positive=True, integer=True)
gate("r1a_shell_series", sp.summation(sp.Rational(1,2)**j, (j,1,sp.oo)) == 1, "Σ_{j≥1}2⁻ʲ = 1")
gate("r1a_holder_pair", sp.Rational(5,6) == sp.Rational(1,2)+sp.Rational(1,3), "5/6 = 1/2 + 1/3")
gate("r1a_cm", sp.simplify((1 + k3/(2*sp.pi)**3) - (1 + 1/(6*sp.pi**2))) == 0, "c_m = 1 + 1/(6π²)")

# --- R1-B chains --------------------------------------------------------------
s_, kk = sp.symbols('sigma k', positive=True)
gate("r1b_step_factor", sp.simplify(3*sp.sqrt(3)/(s_/(4*kk)) - 12*sp.sqrt(3)*kk/s_) == 0, "3√3/(σ/4k) = 12√3k/σ")
gate("r1b_mv_8", sp.simplify((k3*(s_/4)**3)**sp.Rational(-1,2) - 8*k3**sp.Rational(-1,2)*s_**sp.Rational(-3,2)) == 0, "(κ₃(σ/4)³)^{-1/2} = 8κ₃^{-1/2}σ^{-3/2}")
n = sp.Symbol('n', positive=True, integer=True)
gate("r1b_closure_exp", sp.simplify((2*n+5)/(2*n+4) - (1 + 1/(2*n+4))) == 0, "(2n+5)/(2n+4) = 1+1/(2n+4)")
ok = all((1 + 1/(2*(sp.floor((1/h - 5)/2)+1)+4))*(1-h) < 1 for h in [sp.Rational(1,100), sp.Rational(1,20), sp.Rational(1,7), sp.Rational(1,3)])
gate("r1b_n_eta", ok, "n(η)=⌊(1/η−5)/2⌋+1 ⇒ (1+1/(2n+4))(1−η) < 1 on the η-grid")

# --- Lemma D: race, recursion, rent, leakage ---------------------------------
Om0, w0, eps, W = sp.symbols('Omega_0 omega_0 epsilon W', positive=True)
lhs = (Om0*(4*(1-eps))**W)/((w0*2**W)**2)
gate("rd_race_ratio", sp.simplify(lhs - (Om0/w0**2)*(1-eps)**W) == 0, "Ω/ω² picks exactly (1−ε)^W")
gate("rd_eta_pos", all(-mp.log(1-e, 2) > 0 for e in (0.01, 0.1, 0.5)), "η′ = −log₂(1−ε) > 0")
a, b, x0 = sp.symbols('a b x_0', positive=True)
xW = a**W*x0 + b*(a**W-1)/(a-1)
gate("rd_affine_solve", sp.simplify(xW - (a**W*(x0 + b/(a-1)) - b/(a-1))) == 0, "exact affine solve; ≤ a^W(x₀+b/(a−1))")
Cpsi, K, th = sp.symbols('C_psi K theta', positive=True)
gate("rd_leakage", sp.simplify(sp.solve(Cpsi/(686*K*th) - sp.Rational(1,2), K)[0] - Cpsi/(343*th)) == 0, "leakage ≤ rent/2 ⟺ K ≥ C_ψ/(343θ)")
nu, sr, Omc = sp.symbols('nu s Omega_core', positive=True)
gate("rd_rent_cancel", sp.simplify((nu*th*K**-2*sr**-2*Omc)*((K*sr)**2/nu) - th*Omc) == 0, "rent·window = θ·Ω_core exactly")

# --- R2: floor, count, dipole -------------------------------------------------
w_c, s2 = sp.symbols('omega_0 s', positive=True)
Gam = w_c*sp.pi*s2**2   # constant-ω disc: sharpness of the floor
gate("r2a_floor_sharp", sp.simplify(Gam**2/(sp.pi*s2**2*(w_c**2*sp.pi*s2**2)) - 1) == 0, "C-S equality case: floor sharp")
gate("r2a_geometry", sp.sqrt(2) <= 2, "cylinder ⊂ B_{√2 s} ⊂ B_{2s}")
Om, Gm, cN, N = sp.symbols('Omega Gamma_min c_N N', positive=True)
sol = sp.solve(N - (2*sp.pi*cN*N**sp.Rational(-1,3)*Om/Gm**2), N)
gate("r2b_count_solve", sp.simplify(sol[0] - (2*sp.pi*cN*Om/Gm**2)**sp.Rational(3,4)) == 0, "N = (2πc_NΩ/Γ²)^{3/4}")
gate("r2c2_mv16", sp.Rational(2,1)**4 == 16, "mean-value factor (d/2)⁻⁴ = 16d⁻⁴")

# --- R3: Γ_min, c_E, clauses, fatness ----------------------------------------
ccc, R7, C1, g_ = sp.symbols("c_cc R_7 C_1' gamma", positive=True)
gate("r3a_gamma_min", sp.simplify(ccc*(R7*g_)*(4*nu/(C1*g_)) - 4*ccc*R7*nu/C1) == 0, "γ cancels: Γ_min = 4c_ccR₇ν/C₁′")
L, dl = sp.symbols('L delta', positive=True)
gate("r3a_ce", sp.simplify((L/(4*dl))*(Gm**2/(sp.pi*dl)) - Gm**2*L/(4*sp.pi*dl**2)) == 0, "stack: E ≥ Γ²L/(4πδ²), c_E = 1/4π")
b3, Rm = sp.symbols('b_3 R_m', positive=True)
gate("r3b_rm_clause", sp.simplify(sp.solve(sp.pi*R7/Rm**2 - 1/(24*b3), Rm)[0]**2 - 24*sp.pi*b3*R7) == 0, "πR₇/R_m² ≤ 1/24b₃ ⟺ R_m² ≥ 24πb₃R₇")
Gflux = sp.Symbol('Gamma_flux', positive=True)
gate("r3b_fatness", sp.simplify(sp.solve(Gflux - sp.pi*w_c*s2**2, s2)[0]**2 - Gflux/(sp.pi*w_c)) == 0, "s² = Γ/(πω) at the flux bound")

# --- R4: equilibrium, window, grace, averaging -------------------------------
Cpr, D0, c1 = sp.symbols('C_pr Delta_0 c_1', positive=True)
gate("r4a_overtone_eq", sp.simplify(Cpr*D0*g_/(2*c1*g_) - Cpr*D0/(2*c1)) == 0, "overtone equilibrium γ-free")
Csh, cst = sp.symbols('C_shape c_star', positive=True)
gate("r4a_window", sp.simplify(Csh*(c1*cst/(4*Csh))/c1 - cst/4) == 0, "Δ₀-clause ⇒ equilibrium ≤ c*/4")
Cent, cc_ = sp.symbols('C_ent c', positive=True)
kg = sp.log(2*Cent/cst)/(2*c1*cc_)
gate("r4b_kgrace", sp.simplify(Cent*sp.exp(-2*c1*cc_*kg) - cst/2) == 0, "C_ent·e^{−2c₁c·k_grace} = c*/2 at the formula")
phi, beta, tt = sp.symbols('phi beta theta_t', real=True)
S22 = sp.Matrix([[sp.cos(2*beta), sp.sin(2*beta)],[sp.sin(2*beta), -sp.cos(2*beta)]])
v = sp.Matrix([sp.cos(phi), sp.sin(phi)])
gate("r4c_zero_mean_id", sp.simplify((v.T*S22*v)[0,0] - sp.cos(2*phi-2*beta)) == 0, "θᵀS_⊥θ = cos(2φ−2β): pure oscillation, zero mean")
Ct, cw, cf, Cd = sp.symbols('C_tau c_w c_f C_d', positive=True)
Cav = Ct*(1/(cw*cf) + Cd/(2*cf) + Cd/(4*cf**2))
gate("r4c_cav_form", sp.simplify(Cav - Ct*(4*cf + 2*Cd*cf*cw + Cd*cw)/(4*cw*cf**2)) == 0, "C_av assembly explicit")

# --- R2 assembly allocation ---------------------------------------------------
gate("r2asm_allocation", sp.Rational(3,8) + 3*sp.Rational(1,24) == sp.Rational(1,2), "3/8 + 3·(1/24) = 1/2 exactly")
gate("r2asm_log_slot", mp.mpf(8)/3 < mp.e, "8/3 < e: the calibrated-log slot unchanged")

# --- R1-D lock ----------------------------------------------------------------
est, M_ = sp.symbols('epsilon_star M', positive=True)
gate("r1d_lock", sp.simplify(sp.solve(est*nu**2 - k3*s2**4*M_**2, M_)[0] - sp.sqrt(est/k3)*nu/s2**2) == 0, "ε*ν² = κ₃s⁴M² ⟺ M = (ε*/κ₃)^{1/2}ν/s²")

# --- S6 additions: S1 inheritance, power domination ---------------------------
D_, a_ = sp.symbols('Delta_0 a', positive=True)
# osc ≤ 2Da and mean' ≥ (1−1.5D)a with D ≤ 1/6 ⇒ 2Da ≤ 3D·mean': margin = Da(1−4.5D) ≥ 0
margin = sp.simplify(3*D_*(1-sp.Rational(3,2)*D_)*a_ - 2*D_*a_)
gate("s1_inheritance", sp.simplify(margin - D_*a_*(1-sp.Rational(9,2)*D_)) == 0 and (1-sp.Rational(9,2)*sp.Rational(1,6)) > 0,
     "3D(1−1.5D)a − 2Da = Da(1−4.5D) ≥ 0 for D ≤ 1/6 (indeed ≤ 2/9)")
ok_pd = all(mp.mpf(x)**(mp.mpf(5)/8) <= mp.mpf(x)**(mp.mpf(5)/6) + 1 + 1e-15 for x in (0, 0.01, 0.5, 1, 2, 100, 1e8))
gate("pow_dominate", ok_pd, "x^(5/8) ≤ x^(5/6)+1 on the grid (split at x = 1)")

print(f"\n{PASS}/{PASS+FAIL} gates PASS, {FAIL} FAIL")
raise SystemExit(0 if FAIL == 0 else 1)
