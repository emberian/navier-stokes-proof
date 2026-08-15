import numpy as np
np.set_printoptions(suppress=True)
N0, N, NU = 64, 128, 0.006
print("STRAIN SPLIT -- does the Burgers law close EXACTLY with the AMBIENT-strain ruler?")
print("""  The tracked worm: R = alpha_total*delta^2/(4nu) = 1.85 stable.  Lemmas 3/5 predict the
  contraction is driven by the AMBIENT strain only (self-strain of the bent worm does not
  contract the core).  Parameter-free: alpha_amb should = 4nu/delta^2 = 0.327 (alpha_total
  0.648).  REGISTERED: SS-1 R_amb = alpha_amb*delta^2/(4nu) in [0.65, 1.35] -> the law closes
  exactly with the correct ruler; the excess is the measured self-term.  FAIL -> fat core is
  physical, recorded.""")
U64 = np.load("results/l19_field_t8_N64.npy")
k1 = np.fft.fftfreq(N, d=1.0/N)
KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K2 = KX**2 + KY**2 + KZ**2
K2s = np.where(K2 == 0, 1, K2)
def up(u):
    out = np.zeros((N, N, N), complex); h = N0//2
    ix = np.r_[0:h, N-h:N]; src = np.r_[0:h, N0-h:N0]
    out[np.ix_(ix, ix, ix)] = u[np.ix_(src, src, src)]
    return out*(N/N0)**3
U = [up(c) for c in U64]
cur = lambda V: [1j*(KY*V[2]-KZ*V[1]), 1j*(KZ*V[0]-KX*V[2]), 1j*(KX*V[1]-KY*V[0])]
Wh = cur(U)
wr = [np.real(np.fft.ifftn(c)) for c in Wh]
wm = np.sqrt(sum(c**2 for c in wr))
i0 = (80, 93, 104)
BOX = 10
idx = [(np.arange(-BOX, BOX+1)+i0[a]) % N for a in range(3)]
BX, BY, BZ = np.meshgrid(*idx, indexing='ij')
sub = wm[BX, BY, BZ]; wpk = sub.max()
maskf = np.zeros((N, N, N))
mloc = sub >= 0.5*wpk
maskf[BX, BY, BZ] = mloc
maskf = np.real(np.fft.ifftn(np.exp(-0.5*K2*(2*np.pi/N)**2)*np.fft.fftn(maskf)))  # 1-cell taper
Wc = [np.fft.fftn(c*maskf) for c in wr]
# solenoidal BS: u_hat = i k x w_hat / k^2
def bsvel(Wh_):
    return [1j*(KY*Wh_[2]-KZ*Wh_[1])/K2s, 1j*(KZ*Wh_[0]-KX*Wh_[2])/K2s,
            1j*(KX*Wh_[1]-KY*Wh_[0])/K2s]
Uc = bsvel(Wc)
def strain_at(V):
    G = np.zeros((21, 21, 21, 3, 3))
    for i in range(3):
        for kk in range(3):
            gi = np.real(np.fft.ifftn(1j*(KX, KY, KZ)[kk]*V[i]))
            G[..., kk, i] = gi[BX, BY, BZ]
    return 0.5*(G+np.transpose(G, (0, 1, 2, 4, 3)))
St = strain_at(U); Sc = strain_at(Uc)
wv = np.stack([c[BX, BY, BZ] for c in wr], axis=-1)
xi = wv/np.maximum(np.sqrt((wv**2).sum(-1)), 1e-300)[..., None]
w2 = (sub**2)*mloc
alt = (w2*np.einsum('xyzi,xyzij,xyzj->xyz', xi, St, xi)).sum()/w2.sum()
als = (w2*np.einsum('xyzi,xyzij,xyzj->xyz', xi, Sc, xi)).sum()/w2.sum()
ala = alt - als
d2 = 0.0734
Ramb = ala*d2/(4*NU)
print(f"  alpha_total = {alt:.3f}   alpha_self = {als:.3f}   alpha_ambient = {ala:.3f}   "
      f"(predicted ambient for exact closure: {4*NU/d2:.3f})")
print(f"  SS-1: R_amb = {Ramb:.2f}   "
      f"({'PASS -- the Burgers law closes EXACTLY with the ambient ruler; the excess IS the self-term' if 0.65 <= Ramb <= 1.35 else 'FAIL -- fat core physical, recorded'})")
