(* The ideal I_0 of the Z2-graded-commutative ring S for N=4 SYM with gauge algebra su(3) (2d VOA with c = -24),
   such that R = S / I_0 underlies the Schur and Macdonald indices via HS_{q,q,T,-1}(gr J_infinity(S / I_0)).

   The relations are the derivative-free parts (Li-grade zero) of the null operators of the VOA up to and including
   conformal dimension 4, computed from the free-field realization; listed are the 59 minimal generators.

   Products are written with ** in a fixed order; the fermionic coordinates anticommute and the bosonic ones commute.
   The relations are homogeneous in the q-grading and in the su(2) flavor charge a, but not in the T-grading. *)

N4SU3Generators = {
  {t, "T", h -> 2, T -> 1, a -> 0, F -> 0},
  {j0, "K^3", h -> 1, T -> 1, a -> 0, F -> 0},
  {jp, "K^+", h -> 1, T -> 1, a -> 2, F -> 0},
  {jm, "K^-", h -> 1, T -> 1, a -> -2, F -> 0},
  {gpp, "G^{++}", h -> 3/2, T -> 1/2, a -> 1, F -> 1},
  {gpm, "G^{+-}", h -> 3/2, T -> 1/2, a -> -1, F -> 1},
  {gmp, "G^{-+}", h -> 3/2, T -> 3/2, a -> 1, F -> 1},
  {gmm, "G^{--}", h -> 3/2, T -> 3/2, a -> -1, F -> 1},
  {w[-3/2], "W_{-3/2}", h -> 3/2, T -> 3/2, a -> -3, F -> 0},
  {w[-1/2], "W_{-1/2}", h -> 3/2, T -> 3/2, a -> -1, F -> 0},
  {w[1/2], "W_{+1/2}", h -> 3/2, T -> 3/2, a -> 1, F -> 0},
  {w[3/2], "W_{+3/2}", h -> 3/2, T -> 3/2, a -> 3, F -> 0},
  {wp[-1], "W^+_{-1}", h -> 2, T -> 1, a -> -2, F -> 1},
  {wp[0], "W^+_0", h -> 2, T -> 1, a -> 0, F -> 1},
  {wp[1], "W^+_{+1}", h -> 2, T -> 1, a -> 2, F -> 1},
  {wm[-1], "W^-_{-1}", h -> 2, T -> 2, a -> -2, F -> 1},
  {wm[0], "W^-_0", h -> 2, T -> 2, a -> 0, F -> 1},
  {wm[1], "W^-_{+1}", h -> 2, T -> 2, a -> 2, F -> 1},
  {wu[-1/2], "W^{up}_{-1/2}", h -> 5/2, T -> 3/2, a -> -1, F -> 0},
  {wu[1/2], "W^{up}_{+1/2}", h -> 5/2, T -> 3/2, a -> 1, F -> 0}
};

N4SU3Fermions = {gpp, gpm, gmp, gmm, wp[-1], wp[0], wp[1], wm[-1], wm[0], wm[1]};

N4SU3Ideal = {
  wu[-1/2] - 1/3 j0 ** w[-1/2] + 1/3 jp ** w[-3/2] + 2/3 jm ** w[1/2],
  wu[1/2] - 2/3 j0 ** w[1/2] + 1/3 jp ** w[-1/2] + 2 jm ** w[3/2],
  t ** j0 + 1/4 gpp ** gmm + 1/4 gpm ** gmp + 1/8 w[-3/2] ** w[3/2] - 1/24 w[-1/2] ** w[1/2] - 1/12 j0 ** j0 ** j0 + 1/3 j0 ** jp ** jm,
  t ** jp + 1/4 gpp ** gmp + 1/8 w[-1/2] ** w[3/2] - 1/12 w[1/2] ** w[1/2] - 1/12 j0 ** j0 ** jp + 1/3 jp ** jp ** jm,
  t ** jm + 1/4 gpm ** gmm + 1/24 w[-3/2] ** w[1/2] - 1/48 w[-1/2] ** w[-1/2] - 1/12 j0 ** j0 ** jm + 1/3 jp ** jm ** jm,
  j0 ** wp[-1] - 2 jm ** wp[0] - gpp ** w[-3/2] + gpm ** w[-1/2],
  j0 ** wp[0] - 4 jm ** wp[1] - gpp ** w[-1/2] + 2 gpm ** w[1/2],
  j0 ** wp[1] - jp ** wp[0] + gpp ** w[1/2] - 3 gpm ** w[3/2],
  j0 ** wm[-1] - 2 jm ** wm[0] - gmp ** w[-3/2] + gmm ** w[-1/2],
  j0 ** wm[0] - 4 jm ** wm[1] - gmp ** w[-1/2] + 2 gmm ** w[1/2],
  j0 ** wm[1] - jp ** wm[0] + gmp ** w[1/2] - 3 gmm ** w[3/2],
  jp ** wp[-1] - 2 jm ** wp[1] - gpp ** w[-1/2] + 2 gpm ** w[1/2],
  jp ** wm[-1] - 2 jm ** wm[1] - gmp ** w[-1/2] + 2 gmm ** w[1/2],
  t ** gpp - 1/12 w[1/2] ** wp[0] + 1/4 w[3/2] ** wp[-1] - 1/6 j0 ** j0 ** gpp + 1/6 j0 ** jp ** gpm + 1/3 jp ** jm ** gpp,
  t ** gpm - 1/12 w[-1/2] ** wp[0] + 1/6 w[1/2] ** wp[-1] - 1/3 j0 ** jm ** gpp + 2/3 jp ** jm ** gpm,
  t ** gmp - 1/12 w[1/2] ** wm[0] + 1/4 w[3/2] ** wm[-1] - 1/6 j0 ** j0 ** gmp + 1/6 j0 ** jp ** gmm + 1/3 jp ** jm ** gmp,
  t ** gmm - 1/12 w[-1/2] ** wm[0] + 1/6 w[1/2] ** wm[-1] - 1/3 j0 ** jm ** gmp + 2/3 jp ** jm ** gmm,
  t ** w[-3/2] + gpm ** wm[-1] - gmm ** wp[-1] + 2/3 j0 ** jm ** w[-1/2] - 2/3 jp ** jm ** w[-3/2] - 4/3 jm ** jm ** w[1/2],
  t ** w[-1/2] + gpm ** wm[0] - gmm ** wp[0] + 4/3 j0 ** jm ** w[1/2] - 2/3 jp ** jm ** w[-1/2] - 4 jm ** jm ** w[3/2],
  t ** w[1/2] + gpm ** wm[1] - gmm ** wp[1] + 2/3 j0 ** j0 ** w[1/2] - 2/3 j0 ** jp ** w[-1/2] - 2 j0 ** jm ** w[3/2] + 1/3 jp ** jp ** w[-3/2] + 2/3 jp ** jm ** w[1/2],
  t ** w[3/2] + 1/3 gpp ** wm[1] - 1/3 gmp ** wp[1] + 2/9 j0 ** jp ** w[1/2] - 1/9 jp ** jp ** w[-1/2] - 2/3 jp ** jm ** w[3/2],
  gpp ** wp[-1] - gpm ** wp[0],
  gpp ** wp[0] - 2 gpm ** wp[1],
  gpp ** wm[-1] - gpm ** wm[0] + 1/3 j0 ** j0 ** w[-1/2] - 1/3 j0 ** jp ** w[-3/2] - 2 j0 ** jm ** w[1/2] + 2/3 jp ** jm ** w[-1/2] + 4 jm ** jm ** w[3/2],
  gpp ** wm[0] - 2 gpm ** wm[1] - 2/3 j0 ** j0 ** w[1/2] + j0 ** jp ** w[-1/2] + 2 j0 ** jm ** w[3/2] - 2/3 jp ** jp ** w[-3/2] - 4/3 jp ** jm ** w[1/2],
  gmp ** wp[-1] - gmm ** wp[0] - 1/3 j0 ** j0 ** w[-1/2] + 1/3 j0 ** jp ** w[-3/2] + 2 j0 ** jm ** w[1/2] - 2/3 jp ** jm ** w[-1/2] - 4 jm ** jm ** w[3/2],
  gmp ** wp[0] - 2 gmm ** wp[1] + 2/3 j0 ** j0 ** w[1/2] - j0 ** jp ** w[-1/2] - 2 j0 ** jm ** w[3/2] + 2/3 jp ** jp ** w[-3/2] + 4/3 jp ** jm ** w[1/2],
  gmp ** wm[-1] - gmm ** wm[0],
  gmp ** wm[0] - 2 gmm ** wm[1],
  w[-3/2] ** wp[0] - w[-1/2] ** wp[-1] - 4 j0 ** jm ** gpm + 8 jm ** jm ** gpp,
  w[-3/2] ** wp[1] + 1/2 w[-1/2] ** wp[0] - 2 w[1/2] ** wp[-1] - 2 j0 ** j0 ** gpm + 6 j0 ** jm ** gpp - 4 jp ** jm ** gpm,
  w[-3/2] ** wm[0] - w[-1/2] ** wm[-1] - 4 j0 ** jm ** gmm + 8 jm ** jm ** gmp,
  w[-3/2] ** wm[1] + 1/2 w[-1/2] ** wm[0] - 2 w[1/2] ** wm[-1] - 2 j0 ** j0 ** gmm + 6 j0 ** jm ** gmp - 4 jp ** jm ** gmm,
  w[-1/2] ** wp[1] - 1/2 w[1/2] ** wp[0] - 3/2 w[3/2] ** wp[-1] + j0 ** j0 ** gpp - 3 j0 ** jp ** gpm + 2 jp ** jm ** gpp,
  w[-1/2] ** wm[1] - 1/2 w[1/2] ** wm[0] - 3/2 w[3/2] ** wm[-1] + j0 ** j0 ** gmp - 3 j0 ** jp ** gmm + 2 jp ** jm ** gmp,
  w[1/2] ** wp[1] - 3/2 w[3/2] ** wp[0] + j0 ** jp ** gpp - 2 jp ** jp ** gpm,
  w[1/2] ** wm[1] - 3/2 w[3/2] ** wm[0] + j0 ** jp ** gmp - 2 jp ** jp ** gmm,
  t ** t - 1/4 j0 ** gpp ** gmm - 1/4 j0 ** gpm ** gmp + 1/24 j0 ** w[-3/2] ** w[3/2] - 1/72 j0 ** w[-1/2] ** w[1/2] - 1/9 jp ** w[-3/2] ** w[1/2] + 1/18 jp ** w[-1/2] ** w[-1/2] + jm ** gpp ** gmp + 1/6 jm ** w[-1/2] ** w[3/2] - 1/9 jm ** w[1/2] ** w[1/2] - 1/36 j0 ** j0 ** j0 ** j0 + 2/9 j0 ** j0 ** jp ** jm - 4/9 jp ** jp ** jm ** jm,
  t ** wp[-1] + 1/3 j0 ** gpm ** w[-1/2] - 1/3 jp ** gpm ** w[-3/2] - 2/3 jm ** gpm ** w[1/2],
  t ** wp[0] + 2/3 j0 ** gpm ** w[1/2] - 1/3 jp ** gpm ** w[-1/2] - 2 jm ** gpm ** w[3/2],
  t ** wp[1] + 1/3 j0 ** gpp ** w[1/2] - 1/6 jp ** gpp ** w[-1/2] - jm ** gpp ** w[3/2],
  t ** wm[-1] + 1/3 j0 ** gmm ** w[-1/2] - 1/3 jp ** gmm ** w[-3/2] - 2/3 jm ** gmm ** w[1/2],
  t ** wm[0] + 2/3 j0 ** gmm ** w[1/2] - 1/3 jp ** gmm ** w[-1/2] - 2 jm ** gmm ** w[3/2],
  t ** wm[1] + 1/3 j0 ** gmp ** w[1/2] - 1/6 jp ** gmp ** w[-1/2] - jm ** gmp ** w[3/2],
  wp[-1] ** wp[0] - 4 jm ** gpp ** gpm,
  wp[-1] ** wp[1] - 2 j0 ** gpp ** gpm,
  wp[-1] ** wm[-1] + 1/3 j0 ** w[-3/2] ** w[-1/2] - 1/3 jp ** w[-3/2] ** w[-3/2] + 2 jm ** gpm ** gmm - jm ** w[-3/2] ** w[1/2] + 1/6 jm ** w[-1/2] ** w[-1/2] + 2/3 j0 ** j0 ** jm ** jm - 8/3 jp ** jm ** jm ** jm,
  wp[-1] ** wm[0] + 1/3 j0 ** w[-1/2] ** w[-1/2] - 1/3 jp ** w[-3/2] ** w[-1/2] - jm ** gpp ** gmm + 3 jm ** gpm ** gmp - 1/2 jm ** w[-3/2] ** w[3/2] - 1/2 jm ** w[-1/2] ** w[1/2] + 1/3 j0 ** j0 ** j0 ** jm - 4/3 j0 ** jp ** jm ** jm,
  wp[-1] ** wm[1] - 2 j0 ** gpp ** gmm + 1/3 j0 ** w[-1/2] ** w[1/2] - 2/3 jp ** w[-3/2] ** w[1/2] + 1/6 jp ** w[-1/2] ** w[-1/2] + 5 jm ** gpp ** gmp + 1/2 jm ** w[-1/2] ** w[3/2] - jm ** w[1/2] ** w[1/2] + 1/3 j0 ** j0 ** jp ** jm - 4/3 jp ** jp ** jm ** jm,
  wp[0] ** wp[1] - 2 jp ** gpp ** gpm,
  wp[0] ** wm[-1] + 1/3 j0 ** w[-1/2] ** w[-1/2] - 1/3 jp ** w[-3/2] ** w[-1/2] + 3 jm ** gpp ** gmm - jm ** gpm ** gmp - 1/2 jm ** w[-3/2] ** w[3/2] - 1/2 jm ** w[-1/2] ** w[1/2] + 1/3 j0 ** j0 ** j0 ** jm - 4/3 j0 ** jp ** jm ** jm,
  wp[0] ** wm[0] + 3/2 j0 ** gpp ** gmm + 3/2 j0 ** gpm ** gmp - 1/4 j0 ** w[-3/2] ** w[3/2] + 3/4 j0 ** w[-1/2] ** w[1/2] - 1/3 jp ** w[-1/2] ** w[-1/2] - 4 jm ** gpp ** gmp - 2 jm ** w[-1/2] ** w[3/2] + 1/6 j0 ** j0 ** j0 ** j0 - 2/3 j0 ** j0 ** jp ** jm,
  wp[0] ** wm[1] + 2/3 j0 ** w[1/2] ** w[1/2] - 1/2 jp ** gpp ** gmm + 3/2 jp ** gpm ** gmp - 1/4 jp ** w[-3/2] ** w[3/2] - 1/4 jp ** w[-1/2] ** w[1/2] - 2 jm ** w[1/2] ** w[3/2] + 1/6 j0 ** j0 ** j0 ** jp - 2/3 j0 ** jp ** jp ** jm,
  wp[1] ** wm[-1] - 2 j0 ** gpm ** gmp + 1/3 j0 ** w[-1/2] ** w[1/2] - 2/3 jp ** w[-3/2] ** w[1/2] + 1/6 jp ** w[-1/2] ** w[-1/2] + 5 jm ** gpp ** gmp + 1/2 jm ** w[-1/2] ** w[3/2] - jm ** w[1/2] ** w[1/2] + 1/3 j0 ** j0 ** jp ** jm - 4/3 jp ** jp ** jm ** jm,
  wp[1] ** wm[0] + 2/3 j0 ** w[1/2] ** w[1/2] + 3/2 jp ** gpp ** gmm - 1/2 jp ** gpm ** gmp - 1/4 jp ** w[-3/2] ** w[3/2] - 1/4 jp ** w[-1/2] ** w[1/2] - 2 jm ** w[1/2] ** w[3/2] + 1/6 j0 ** j0 ** j0 ** jp - 2/3 j0 ** jp ** jp ** jm,
  wp[1] ** wm[1] + j0 ** w[1/2] ** w[3/2] + 1/2 jp ** gpp ** gmp - 3/4 jp ** w[-1/2] ** w[3/2] + 1/6 jp ** w[1/2] ** w[1/2] - 3 jm ** w[3/2] ** w[3/2] + 1/6 j0 ** j0 ** jp ** jp - 2/3 jp ** jp ** jp ** jm,
  wm[-1] ** wm[0] - 4 jm ** gmp ** gmm,
  wm[-1] ** wm[1] - 2 j0 ** gmp ** gmm,
  wm[0] ** wm[1] - 2 jp ** gmp ** gmm
};


(* A triplet of superpotentials for I_0, as for the rank-one N=3 SCFTs in the paper:
     I_0 = Sum_a ( Jac(P[a]) + Jac(deltaPlus P[a]) + Jac(deltaMinus P[a]) ),   a = -2, 0, 2,
   where Jac(f) is the ideal generated by the (left) partial derivatives of f with respect to all twenty coordinates.
   deltaPlus and deltaMinus are the odd derivations induced by the zero modes of the supercurrents G^{-+} and G^{+-}
   (G~_+ and G_- in the notation of the paper), extended by deltaX(f ** g) = deltaX(f) ** g + (-1)^F(f) f ** deltaX(g);
   they act on the coordinates as below and annihilate the coordinates that are not listed.
   P[0] is the sum of r_- ** r_+, with r_-, r_+ the two minimal generators of I_0 at conformal dimension 5/2 (the first two
   elements of N4SU3Ideal), and a polynomial independent of wu[-1/2], wu[1/2]; P[2] and P[-2] are obtained from P[0] with the
   zero modes of the su(2) currents K^+ and K^-. The equality of ideals holds exactly over the rationals.
   In the notation of the paper, (j0, jp, jm, gpp, gpm, gmp, gmm) = (j, j_+, j_-, g_+, g_-, g~_+, g~_-), and w[m], wp[m], wm[m],
   wu[m] are w_m, psi_m, chi_m, u_m, respectively. *)

N4SU3DeltaPlus = {
  j0 -> -gmp,
  jm -> -gmm,
  gpm -> -t,
  w[-3/2] -> -3 wm[-1],
  w[-1/2] -> -2 wm[0],
  w[1/2] -> -wm[1],
  wp[-1] -> -2 wu[-1/2],
  wp[0] -> -wu[1/2]
};

N4SU3DeltaMinus = {
  j0 -> gpm,
  jp -> gpp,
  gmp -> -t,
  w[-1/2] -> wp[-1],
  w[1/2] -> wp[0],
  w[3/2] -> wp[1],
  wm[0] -> -wu[-1/2],
  wm[1] -> -wu[1/2]
};

N4SU3Superpotential = <|
  -2 -> wu[-1/2] ** wu[-1/2] + 2 t ** t ** jm + t ** gpm ** gmm + 1/6 t ** w[-3/2] ** w[1/2] - 1/12 t ** w[-1/2] ** w[-1/2] - 2/3 j0 ** w[-1/2] ** wu[-1/2] - 1/12 j0 ** wp[-1] ** wm[0] - 1/12 j0 ** wp[0] ** wm[-1] + 2/3 jp ** w[-3/2] ** wu[-1/2] + 1/6 jp ** wp[-1] ** wm[-1] + 4/3 jm ** w[1/2] ** wu[-1/2] + 1/6 jm ** wp[0] ** wm[0] + 1/12 gpp ** w[-3/2] ** wm[0] - 1/12 gpp ** w[-1/2] ** wm[-1] - 1/12 gpm ** w[-1/2] ** wm[0] + 1/6 gpm ** w[1/2] ** wm[-1] - 1/12 gmp ** w[-3/2] ** wp[0] + 1/12 gmp ** w[-1/2] ** wp[-1] + 1/12 gmm ** w[-1/2] ** wp[0] - 1/6 gmm ** w[1/2] ** wp[-1] - 1/3 t ** j0 ** j0 ** jm + 4/3 t ** jp ** jm ** jm + 1/12 j0 ** j0 ** w[-1/2] ** w[-1/2] - 1/6 j0 ** jp ** w[-3/2] ** w[-1/2] - 1/3 j0 ** jm ** gpp ** gmm - 1/3 j0 ** jm ** gpm ** gmp - 1/3 j0 ** jm ** w[-1/2] ** w[1/2] + 1/12 jp ** jp ** w[-3/2] ** w[-3/2] + 2/3 jp ** jm ** gpm ** gmm + 1/3 jp ** jm ** w[-3/2] ** w[1/2] + 2/3 jm ** jm ** gpp ** gmp + 1/3 jm ** jm ** w[1/2] ** w[1/2],
  0 -> wu[-1/2] ** wu[1/2] + t ** t ** j0 + 1/2 t ** gpp ** gmm + 1/2 t ** gpm ** gmp + 1/4 t ** w[-3/2] ** w[3/2] - 1/12 t ** w[-1/2] ** w[1/2] - 1/3 j0 ** w[-1/2] ** wu[1/2] - 2/3 j0 ** w[1/2] ** wu[-1/2] - 1/12 j0 ** wp[-1] ** wm[1] - 1/12 j0 ** wp[0] ** wm[0] - 1/12 j0 ** wp[1] ** wm[-1] + 1/3 jp ** w[-3/2] ** wu[1/2] + 1/3 jp ** w[-1/2] ** wu[-1/2] + 1/12 jp ** wp[-1] ** wm[0] + 1/12 jp ** wp[0] ** wm[-1] + 2/3 jm ** w[1/2] ** wu[1/2] + 2 jm ** w[3/2] ** wu[-1/2] + 1/6 jm ** wp[0] ** wm[1] + 1/6 jm ** wp[1] ** wm[0] + 1/12 gpp ** w[-3/2] ** wm[1] - 1/12 gpp ** w[1/2] ** wm[-1] - 1/12 gpm ** w[-1/2] ** wm[1] + 1/4 gpm ** w[3/2] ** wm[-1] - 1/12 gmp ** w[-3/2] ** wp[1] + 1/12 gmp ** w[1/2] ** wp[-1] + 1/12 gmm ** w[-1/2] ** wp[1] - 1/4 gmm ** w[3/2] ** wp[-1] - 1/6 t ** j0 ** j0 ** j0 + 2/3 t ** j0 ** jp ** jm - 1/6 j0 ** j0 ** gpp ** gmm - 1/6 j0 ** j0 ** gpm ** gmp + 1/6 j0 ** j0 ** w[-1/2] ** w[1/2] + 1/3 j0 ** jp ** gpm ** gmm - 1/6 j0 ** jp ** w[-3/2] ** w[1/2] - 1/12 j0 ** jp ** w[-1/2] ** w[-1/2] + 1/3 j0 ** jm ** gpp ** gmp - 1/2 j0 ** jm ** w[-1/2] ** w[3/2] - 1/3 j0 ** jm ** w[1/2] ** w[1/2] + 1/12 jp ** jp ** w[-3/2] ** w[-1/2] + 1/2 jp ** jm ** w[-3/2] ** w[3/2] + 1/6 jp ** jm ** w[-1/2] ** w[1/2] + jm ** jm ** w[1/2] ** w[3/2],
  2 -> -wu[1/2] ** wu[1/2] - 2 t ** t ** jp - t ** gpp ** gmp - 1/2 t ** w[-1/2] ** w[3/2] + 1/3 t ** w[1/2] ** w[1/2] + 4/3 j0 ** w[1/2] ** wu[1/2] + 1/6 j0 ** wp[0] ** wm[1] + 1/6 j0 ** wp[1] ** wm[0] - 2/3 jp ** w[-1/2] ** wu[1/2] - 1/6 jp ** wp[0] ** wm[0] - 4 jm ** w[3/2] ** wu[1/2] - 2/3 jm ** wp[1] ** wm[1] - 1/6 gpp ** w[-1/2] ** wm[1] + 1/6 gpp ** w[1/2] ** wm[0] + 1/3 gpm ** w[1/2] ** wm[1] - 1/2 gpm ** w[3/2] ** wm[0] + 1/6 gmp ** w[-1/2] ** wp[1] - 1/6 gmp ** w[1/2] ** wp[0] - 1/3 gmm ** w[1/2] ** wp[1] + 1/2 gmm ** w[3/2] ** wp[0] + 1/3 t ** j0 ** j0 ** jp - 4/3 t ** jp ** jp ** jm - 1/3 j0 ** j0 ** w[1/2] ** w[1/2] + 1/3 j0 ** jp ** gpp ** gmm + 1/3 j0 ** jp ** gpm ** gmp + 1/3 j0 ** jp ** w[-1/2] ** w[1/2] + 2 j0 ** jm ** w[1/2] ** w[3/2] - 2/3 jp ** jp ** gpm ** gmm - 1/12 jp ** jp ** w[-1/2] ** w[-1/2] - 2/3 jp ** jm ** gpp ** gmp - jp ** jm ** w[-1/2] ** w[3/2] - 3 jm ** jm ** w[3/2] ** w[3/2]
|>;
