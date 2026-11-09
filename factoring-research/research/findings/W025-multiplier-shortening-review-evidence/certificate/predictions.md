# W025 certificate: frozen cases and predictions (written before execution)

Single run, python3 -I, wall timeout 60 s, charged-event cap 20000 (one event per
c-trial, per R^2 identity check, per covered (x,sigma,S) check). Literal bounded
search over c is a CERTIFICATE of existence/identities on these cases only, NOT an
implementation of Lenstra's algorithm and not evidence of asymptotic cost.

Cases
K1 real W022 chart, ell=3, h=5 (Q=3^10, H=9), p=1013, q=100003, v=-1 (signed
   singleton y=-1), U=242, V=2, W=U*p+V*q, section-3 univariate quartic.
K2 real W022 chart, ell=5, h=4 (Q=5^8, H=25), p=1009, q=10007, v=+1, U=624, V=2.
K3 synthetic section-1/2 generic: ell=3, Q=3^6, d=(1,3,6,81,81), w=(1,4,16,64,256),
   T=16, W=2Q.
K4 synthetic Q'=ell: ell=3, Q=9, d=(1,3,3,3,3), w=(1,2,4,8,16), T=4, W=2Q.
K5 section-3 formula with ell=3, Q=9, Z=4, A=1 (B>=Q fallback).

Predictions
P1 Pigeonhole: a c in [1,B] satisfying (1) exists in K1-K4 (B<Q there).
P2 K1,K2: B<Q; c_struct=Q/H^3 satisfies (1) iff c_struct<=B (deterministic: it
   annihilates coefficients 3,4); recorded either way.
P3 K3: least feasible c is 9, r=9, c'=1, Q'=81.  K4: least c=3, c'=1, Q'=3=ell.
P4 K5: B=30>=Q=9, fallback branch flagged; no normalization attempted.
P5 Zero violations of: R^2==4Nuv mod Q (K1,K2); P==c'R mod Q'; |P|<=D*Q'*T
   (section-3 cases: <=3Q'T); every covered S (both signs) has c'S=sigma*P+Q'*tau
   with |tau|<=bound (2) (K1,K2: <=7T); E' == c'*eps_sigma mod ell (K1,K2).
P6 K1,K2: coefficient of x^i divisible by H^i mod Q (i=0..4); truncation to degree 2
   modulo H^3 represents every covered S with |tau|<=floor((W+H^3*Z^2)/H^3) and the
   same eps residue.
P7 K1,K2 true leaf: retained (p != 1 mod ell); E'=c'*(p-1)*(v*q-u) and nonzero.
P8 K1,K2: truncation carry bound < W025 bound 7T at these sizes (finite numbers only).
Failures will be retained verbatim; no reruns or tuning.
