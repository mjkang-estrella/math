# Generalized Erdos-Lax screen — unfinished, no nomination

Target: Bergman--Rubin, arXiv:2309.02047v2, Conjecture 2, MathDB 359807.
Read the cached literal statement and Theorems 4/5. For rational exponents
s_k >= 1 and roots |a_k| >= 1 the question is
||f'||_T <= (sum s_k)/2 ||f||_T, for f a branch of the product of powers,
with equality precisely for unimodular roots (the zero constant degeneracy
is not a discovery target). Existing proved cases include all boundary roots
and integer exponents at exterior roots. No new proof has been found here.

Live arXiv history still lists v2 (15 January 2024) as latest. Publisher DOI
10.1016/j.jat.2024.106048, JAT 301 (2024), 106048, is confirmed by the publisher
and Lund record. Direct publisher body retrieval returned 403, respected.
The public Rubin thesis file ending LUCRIS-2 was retrieved but has only 102
pages; its contents list appended papers beyond that, so it does not close the
published-body gap. A second public thesis file is retained for further read.
Poppler warned about an xref reconstruction on the first; extraction completed.

Current trureturing head 2ddf2917de0dde187e85df253cbd6bd0e0c00a0e was fetched.
Complete Problems, D5 and Blueprint trees were fetched with truncated=false;
the path-level target screen found no on-point hit. RationalPower hits concern
Mersenne arithmetic and have not been body-audited. This is not full novelty
clearance. Current openai/math head remains 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a;
its current full manuscript catalogue has not yet been screened for this target.

`checks/probe.py` uses literal product log moduli and logarithmic derivatives,
4096-angle sampling plus local maximization of every sampled maximum. Seed
359807; 300 configurations with 2--7 roots and half-integer weights >= 1 gave
no violation, largest normalized ratio 0.9999878605674631. It also tested the
possible stronger logarithmic-derivative bound at a derivative maximizer,
finding no obstruction in those trials. Neither global maxima nor any inequality
are certified by this floating-point diagnostic. No proof or Lean is claimed.

Work was interrupted for the completed Jacobi packet's root inspection and
final-review preparation. Continue source/prior closure and genuine mathematics
before further investment. Credit 0; all shared counts unchanged.
