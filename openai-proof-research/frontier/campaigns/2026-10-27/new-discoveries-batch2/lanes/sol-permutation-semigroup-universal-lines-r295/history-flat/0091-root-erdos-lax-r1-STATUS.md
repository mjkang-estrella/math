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
Both public Rubin thesis files were read: 102 and 100 introductory pages only,
without the appended article. The 2026 Bergman public thesis PDF similarly has
34 introductory pages only. Its Theorem 8 (printed p12, PDF p24), visually read,
requires all roots on the unit circle. None closes the published-body gap.
Poppler warned about an xref reconstruction on the first Rubin file; extraction
completed. Retrieval URLs, exact hashes and timestamps are retained.

Current trureturing head 2ddf2917de0dde187e85df253cbd6bd0e0c00a0e was fetched.
Complete Problems, D5 and Blueprint trees were fetched with truncated=false;
the path-level target screen found no on-point hit. RationalPower hits concern
Mersenne arithmetic and have not been body-audited. This is not full novelty
clearance. Current openai/math head remains 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a;
the current complete preprint path tree from the Jacobi refresh was screened for
Lax/vanishing-weight/Bergman-Rubin/fractional-power paths without an on-point hit.
This path screen is not a body audit or complete prior-art clearance.

`checks/probe.py` uses literal product log moduli and logarithmic derivatives,
4096-angle sampling plus local maximization of every sampled maximum. Seed
359807; 300 configurations with 2--7 roots and half-integer weights >= 1 gave
no violation, largest normalized ratio 0.9999878605674631. It also tested the
possible stronger logarithmic-derivative bound at a derivative maximizer,
finding no obstruction in those trials. The stronger claim is now exactly
refuted by a quadratic with exterior roots; see ROUTES.md and the rational
checker route_obstructions.py. This does not refute the actual conjecture.

The normalized-minimum reduction in ROUTES.md proves that it suffices to treat
min(s_k)=1, including strictness for an exterior root. It is an elementary
reduction, not a nominated result. A further 1,800 normalized configurations
(seed 359808) give largest diagnostic ratio 0.9999983883759404, no conjecture
violation, and 93 failures of the stronger local shortcut. Neither global
maxima nor any general inequality are certified by this floating-point scan.

Erdelyi's actual 1993 JCAM survey Sections 9--11 were compared: the available
generalized-polynomial derivative bounds use unspecified absolute constants
or different real-interval norms. No direct exact S/2 bridge follows from those
statements. No full literature/subsumption clearance is claimed.

Continue source/prior closure and genuine mathematics before major formal
investment. The global norm comparison remains unproved. No Lean or discovery
nomination; credit 0. These notes preserve failed routes for the next worker.
