# Primary-source check: the sole external mathematical dependency

Checked on 2026-10-08 through the web tool, the author's institutional
publication listing, and the author-hosted published PDF:

D. Zagier, *Newman's Short Proof of the Prime Number Theorem*,
The American Mathematical Monthly 104, no. 8 (1997), 705-708.
Published article identifier: 10.2307/2975232.

- Author's listing: https://people.mpim-bonn.mpg.de/zagier/
- Checked paper: https://people.mpim-bonn.mpg.de/zagier/files/doi/10.2307/2975232/fulltext.pdf
- Downloaded PDF byte length: 196309.
- Downloaded PDF SHA-256: a2cdbbcc38b9f21cd68903bcd0262be2c211677cbda7ae903b9e124bd0d12561.

The paper itself presents a mathematical proof; no secondary summary was
used as authority. Page 705 defines the prime-weight sum. Step (VI) on page
707 states theta(x) ~ x and gives the deduction from the preceding integral
convergence. The displayed theta sum on page 707 is over primes p<=x.
Thus the imported statement is exactly

    theta(x) := sum_(p<=x, p prime) log p = x+o(x).

This short formula and these source metadata freeze the technical input.
The full copyrighted article and a whole-page image are not part of the
delivery. They were used transiently inside the assigned evidence directory
for source inspection, then removed before sealing the manifest.

The web PDF text was checked, but its mathematical OCR was damaged. The
downloaded PDF's fourth page (printed page 707) was therefore rendered with
pdftoppm and visually inspected through view_image. The rendering clearly
shows step (VI), theta(x) ~ x, and the p<=x sum. The inspected rendering's
SHA-256 was a511973639d989417500532163feb8afd0f97c78e189195349060961ff3ce5bb.
This was source reading, not numerical or symbolic-program evaluation of
the research candidate.

Use in the review is limited to the asymptotic growth of the prime-band
product. The exact finite period-divisibility theorem does not use PNT.
The subtraction theta(2R-3)-theta(R+1), its asymptotic R+o(R), and the
uniform filter consequence are derived in the review. No effective threshold,
error rate, short-interval or arithmetic-progression prime theorem, Riemann
hypothesis, algorithmic prime-finding bound, or factoring complexity result
is attributed to this source. The review does not claim originality for PNT
or reprove the paper's analytic theorem.
