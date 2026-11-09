# Classical Bessel source comparison (root, 2026-10-27)

No discovery credit, acceptance, or independent novelty PASS is made here.
The Bessel candidate remains frozen at 26b211919f and pending its six-gate
independent final review. This note and its evidence are outside that freeze.

## Actual primary access and reading

Young, *On Series of Bessel Functions*, Proc. London Math. Soc. series 2,
volume 18, pp.163–200, DOI 10.1112/plms/s2-18.1.163. The scan itself records
received/read December 1917; later volume references date it 1919/1920.
Public Internet Archive item london-mathematical-society-proceedings_1919-1920_18
contains the genuine complete journal volume. Root downloaded the PDF, OCR and
scandata, verified each MD5 against that item's metadata, and read the complete
article OCR, including all theorem statements and intervening arguments.
Root separately rendered and visually read printed pp.163,171,191. Printed
p.163 is PDF page201 (scan leaf201; PDF count omits an earlier leaf). The retained
article excerpt is printed pp.163–200, extracted from full-volume PDF201–238.
OCR is imperfect: visual pages govern displayed formulas used in this note.

Watson, *A Treatise on the Theory of Bessel Functions* (1922), Chapter XVIII,
sections18.5–18.56, printed pp.606–616. Public IA item treatiseontheory00watsuoft
provided the complete OCR, matched against declared MD5. The main PDF URL
redirected to dn760100.eu.archive.org and hit an SSL-handshake/read timeout.
The item's own metadata lists workable server ia800507.us.archive.org; the
same public PDF was downloaded there and matched the declared MD5. Root read
pp.606–616 in OCR and separately rendered and visually read pp.606,607,610,614.
Printed p.606 is PDF616. Retained excerpt is PDF616–626. The rest of the book
was searched by keywords only, not read in full; no whole-book clearance claim.

## Comparison with the candidate

The candidate concerns the literal finite sum
K_M^alpha(x) = sum_{m=1}^M (1-m/(M+1))*j_m^alpha*J0(j_m*x).
Its proposed refutation is M=2, alpha=2/5, x=47/50, with K < -1/500.

Young section5 gives coefficient/term decay from weighted integrability;
section6 gives a Cesaro-localization theorem. Sections15/31 identify limiting
upper/lower functions and a partial-sum difference tending to zero (when
individual terms tend to zero). Sections36–38 address endpoint convergence.
No finite modified-kernel positivity or counterexample was found in these
actual bodies. An asymptotic zero-error comparison by itself supplies no sign
or numerical value for the two-term sum. Section6 explicitly defers a fuller
Cesaro convergence discussion to other work; this is a remaining search lead,
not evidence that no related literature exists.

Watson p.607, eq.(2) defines
T_n(t,x|R) = sum_{m=1}^n (1-j_m/A_n)*
             2*J_nu(j_m*x)*J_nu(j_m*t)/J_{nu+1}(j_m)^2.
The weight is LINEAR in j_m/A_n. An initial root steering message misread OCR
as a squared weight; the actual rendered pages606–607 corrected this and a
second steering message explicitly retracted the erroneous squared version.
There is no reliance on that transcription. Section18.52 (p.610) is a
limiting Riesz summability theorem to the mean of one-sided values.
Section18.54 (pp.613–614) compares Riesz and index-Cesaro means in the limit
for actual Fourier–Bessel coefficients. This normalized Bessel-product kernel
is different from the candidate's j_m^alpha coefficient family; the cited
summability theorems do not directly provide its finite two-term sign.

## Scope of the conclusion and remaining objections

Neither of these read bodies supplies the specific finite counterexample or
an identified immediate subsuming theorem. That is a bounded comparison,
not a worldwide novelty certificate or an eligibility decision. Other
Fourier–Bessel positivity/Cesaro/Riesz literature, author follow-ups, registries
and unindexed prior counterexamples still require the independent reviewer's
judgment. A small-M counterexample can still be a simple overlooked error or
a parameter-domain issue rather than a substantial new discovery: the parent
has not pre-decided this question in order to reach30. The separate slow-decay
existence questions in the modern source are not resolved by this witness.

All 56 frozen Bessel paths remained unchanged. No public posting/contact,
credential use or access-control bypass occurred. Public source PDFs and
excerpts are evidence only; no Lean proof changes or tally updates were made.
