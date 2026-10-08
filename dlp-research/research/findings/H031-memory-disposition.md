# H031 memory proposals: corrected paper screens

Status: independently reviewed limited mathematics, speculative many-target
survivor, no verified algorithm improvement. Date2026-10-08 UTC.

The five independent Factory proposals are preserved verbatim in
[the raw report](H031-memory-factory-raw.md). Its transport final summary was
housekeeping only; root recovered the substantive untruncated message at
timeline position40. The report's probability models, novelty, cost claims and
universal rejections are not accepted merely because the task completed.

## Review provenance and scope

- Factory Opus5.5 proposer: task suffix
  `ecdloop-h031-memory-recomputation-factory-opus-20261008-r2`.
- Native Sol `/root/h010_early_dependencies`: independent Card1 mathematics,
  COMPLETED; exact conditional coverage law and paid-construction caveats.
- Native Astra `/root/h007_additive_relations`: independent Cards2–5 review,
  COMPLETED; then separately confirmed root's corrected conditional Card3 loss.
  Final narrow symbolic-cost review of the Opus report also COMPLETED; confirms
  the corrections below, with no new experiment recommended.
- Root checked algebra, scope and dispositions and owns integration.
- Claude Opus5.5 prior-art/full-cost review COMPLETED: suffix
  `ecdloop-h031-retained-giants-priorart-opus-20261008-r1`.
  Every T3 suffix above has the full prefix
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3A`.

All roles read-only; no new experiment/import, numerical integration, code or
Lean claim. The arithmetic units below are conditional ledgers, not measured
hardware throughput. Write s=S/M in[0,1]. Raw prior-art report is retained in
[H031-retained-priorart-opus-raw.md](H031-retained-priorart-opus-raw.md), with
the following root corrections; its completion does not accept its cost claims.

## Card1: retained giants with shared signed babies

Mechanism: solve K independently blinded targets in succession; retain each
solved target's giants as additional known-log records for later targets.
Different target strides are primes near2b+1, with b signed babies. This is
only a solve-all-K scheduling proposal. K=1 gets no benefit from earlier targets.

Let Q'_t=Q_t+r_tG=[κ_t]G and retain v=κ_t−j'D_t. A giant match against a baby
or retained point gives κ_s=jD_s±i or κ_s=jD_s±v, respectively. Verify the
candidate and output k_s=κ_s−r_s. Process O directly: abscissa lookup omits it.
For0<D_s≤2b+1<q, j=0,...,ceil(q/D_s)−1 covers every scalar: the intervals
jD_s+[-b,b] touch/overlap and contain at least q consecutive integers. This
does not establish the existence or cheap construction of K suitable primes.

Fresh uniform independent blinding makes κ_s uniform conditional on completed
past work. Let C contain DISTINCT signed known scalars, including0 and±[1,b],
and let F_j=union_{v=0}^j(C+vD_s), F_{−1}=empty. For query count T_s and
J_s=ceil(q/D_s), the exact law is

    Pr(T_s>j+1 | C) = 1 − |F_j|/q
    hazard at query j = |(C+jD_s) \ F_{j−1}| / (q−|F_{j−1}|)
    E[T_s | C] = sum_{j=0}^{J_s−1} (1−|F_{j−1}|/q).

The hazard is defined only on a positive-probability survival event. It depends
on translated-set overlaps, not just the number R of retained records. Previous
targets stop at previous collisions, so retention is itself selected by earlier
coverage. Uniform initial blinding does not justify memoryless hazard2R/q.
Distinct prime strides exclude some bounded integer difference equalities;
modular equalities and their translated pair multiplicities need separate bounds.
The raw O(1) coincidence correction does not follow from primality alone.

Therefore the continuum ψ integral and claimed0.906√(qK) key cost remain
UNESTABLISHED. Recomputing an optimum of that model would not validate it.
Even granting its estimate, gross headroom against its claimed1.0 comparator
would be only0.094 C_x√(qK); no full-work saving follows.

Mandatory costs: every giant including the successful query, dynamic insertion,
deduplication, fingerprint resolution, retained storage and temporary buffers;
each blinding, stride/offset construction, prime search, recovery and verification.
The raw10× record bits/16× total bits is unsupported: a concrete layout and paid
recovery are needed. Index-free hierarchy alternatives from H030 preclude an
universal explicit-index necessity. Match stored bits, solve-all-K scope and
preprocessing against shared signed BSGS, interleaved growth and known reused
walk/precomputation methods.

Primary source check: root independently fetched the PDFs via urllib.request and
piped bytes to `pdftotext - -`, after web open returned502. Kuhn–Struik
§4 pp218–219 already converts solved-target distinguished points into known-log
entries usable for later targets; it credits Silverman–Stapleton. Bernstein–Lange
§6 already chooses two coprime giant strides for distinct-slope coverage. The
present combination is not thereby proved identical, but retaining solved points
or using different strides is not itself a discovery. Sources:
[Kuhn–Struik, SAC2001](https://cr.yp.to/bib/2001/kuhn-rho.pdf) and
[Two grumpy giants and a baby](https://cr.yp.to/elliptic/grumpy-20120709.pdf).
This bounded source check establishes antecedents, not exhaustive novelty.

Additional raw-review claims NOT accepted: an unmeasured DRAM miss≈C_x; a
necessary log(R)-bit index per retained point; a guaranteed short interval of
K primes from Δ≈K log b; comparator rankings from different primitive counts,
memory or model conventions. Also its0.094 headroom mixes rounded B+Γ≈0.91
with W≈0.906. Keep symbolic coefficients until the probability model is valid.
Use actual baby count b in buffer estimates such as q/(2b), not the normalized
coefficient B=b/sqrt(qK). Distinguish storage already counted in retained records
from a current uninserted buffer before summing peak space. No hardware or
universal layout lower bound was obtained by the source reviewer.

For provisional normalized key counts B_c,G_c for candidate and B_b,G_b for
baseline, a complete-cost condition must compare

    (B_b+G_b−B_c−G_c) C_x
      > table_cost_c/sqrt(qK) − table_cost_b/sqrt(qK)
        + (other_cost_c−other_cost_b)/sqrt(qK).

Table costs include distinct bulk-build/dynamic-insert/probe/resolve costs and
sizes; replacing them by one common insertion price is an extra model, not a
necessary physical law. Matched peak stored bits is a separate constraint, not
an arbitrary memory price. Failed targets/setup and all success probabilities
must agree. The raw0.2 C_x break-even is only an informal special case, not an
admission test supported by measured data.

The independently checked rounded special case uses T=sqrt(qK), B_c=.35,
G_c=.56, B_b=G_b=.5. Its consistent credit is.09 C_x T (not.094), with gate

    .09 C_x > .35 I_c,b + .56 I_c,g − .5 I_b,b
              + .56 P_c − .5 P_b + (S_c−S_b)/T.

I denotes the relevant per-record table construction price, P probe price,
and S remaining paid work. If every I is identical and P_c=P_b=P, this becomes
.09 C_x>.41 I+.06 P+(S_c−S_b)/T. If P_c=P_b+ΔP, the probe difference is
.06 P_b+.56 ΔP. None of these stipulated costs is a hardware measurement.

Disposition: speculative many-target survivor for PAPER review only. Next
decisive gate is a justified retained-set law or coverage bound using F_j, plus
equal-bit complete costs. No finite integer simulation is admitted by this note.
This cannot change the single-target dashboard even if its model is repaired.

## Card2: minimum of two candidate classes

Granting the proposed4/3 collision enhancement and its6M+2S transition ledger,
the ratio against5M+S is

    (sqrt(3)/2)(6+2s)/(5+s) ≥ 3sqrt(3)/5 > 1.

The ratio increases with s. This is a conditional arithmetic loss. The two
candidates are not independent samples, and an iid minimum pushforward density
is not the walk's stationary distribution or stopped-solver law. No universal
statement about more candidates, slope selectors or all biased walks follows.

## Card3: block minimum-hash anchors

For fixed sets A,B under a shared uniform random ordering, the exact probability
of equal minima is |A∩B|/|A∪B|. Equal n-element sets with one common element
therefore share the anchor with probability1/(2n−1), NOT1/n². This corrects
the report's different-stride argument. The claimed universal 'coalescence lock'
is not established.

Nevertheless, grant its rare-single-intersection model and conversion from
collision rate to square-root stopping: enhancement F=n²/(2n−1). Its own ledger
for odd n=2ell+1≥3 is C=(n−1)(2.5+s)+6+s=n(2.5+s)+3.5. Hence

    C/((5+s)sqrt(F))
      ≥ ((2.5+s)/(5+s))sqrt(2n−1)
      ≥ sqrt(5)/2 > 1.

Thus the corrected idealization still predicts a loss, even dropping positive
3.5M overhead. This does not prove the EC intersection law, collision-to-stopping
conversion or arithmetic applicability. Canonical orientation, anchor coordinates,
coefficient updates, hashing, stride setup and recovery remain paid obligations.
Same-stride overlap/minhash identities also do not by themselves prove a walk
stopping law. No simulation or broader block-method rejection is justified here.

## Card4: a filter over all precomputed trail points

Membership does not supply a recovery index. But the raw conclusion that one
must either walk to a distinguished point or store log(number-of-points) bits
per point is unsupported: paid replay, checkpoints or hierarchies are possible.
H030 already records such distinctions. The stated near-full-table threshold
has not been derived for a specified executable recovery method and cost model.

Disposition: no accepted gain and no universal rejection. Requires a concrete
paid recovery/layout mechanism before a useful comparison; no implementation now.

## Card5: bursts around distinguished points

Under the proposed rate model, R=(1+nθc)/sqrt(1+nθ²), where0≤θ≤1 and
c=(2.5+s)/(5+s)∈[1/2,7/12]. The raw approximate0.57 is not uniform. Exactly,

    (1+nθc)²−(1+nθ²) = nθ(2c−θ+nθc²) ≥ 0.

So the granted model predicts no gain for all n≥0, not just to first order.
Its rate law and stopped-solver interpretation remain unproved: dependence,
repeated relations, coefficient usefulness, center double-counting and delay
must be handled. The related claimed dominance by Card1 inherits Card1's missing
coverage model. No universal burst-method closure is accepted.

## Wave outcome

Best supported reference remains square-root classical work with the existing
memory/automorphism qualifications. Verified improvement NONE. Corrected paper
models lose for Cards2,3,5; Card4 lacks a concrete recovery contract; Card1 lacks
its claimed probability/cost justification and is many-target only. Preserving
these objections prevents treating brainstorming estimates as findings.

Next: a justified Card1 coverage/cost bound could reopen the paper-only survivor;
otherwise prioritize the still-independent Grok initial proposal and single-target
mechanisms. No numerical result, new formal theorem or hardware claim is made.
Validation command and result are recorded in STATE.
