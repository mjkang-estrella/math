# r119: no full-scope resolution

This solo lane nominates nothing. Counts remain 8 additional / 38 total;
no shared files, git, messages, browser tabs, Lean or paper were used.

## Exact primary questions and body scope

Primary original: Beck–Sam–Woods, *Maximal Periods of (Ehrhart)
Quasi-Polynomials*, author-hosted PDF, Section 6, Conjecture 11 (PDF p7).
For every n>=1 and positive integer list a_1,...,a_n, write the restricted
partition count q(k)=#{u in N^n: sum a_i u_i=k} uniquely as
sum_{j=0}^{n-1} c_j(k)k^j with periodic coefficient functions. Set
b_m=#{i:m divides a_i} and p_j=lcm{m:b_m>j}. The conjecture asserts that
the minimum period of every c_j is exactly p_j. The actual original statement,
Theorems 2, 6 and 7, and full proof of Theorem 2 were read in the author PDF.

This universal assertion is already publicly refuted by Liu–Tang–Xin–Zhang,
arXiv:2608.02085v1, Theorems 1.4 and 4.3. Actual Section 4 proof bodies were
read, including Propositions 4.1 and 4.2: at -1 the constant coefficient is
2^(-u-5)(lambda^3/6-alpha*lambda), with lambda=4+(u+M)/2 and
alpha=2/3+u/8+M^2/8. For u=2,M=13 it vanishes. Primitive 13th roots have
nonzero simple-pole coefficients; hence the constant coefficient has period
13 although p_0=26. The source's exact Fourier-support formula (Theorem 1.2)
and Fourier Lemmas 2.1/2.2 were inspected, together with Section 6's explicit
distinct-weight and all-weights>1 examples. Thus those restrictions do not
supply a fresh unrestricted question. The larger Section 6 examples and the
infinite Pell family were NOT independently certified here.

The public proof's body scope covers the universal conjecture's negation;
this is separate from an audit of every theorem it announces. This lane
independently checks only its seven-weight example, using exact integer
dynamic programming and rational interpolation, rather than the hyperbolic
formula: periods are [13,2,2,2,1,1,1] for weights (1,1,2,2,2,2,13).
The classical degree n-1/period N quasipolynomial theorem is an explicit
input to interpreting interpolation; two additional values per residue are
also checked. These finite checks earn no discovery credit and do not certify
the whole public paper. The low-order cancellation identity is checked as a
second route. No independent novel proof preceded the external publication.

## An adjacent full source question, left unresolved

The same original Section 6 asks whether Theorem 2 survives without the
distinctness restriction. Precisely: for every d>=0 and positive integers
p_d | p_{d-1} | ... | p_0, repetitions allowed, does the Ehrhart count of
conv(e_0/p_0,...,e_d/p_d) have coefficient c_j of minimum period p_j for
every 0<=j<=d? Equivalently its series is product_i (1-x^{p_i})^-1.
This is an actual source question, not invented generalization of Conjecture11.
The public counterexample above has weights 2 and 13, which are incomparable
under divisibility, so does not answer this chain-restricted question.

checks.py exhausts all 458 nondecreasing divisibility-chain lists with length
2 through 5 and entries at most 12. It finds no counterexample, using rational
interpolation of every coefficient and every residue. This is finite evidence
only. No all-d/all-weight nonvanishing theorem has been established here.

The attempted direct transfer of the original Theorem 2 proof fails at its
first pole-order assertion: distinctness forces a primitive p_j-th root to
have pole order j+1. With repeated weights it can be larger. For (p_0,p_1,p_2)
=(2,2,1), j=0, -1 is a double pole, not a simple pole. The checker records
actual periods [2,2,1]; this falsifies the attempted intermediate premise,
not the source question. A pole of order s forces the highest surviving
coefficient frequency at degree s-1, without forcing all lower degrees.
The public seven-weight cancellation separately falsifies the stronger
generic nonvanishing assertion that every pole contributes to every lower
coefficient. Neither route closes the chain-specific nonvanishing gap.

Strongest routine/subsumption objection: the relaxed chain question might
follow from a positive formula for chained restricted partitions or a small
extension of the original pole proof. This lane has neither a complete bridge
nor a proof defeating that objection. Falsifiers are an exact chain with a
coefficient period smaller than its assigned p_j, or an actual published
all-chain theorem. Finite tests settle neither. No novelty clearance is
claimed; no investment nomination or PROOF.md is appropriate. Lean feasibility
is conditional: finite counterexamples would reduce to rational coefficient
identities plus a literal counting/quasipolynomial bridge; a universal result
needs the still-missing all-order proof and source identification. No Lean run.

## Historical screen, exact coverage, and failures

research.py streams selected text extensions throughout all-date
openai-proof-research, including original research, copied reviews, rejected
lanes, catalogues and scripts/tools. It hashes each selected body and records
all paths in compressed pathmap.jsonl.gz, scanning each distinct body once.
382641 paths / 276654 distinct bodies completed in 101.38 seconds. The
screen-receipt records exact excluded basenames/directories/extensions and
each selected text over the 12MB cap as a precise gap. Binary PDFs, compressed
texts and other extensions are outside this lexical pass. Generated r111-r113
large caches are not mathematical evidence. No aggregate content inventory
was generated or reproduced. The broad period and Ward reporting caps filled;
focused-matches.json separately rescreens the distinct originals with exact
target terms. Hash/lexical screening is not full historical semantic reading.
No zero-match or stale catalogue absence is used to certify freshness.

The focused rescreen returned 54 lines (all retained under its65 limit), largely
unrelated uses of “quasiperiodic,” rather than an original source resolution
of these two questions. The full retained bounded record was inspected. This
does not clear omitted/binary/large historical material. It supplies no novelty
PASS for the unresolved repeated-chain question.

Initial mistakes preserved: two broad combined context reads produced truncated
tool output; a root-r117 SUMMARY.md lookup failed because its actual handback
files are ADOPTION.json and DECISION.md, subsequently read. A later rg of a
single-line registry JSON echoed too much metadata; subsequent registry handling
parses JSON and reports bounded fields. These failures do not count as reads
of omitted text. Full as-read context copies/hashes are frozen; NEXT is mutable
coordination, and its drift is recorded separately from mathematical inputs.

The initial screen's 90-hit reporting cap is not a complete list of matches;
the focused rescreen retains its own cap and total. Large-file exclusions mean
the scan is not a complete historical clearance. No acceptance depends on it.
Search-engine results are leads only. Ward and read-once-factorial leads were
not selected after this screen; no scope/absence conclusions about them.

Registry-coverage.json records one new HEAD observation per registry and only
the Omega d254db-to-observed-head comparison. The earlier fixed interval stays
with the assigned r4 reviewer and is neither duplicated nor declared closed.
No generic freshness PASS; no repeated HEAD chasing. New commits observed in
this run postdate the August public counterexample but precede any new proof
here (there is no new proof). Patch/path observations do not certify actual
proof-body clearance for the unresolved adjacent question.

Exact new observation at22:21:24UTC: Omega HEAD
a7769c386bd6072628a21cf4680756d2a49bf221. Its comparison from d254db is ahead,
merge-base exactly d254db,47 returned/total commits and207 changed paths,
below the300-file cap. No target-bearing path name was found; actual relevant
proof bodies are NOT certified. OpenAI HEAD remains
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. This new interval is not a partition
of, or repair to, the assigned reviewer's older interval.

All Python and extraction helpers use the unchanged designated helper_guard.py,
AS and sampled group RSS 512MiB, CPU210s/wall230s, nominal40ms, BLAS threads1.
Native bounded reads/apply_patch are exceptions authorized by the task.
source-lock.json binds scientific inputs; context-receipts and context-drift
separate mutable coordination. finalmanifest and its detached verified receipt
bind the delivered lane. Runnable checks are supporting diagnostics only.
