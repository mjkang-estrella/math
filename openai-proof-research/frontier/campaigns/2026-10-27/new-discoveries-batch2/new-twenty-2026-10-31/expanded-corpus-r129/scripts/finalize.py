import pathlib,json,collections,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text())
assert len(r)==20 and set(map(int,r))==set(reservation['ids'])
for i,o in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
 assert o['lean_packet'] is None and o['accepted_credit']==0
for f in ['pseudoline','pseudoline-large']:
 rows=[json.loads(l) for l in (D/f'logs/{f}.log').read_text().splitlines()];print(f,'sampled',sum(x['sampled_reduced_words'] for x in rows),'colorable',sum(x['3colorable'] for x in rows),'unknown',sum(x['solver_unknown'] for x in rows))
counts=collections.Counter(x['outcome'].split('_')[0] for x in r.values());print(dict(counts))
summary='''Lane expanded-corpus-r129 — research handback
=============================================

No qualifying new full-scope solution or Lean packet was produced. Root alone
adjudicates acceptance. Exactly 20 ID-keyed dispositions are in [results.json](results.json).
This packet contains five stop/exclusion recommendations and fifteen parked targets.
It is a bounded investigation, not the several-hour deep pass requested in TASK.txt;
that depth requirement is not fulfilled. No acceptance count or shared index was changed.

The strongest retained routes are 362890 (unimodality coefficient inequalities),
353384 (3-connected gamma-zero structure), and 354662 (antipodal arrangement
coloring). Concrete equations, semantic limits and remaining lemmas appear in
[ATTEMPTS.md](ATTEMPTS.md). None has a complete ordinary proof or a literal Lean endpoint.

Stop recommendations:

* 358651: the source itself proves Wilson's Rose Window conjecture, Theorem 1.3.
* 358618: the intended n>=3 tree-independence statement is proved in EJC 32(2)
  (2025), P2.30, Theorem 7; even-order nonvanishing has a separate published proof.
  The corpus's damaged n≠3 formulation is not a valid discovery route.
* 360369: Brooks–Linz arXiv:2610.12433, Theorem 5, gives the full bound and
  equality characterization. Its primary statement and proof were read.
* 355648: the live Omega problem body already prints n=27, lengths (12,6,5),
  with the complete distance multiplicity table refuting the proposed classification.
* 365781: the cited source reports resolution of the stronger chorded-cycle
  conjecture. Subgraph containment gives the reserved cycle claim. Original
  cited proof [9] was not independently read here; this depth limit is retained.

Completed computations (diagnostics, not Lean proofs):

* 362890: exact distribution polynomials for every n<=250; predicted peak two
  holds throughout. Independent full permutation enumeration validates n<=7.
* 355432: every ascent/descent signature through n=25, extending the source's
  n<=19 computations; source's intended reversal convention is included. No failure.
  Even n is classical Niven/de Bruijn; odd-case classical-subsumption risk remains.
* 355534: full coefficient checks on 104 coprime pairs, 2<=s<=9, 2<=r<=24,
  rational Catalan count at most 180000, all passing. Every pair/count is logged.
* 353384: 367 logged 3-connected random/structured graph cases at n=7..11,
  all consistent. These include duplicate structured graphs, not 367 isomorphism classes.
* 358772: every permutation of n=4..9 in the standard simple-root matrix model;
  the triangularizable permutations are precisely separable in this range.
  No arbitrary-shape KL action or semantic endpoint is certified.
* 359681: shifted-power-sum q-bracket rank model at every even weight 2..30,
  using coefficients through q^30 modulo 1000000007; full expected rank in each case.
* 354662: 7100 reduced wiring words at n=7..40. All decided cases were
  3-colorable; solver-unknown counts are in outputs/computation-summary.json.
  No exhaustive arrangement census or general part (a)/(b) coverage is claimed.

Source and prior-art evidence:

The 20 original raw JSONL lines, including newline, are in raw/. extracted.json
records one-based corpus lines and chunk/raw/statement SHA-256 values. All 33
versions listed in the current abstract pages of the 20 source arXiv records
were downloaded and converted to inert text; outputs/version-anchors.json
tracks conjecture anchors and hashes. Review depth differs by target and is
stated explicitly. Retaining a full text does not mean auditing every proof.
Historical ledger hashes and extracted accepted/excluded families are in
outputs/inherited-ledgers.json; history-matches.txt retains numeric false positives.

Current GitHub HEADs (via /commits/HEAD): OpenAI/math
4eaee87548250b2682affda7d05d947c05554bae; Omega
1b1e5c823ca043cad728ae309c2cda9420767bdb. Both initial recursive root trees
were truncated. Complete, untruncated D5, Problems, and OpenAI preprints
subtrees were then fetched separately and their receipt hashes preserved.
Path screens do not clear all proof content. The Omega separable peak-three
files concern source Conjecture 2 and explicitly retain a tail gap; they must
not be used to exclude assigned Conjecture 1 (362890). The 2026 Robin successor
only settles convex fixed-area domains, not the full assigned claim.
No 403/429 route was retried; all saved HTTP retrieval receipts here are 200.
Search-result material and bounded non-findings are not worldwide novelty clearance.

Execution and limitations:

All successful experimental processes used scripts/limited.py: affinity two CPUs,
CPU 120 s, wall 140 s, sampled RSS 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR.
RSS monitoring samples the direct process and is not a cgroup proof of a transient
or descendant bound. Actual recorded memory was far below the ceiling.
The C++ attempt could not launch (g++ absent); Python replaced it. The first gamma
script could not import networkx; a dependency-free implementation replaced it.
The failed launch/import logs are retained rather than concealed.

One protocol error occurred: permutation250 was started while pseudoline-large
was still running. It was terminated after 16.829 s, with receipt returncode -15.
The two jobs shared the same two-CPU affinity, but this nonetheless violated the
one-heavy-process rule. A file lock was then added to the wrapper and
permutation250-serial completed alone. This is an explicit process-compliance
limitation. No result from the interrupted run is needed for coverage.

No child agents, git operations, uploads, external messages, or browser tabs were
used. No Lean file was made: no genuine full endpoint survived. No claim of a
Lean build, axiom audit, leanchecker replay, or upstream rebuild is made.
Full scripts and outputs are retained; there is no background research process.
'''
(D/'SUMMARY.md').write_text(summary)
cs={}
for f in ['pseudoline','pseudoline-large','gamma-pure','dyck','kl-root','descendent','tournament25']:
 rows=[json.loads(l) for l in (D/f'logs/{f}.log').read_text().splitlines()]
 cs[f]={'rows':len(rows),'receipt':json.loads((D/f'logs/{f}.receipt.json').read_text())}
 if f.startswith('pseudoline'):cs[f].update(sampled=sum(x['sampled_reduced_words'] for x in rows),colorable=sum(x['3colorable'] for x in rows),unknown=sum(x['solver_unknown'] for x in rows))
cs['permutation250-serial']={'receipt':json.loads((D/'logs/permutation250-serial.receipt.json').read_text()),'complete_rows':sum(l.startswith('{') for l in (D/'logs/permutation250-serial.log').read_text().splitlines())}
(D/'outputs/computation-summary.json').write_text(json.dumps(cs,indent=2)+'\n')
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':manifest},indent=2)+'\n')
print('validated raw hashes, newline preservation, exactly 20 reserved IDs; no Lean endpoint asserted')
