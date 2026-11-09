import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6 * 1024**3, 6 * 1024**3))
from pathlib import Path
import json, hashlib, shutil, datetime

P = Path(__file__).resolve().parent.parent
BASE = P / "expanded-corpus-r420"
def sha(q):
    return hashlib.sha256(q.read_bytes()).hexdigest()
def write(q, value):
    q.write_text(json.dumps(value, indent=2) + "\n")

COMMON = """
GPT-6.1 Sol high/default ONLY personally, no children/model/provider fallback.
Root orchestrates. Current55/60 beyond39 prior94total. Credit0, no acceptance,
no formal dispatch. Author proofs are proposals, not trusted deductions.
FIRST shell command EXACTLY: timeout 20 python3 -I -B LANE/bootstrap.py
Read FULL printed TASK/AGENTS.
SECOND EXACTLY: timeout 140 python3 -I -B LANE/verify_frozen.py before
Bootstrap and standalone before/after verifiers are explicit exceptions.
ALL other substantive local work via immutable EXACT ABSOLUTE LANE/run.py
UNIQUE_LABEL consuming Python stdin; writes via LANE/write_lane.py, except
guard/verifier-owned outputs. Child cwd own lane, not workspace. No direct
navigation/readers, --help, LABEL --command probes, helper/cap modifications,
unchanged failed reruns or bootstrap repeats. Preserve failed receipts.
Read own copied inputs ONLY; external source paths are provenance and only
authorized before/after verifiers may hash external frozen author files.
No campaign recursion, embedded history/source paths, old certificates.
All old code-loop/Polynexus/crown/tournament/bunkbed/Hat formal bodies protected.
All writes own lane only, no /tmp/parent/shared/author/dependency/git/install/
publish/browser/account/messages/children/background. All76 r395 acquisitions
permanently quarantined. No mathematical programs, enumeration, numeric tests,
CAS, solvers, Lean/compiler/checker/formal API/library probing.
Do ordinary mathematics personally. Documentary/hash/PDF processing permitted.
Use PDF read skill for material visuals; scanned final cannot be paid by failed
OCR. No new manuscript/PDF authoring requested.

Audit literal/source hypotheses and every proof bridge independently. Keep
literal/source-original/final/ordinary/prior/novelty/significance/family/formal/
procedure/acceptance gates separate. Repair ordinary gaps or give precise GAP.
Supplied55 full accepted statements and39 trusted prior scopes are scope only,
no certificate re-audit. One outcome max per family; no helper/parameter recount.
Actual applicable primary theorem AND proof before reliance; abstract/search/
openlabel/README/roothead/nohit is not proof or novelty clearance. Specific
applicable unread theorem is precise HOLD; generic worldwide unknown not veto.
Routine exclusion needs COMPLETE applicable prior-to-target bridge and strongest
contrary assessment, not smallness/shortness/standard tools/Lean burden.
If all ordinary/scientific gates pass, supply dormant full-literal implementation
obligations only, no dispatch. Future Lean4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
only propext/Classical.choice/Quot.sound, no sorry/admit/new axioms/unsafe/
native_decide. Full bridges, independent fidelity/deep audit/source-only strict
replay/paper/root acceptance remain required later.

ACCESS: source_get_guard.py SOLE public GET client under run.py. ONE manually
selected persisted exact plan/invocation: url/routes/destination/source_identity/
purpose, routes ['TARGET'], NEW sources destination, identity/purpose >=12 chars.
Focused review max8 GET-HOPS total/perID, every redirect precharged,20s/24MiB.
No seed lists/URL arrays/batch loops/traversal/custom HTTP/requests/curl/wget/
HEAD/native open-fetch/browser/API/account/forms/POST/TLS/cookie bypass.
Every denial/challenge/error/timeout/empty/oversize artifact unavailable across
ALL host/query/version/cache/mirror/alternate delivery; never retry. Guard alone
writes payload/append-only hashchain/lock. No helper/ledger/budget/charging/
denial changes or historical backfill. Read saved outcome after failure. STOP
network FAIL/quarantine on policy/budget breach. Inherited denial union r432
binds all older final frames429/QMC TLS/distance403/rainbow403/CGT13/Gallian/
r395/CPP2019 redirect-only artifacts. Distinct prior work is not automatically
denied, but cannot be indirect delivery of denied work. No refetch cached source/
final/metadata/registry roots. Current saved root heads only navigation; actual
body if concrete match.
Native SEARCH whole review max2 actual calls6 query strings. PRECHARGE exact
plan/live counter via fixed runner/writer BEFORE call. Save FULL actual response
immediately (JSON string legitimate), inventory actual use, no reset/engine HTTP.
This explicit independent targeted budget is not rerun of author broad searches.

Resources fixed affinity<=2,childCPU115/supervisor120,AS6GiB,sampled group RSS6GiB,
deadline130/outer140,arena2. True exit/full saved output/receipts/synchronous reap.
Sampling misses transients; native/writer peaks unavailable, no universal
cgroup/process claim. Standalone verifier CPU120 exception, never nest under115.
Frozen helpers/inputs/author hashes/origins/TASK/reservation/sidecar/denials/policy
immutable; own outputs/budget/guard ledger mutable.
DELIVER actual REVIEW.md/keyedreview.json with every separate gate, full
independent proof or GAP.md, source-obligation map, strongest objections/contrary
cases, actual source/read/figure/access/search/resource inventories. Preserve
failures. Final standalone verify_frozen.py after and actual SHA manifest of
EVERY completed receiptJSON/helper/inputs/source/plans/search/hashchain/
frozen-after/reports; precisely named terminal noncircular self-exclusions.
All jobs reaped, no later frozen writes. Finish concrete scope, no future-tense
acknowledgment-only handoff. No acceptance, credit or formal execution.
"""

SPECS = [
 dict(lane="cmdrr-five-three-source-review-sol-r1", target=326555,
      author="expanded-corpus-r430", source="https://arxiv.org/abs/1310.5240",
      peers=["cpp-ma-prior-source-review-sol-r1", "expanded-corpus-r432"],
      files=["ACTUALBRIEF.md", "FULLCANDIDATE.md", "DORMANT-SOL-FORMAL-PLAN.md",
             "literal-provenance.json", "INVENTORIES.json",
             "registry-and-pinned-inventory.json", "prior-reconciliation.json",
             "search-budget.json", "SHA256-MANIFEST.json", "original-twenty.jsonl",
             "design_final_ocr.receipt.json"],
      sources=["design.pdf", "design.txt", "design-final.pdf",
               "design-final.txt", "design-final-landing.html"],
      detail="""
Independent FULL source/literal/ordinary/prior/significance review CMDRR(5,3)
NONEXISTENCE, not refutation of its negation. Literal vaguely says k games/rounds
ACCORDING TO PAPER DEFINITION. Actual Berman-Wakeling Definition1.2 k=spouse pairs.
Adjudicate faithful literal source-binding explicitly, not wording exploitation.
Cached1310.5240v1 plus actual scanned JCMCC95(2015)65-86 final. Author visually
read final PDF pages3,5,10,11,12,14,15,21 only. Compare unread final pages,
conclusion/references as relevant (all22 if needed), Def1.2pp66-67,Conj2.4p69,
Theorem3.8p76. No rounds/resolvability assumption. Source exact mixed
partner/opposition multiplicities, spouses never game, same-sex counts.
Cached full final accessible, no network refetch; failed OCR not proof.

Audit FULL proof:5M/5F,3 disjoint spouse pairs canonical1,2,3,singles4,5.
22 nonspouse partnership cells imply11games. Male row p_i maps partner female
to opponent female, column analog; no fixed points. A2cycle repeats female
pair, possible only45. Spouse row4symbols thus4cycle not2+2. On4cycle{j,k,4,5},
edge45 iff edgejk. A counts spouse-menpair/women45, B men45/spouse-womenpair,
z men45/women45. Sum edge indicators over3spouse men gives2+A-z=3-B, hence
A+B=1+z. If single row2cycle45, remaining3cycle, both female45games contain
him so A0; he opposes other single exactly2times, so B=2-z, hence2z=1,
impossible. Therefore single rows5cycles. Sex symmetry columns. U row and
C column signs -1 each. Opposite-team T fixedpointfree involution on22cells
has11transpositions, sign-1; C composed T=U forces sign+1 contradiction.
Pay arbitrary spouse canonicalization, genuine bijections/inverses, uniqueness
of games from partner cells, game multiplicity vs ordered teams,45total2,
distinct games in2cycle, cycle classification without schedule enumeration,
4cycle opposite-edge indicator, A/B/z doublecount, column direction and sign.
Do not assume single row5cycle without the structural identity. Repair gaps
or precise GAP. Universal all admissible schedules, no extra latin/resolvable
hypotheses.
Strong positive case exact long-standing exception; sign multiplicativity
alone insufficient without identity eliminating3+2types. Strong contrary
case general design parity/classification may already settle it. Targeted
actual current primary companions/nonexistence results/corrections. Author
found no specific matching prior claim; no world-absence claim. Smallness
alone not routine. If full ordinary/source/prospective scientific PASS,
dormant Lean route only: exact unordered games/multiplicities, arbitrary
spouse bijection, canonical cells/count/cycle/sign lemmas, full nonexistence
endpoint; every formal obligation unpaid, no dispatch.
"""),
 dict(lane="cpp-ma-prior-source-review-sol-r1", target=326886,
      author="expanded-corpus-r431", source="https://arxiv.org/abs/1312.4716",
      peers=["cmdrr-five-three-source-review-sol-r1", "expanded-corpus-r432"],
      files=["ACTUALBRIEF.md", "FULLCANDIDATE.md", "DORMANT-SOL-FORMAL-PLAN.md",
             "literal-provenance.json", "access-classification.json",
             "current-registry-inventory.json", "prior-reconciliation.json",
             "HISTORY-SCOPE-NOTE.md", "search-budget.json", "SHA256-MANIFEST.json"],
      sources=["cpp.pdf", "cpp.txt"],
      detail="""
Focused DISTINCT Ma primary theorem comparison and independent ordinary/source
review326886. Exact oddprimep,r=p-1,k>0,E=F_(p^(rk)),a nonzero,
a^(p^k-1)=-1,d=(p^(rk)-1)/(p^k-1)+1: a^-1 X^d is COMPLETE permutation
polynomial (both f and f+X bijective). Cached1312.4716v2 defs/Lemmas4-5/
Conj2/Remark5 proves k1 only; original final2015 body unread, not denied.
Main gate: specific Ma et al. Theorem3.2 is reported already proving exact
target. Feng-Lin-Wang-Wang Further results on complete permutation monomials
over finite fields,1708.06955/DOI10.1016/j.ffa.2019.01.003Theorem5 reportedly
extends it. That2019 artifact is UNAVAILABLE: DOI->linkinghub
PIIS1071579719300036 gave only2684byte Redirecting HTML/script/meta refresh.
ALL new2019host/version/arxiv/cache/mirror/delivery prohibited. No fetching
its references through another route, no ledger backfill. DISTINCT Ma work
identity needs independent bibliographic identification; not yet denied.
Use bounded targeted search/GET to identify actual Ma PRIMARY theorem AND
proof, date, hypotheses and complete target specialization. No speculative
CPP literature sweep. If body unavailable stop that artifact, precise HOLD.
If full target covered write complete prior bridge+strong contrary case,
recommend public exclusion with zero credit. Excerpts saying theorem solves
it do not authenticate body. If only partial isolate exact residual.

Audit ordinary proof as needed:K=F_(p^k) insideE,a^q=-a impliesb=a² inK
nonsquare. H(t)=t(t²-b)^((p-1)/2) permutesK by collision ratio
z=(x²-b)/(y²-b); squared equality and charp force
b=y²((z-1)/z)^(p-1) if z!=1, contradiction nonsquare;z1 cancellation
restores signs, zero/division cases separate. Norm(t+a)=(t²-b)^((p-1)/2)
by alternating q-conjugates; power-map gcd(N+1,(q-1)N)=1;
Norm F=H composed Norm for F=x(Norm x+a), then fiber injectivity and
finite surjectivity. a^-1 normalization gives both CPP maps. Actual subfield/
Frobenius/norm/gcd/all oddp/k/admissible a/source exponent bridges, not
arbitrary-field proxy. No formal API. Exact older full public theorem if
authenticated decisive irrespective short new proof. Original final/correction
gate separate, does not erase earlier exact literal public solution.
Preserve author late source-family reconciliation process limitation.
If Ma comparison remains unread, retain specific HOLD, not generic veto.
""")
]

summaries = []
for spec in SPECS:
    a = P / spec["author"]
    lane = P / spec["lane"]
    if (lane / "frozen-inputs.json").exists():
        frozen = json.loads((lane / "frozen-inputs.json").read_text())
        assert all(sha(Path(x)) == value for x, value in frozen.items())
        assert not (lane / "bootstrap-receipt.json").exists(), "Already launched lane"
        summaries.append(dict(lane=spec["lane"], target=spec["target"],
                              task_chars=len((lane / "TASK.txt").read_text()),
                              frozen=len(frozen), unchanged_ready_packet=True))
        continue
    assert not (lane / "bootstrap-receipt.json").exists(), "Cannot repair a launched lane"
    lane.mkdir(exist_ok=True)
    inputs = lane / "inputs"
    inputs.mkdir(exist_ok=True)
    origins = {}
    for name in ["bootstrap.py", "run.py", "write_lane.py", "verify_frozen.py",
                 "registry-roots.json", "source_get_guard.py", "model-policy-sol-only.json"]:
        shutil.copyfile(BASE / name, lane / name)
    shutil.copyfile(P / "root-intake-r60/inherited-denials-r432.json",
                    lane / "inherited-denials.json")
    def cp(src, dst):
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
        assert sha(src) == sha(dst)
        origins[str(dst.relative_to(lane))] = dict(path=str(src), sha256=sha(src))
    for name in spec["files"]:
        cp(a / name, inputs / name)
    target = spec["target"]
    if target == 326555:
        raw = next(x for x in (a / "original-twenty.jsonl").read_bytes().splitlines(keepends=True)
                   if json.loads(x)["mathdb_id"] == target)
        (inputs / "literal326555.jsonl").write_bytes(raw)
        origins["inputs/literal326555.jsonl"] = dict(
            path=str(a / "original-twenty.jsonl"), aggregate_sha256=sha(a / "original-twenty.jsonl"),
            selected_raw_sha256=hashlib.sha256(raw).hexdigest(),
            extraction="One unchanged complete newline JSONL object326555")
        searches = ["search-response-1.json", "search-response-2.json", "search-response-3.json"]
    else:
        cp(a / "literals/326886.jsonl", inputs / "literal326886.jsonl")
        searches = ["search-one-full.json", "search-two-full.json", "search-three-full.json"]
    author_gates = json.loads((a / "results.json").read_text())
    target_gates = author_gates.get("ids", author_gates)
    assert len(target_gates) == 20
    write(inputs / (str(target) + "-gates.json"), target_gates[str(target)])
    for name in spec["sources"]:
        cp(a / "sources" / name, inputs / "sources" / name)
    for i, name in enumerate(searches, 1):
        cp(a / name, inputs / "search" / ("author-response-" + str(i) + ".json"))
    cp(P / "root-intake-r60/accepted55-path-review-context.json", inputs / "accepted55-routing.json")
    cp(P / "spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json",
       inputs / "prior39-routing.json")
    cp(P / (spec["author"] + "-parent-integration.json"), inputs / "ROOT-AUTHOR-INTEGRATION.json")
    write(lane / "INPUT-ORIGINS.json", origins)
    write(lane / "reservation.json", dict(ids=[target], mathdb_id=target,
          role="Independent focused source/proof/prior/significance review",
          source_url=spec["source"], author_lane=str(a), accepted_new=55, target_new=60, credit=0))
    reservation_sha = sha(lane / "reservation.json")
    (lane / "reservation.sha256").write_text(reservation_sha + "  reservation.json\n")
    write(lane / "search-budget.json", dict(calls_used=0, queries_used=0,
          maximum_calls=2, maximum_queries=6, charged_before_call=True))
    task = ("Independent review MathDB" + str(target) + " in " + str(lane) +
            ". Reservation SHA256 " + reservation_sha + ".\nPROTECTED ACTIVE/PLANNED peers " +
            ", ".join(spec["peers"]) + ": NO read/hash/glob/list/poll even metadata.\n" +
            COMMON.replace("LANE", str(lane)).replace("TARGET", str(target)) +
            "\nSPECIFIC SCOPE:\n" + spec["detail"])
    (lane / "TASK.txt").write_text(task)
    frozen = {str(x): sha(x) for x in a.rglob("*") if x.is_file()}
    frozen.update({str(x): sha(x) for x in inputs.rglob("*") if x.is_file()})
    for name in ["bootstrap.py", "run.py", "write_lane.py", "verify_frozen.py",
                 "registry-roots.json", "source_get_guard.py", "model-policy-sol-only.json",
                 "inherited-denials.json", "INPUT-ORIGINS.json", "reservation.json",
                 "reservation.sha256", "TASK.txt"]:
        frozen[str(lane / name)] = sha(lane / name)
    write(lane / "frozen-inputs.json", frozen)
    write(lane / "ROOT-PREP.json", dict(
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), lane=str(lane),
        author_lane=str(a), frozen_count=len(frozen), reservation_sha256=reservation_sha,
        task_sha256=sha(lane / "TASK.txt"), accepted_new=55, credit=0,
        protected_peers=spec["peers"], budget=dict(GET_hops=8, search_calls=2, queries=6)))
    assert all(sha(Path(x)) == value for x, value in frozen.items())
    summaries.append(dict(lane=spec["lane"], target=target, task_chars=len(task), frozen=len(frozen)))
print(json.dumps(summaries))
