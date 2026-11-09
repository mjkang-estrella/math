import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3, 6*1024**3))
from pathlib import Path
import json, hashlib, datetime, shutil

P = Path(__file__).resolve().parent.parent
R = P/'cmdrr-five-three-source-review-sol-r1'
L = P/'cmdrr-five-three-formal-sol-r2'
BASE = P/'flat-balance-bridges-formal-pi-r5'
ROOT = P/'root-intake-r60'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p, v):
    assert not p.exists(), str(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(v, indent=2)+'\n')
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
assert not L.exists(), 'Fresh formal lane required; never overwrite an existing packet.'
integrity = json.loads((ROOT/'cmdrr-review-r1-integrity.json').read_text())
assert not integrity['manifest_mismatches'] and not integrity['frozen_mismatches']
assert json.loads((P/'ledger.json').read_text())['accepted_new'] == 55

decision = {
 'utc': now, 'mathdb_id':326555, 'review_lane':str(R),
 'integrity_receipt':str(ROOT/'cmdrr-review-r1-integrity.json'),
 'status':'PROSPECTIVE_QUALIFICATION_FOR_FORMAL_IMPLEMENTATION_ONLY',
 'source_literal_and_final':'PASS: explicit source-definition binding; all22 final pages reviewed; no source change detected',
 'ordinary':'Independent full ordinary PASS, no unresolved mathematical lemma reported',
 'prior':'Bounded no match; no concrete applicable unread theorem identified. Berman-Smith2013 companion403 remains an explicit access limitation; no global priority claim.',
 'significance':'Adopt provisional positive assessment: structural incidence identity supplies missing content beyond parity; no complete public/routine subsumption bridge established in reviewed bodies.',
 'family':'Bounded distinct scope against55 accepted new+39 prior scopes; at most one result',
 'root_adjudication':'The disclosed companion access limit does not by itself veto authorized formal research. It remains in the final qualification record; never claim its proof was read or worldwide novelty was established.',
 'procedure':'Preserve all4 nonzero runner receipts, outside-runner missing-image attempt(no bytes read), skill-read exception, failed render recovery, and guard innerexit1/outerexit0 distinction. No blanket operational-compliance PASS or waiver.',
 'authorized_next':'Fresh GPT-6.1 Sol high/default implementation of full source-defined nonexistence, generic relabeling bridges, audits, controls, source-only replay and paper; no network or children',
 'acceptance':'NOT_ACCEPTED; independent full formal review and final root adjudication remain unpaid',
 'credit':0, 'campaign_accepted_new':55, 'campaign_target':60, 'previous_accepted':39,
 'root_math_or_Lean_execution':False,
 'frozen_source_inputs_untouched':True,
 'review_sha256':sha(R/'REVIEW.md'), 'proof_sha256':sha(R/'INDEPENDENT-PROOF.md')
}
decision_path=P/'cmdrr-five-three-source-parent-integration-sol-r1.json'
save(decision_path,decision)

old=ROOT/'inherited-denials-r432.json'
den=json.loads(old.read_text());den['utc']=now
url='https://paperzz.com/doc/8919938/balanced-equitable-mixed-doubles-round-robin'
den['blocked_keys']=sorted(set(den['blocked_keys']+['paperzz.com/doc/8919938/balanced-equitable-mixed-doubles-round-robin']))
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+['berman-smith2013 balanced equitable mixed doubles round-robin tournaments']))
den['records'].append({'url':url,'reason':{'status':403,'body_obtained':False,'artifact':'Berman-Smith2013 Balanced equitable mixed doubles round-robin tournaments'},'evidence':{'path':str(R/'guard-ledger.jsonl'),'sha256':sha(R/'guard-ledger.jsonl')}})
den['root_cmdrr_companion_scope']='The identified Berman-Smith2013 companion is unavailable across ALL alternate hosts, queries, versions, caches, mirrors, author/DOI deliveries after403. No retry or indirect recovery. This is a bounded prior-access limitation, not an asserted applicable theorem. Cached target1310.5240v1 and actual2015final already acquired are distinct and authorized only where copied.'
denpath=ROOT/'inherited-denials-cmdrr-review-r1.json';save(denpath,den)

L.mkdir();origins={}
def copy(src,rel):
    dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(src,dst);assert sha(src)==sha(dst)
    origins[rel]={'path':str(src),'sha256':sha(src)}
for name in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh']:
    copy(BASE/name,name)
for n in ['src','build','audit','receipt','logs','tmp','cache','results','manuscript','output/pdf']:
    (L/n).mkdir(parents=True,exist_ok=True)
for name in ['REVIEW.md','INDEPENDENT-PROOF.md','DORMANT-OBLIGATIONS.md','keyedreview.json','ACCESS-SEARCH-READ-INVENTORY.json','RESOURCE-INVENTORY.json','SHA256-MANIFEST.json','guard-ledger.jsonl','frozen-before.json','frozen-after.json']:
    copy(R/name,'inputs/review/'+name)
for name in ['literal326555.jsonl','literal-provenance.json','original-twenty.jsonl','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','registry-and-pinned-inventory.json','accepted55-routing.json','prior39-routing.json','sources/design.pdf','sources/design.txt','sources/design-final.pdf','sources/design-final.txt','sources/design-final-landing.html']:
    copy(R/'inputs'/name,'inputs/author/'+name)
copy(decision_path,'inputs/ROOT-QUALIFICATION.json')
copy(ROOT/'cmdrr-review-r1-integrity.json','inputs/ROOT-INTEGRITY.json')
copy(denpath,'inputs/INHERITED-DENIALS.json')

pack=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
binpath=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pins={'lean_version':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','lean_bin':str(binpath/'lean'),'lean_sha256':sha(binpath/'lean'),'leanchecker_bin':str(binpath/'leanchecker'),'leanchecker_sha256':sha(binpath/'leanchecker'),'packages_root':str(pack),'runtime_version_and_mathlib_pin_verification':'Worker must verify under runner before accepting any compilation. Root only hashed binaries, did not execute Lean or git.','immutable':'NEVER overwrite this PINS.json; generated build/extraction plans must use distinct filenames.'}
assert pins['lean_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert pins['leanchecker_sha256']=='ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'
save(L/'PINS.json',pins)
upstream=[str(pack/x/'.lake/build/lib/lean') for x in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
env='#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\n'
env+='LEAN_BIN='+str(binpath)+'\nexport PATH="$LEAN_BIN:$PATH"\n'
env+='export LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n'
(L/'env.sh').write_text(env)

task='''You personally are the ONLY worker in this lane, GPT-6.1 Sol, high reasoning, default service. No children, other providers/models, network/search/browser/curl/wget/HTTP, git, installs, accounts, shared/parent writes, /tmp artifacts, background jobs, or protected-peer access. Root is orchestration only. Current accepted55/60 beyond39 prior; no credit for ordinary proofs/helpers. Root has prospectively qualified326555 for full formal research, NOT accepted it. Read inputs/ROOT-QUALIFICATION.json faithfully; inaccessible companion403 remains a limitation, not an asserted prior theorem or authorization to retrieve it.

Work ONLY in this NEW lane. FIRST command exactly: timeout20 via shell equivalent `timeout 20 python3 -I -B ABS_LANE/bootstrap.py`. It reads TASK and full ancestor AGENTS; preserve its first receipt. SECOND command exactly `timeout 140 python3 -I -B ABS_LANE/verify_frozen.py before`. No mathematical/source/API reads before these. Then via supplied runner read PINS, root qualification/integrity, copied literal326555, original source Definition1.2, author proof/plan, independent REVIEW, INDEPENDENT-PROOF and DORMANT-OBLIGATIONS in full (split if truncated). All research inputs are OWN COPIES. Embedded external paths are provenance only: do not follow them. The supplied helpers, own production files and pinned mathlib/core implementation/API files are the only additional allowed reads. No other campaign lane, reservation glob, polling, or broad repository history; r432/r433 active and all other crown/bunkbed/polynexus/code-loop lanes protected. No legacy production imports/build paths.

AFTER mandatory input reading, FIRST NEW-PROOF operation MUST be WRITE of faithful source model module src/CMDRRBase.lean followed immediately by its real strict check.sh CMDRRRBase (use the ACTUAL written module name CMDRRBase). Do not precede this by broad API inspection, probes, a planning-only turn, or baseline rebuild. Use targeted imports to keep memory low. Subsequent real diagnostic-driven API lookup/probes under runner are permitted. Prove the FULL literal endpoint, not a helper milestone: keep progressing dependency-ordered through the nonexistence theorem and its bridges, audits, clean replay and paper. Persist a real checkpoint at every strict-green module so interruption never loses compiled evidence; if unable to finish, explicitly return precise outstanding lemmas and last real exits, not future-tense claims.

SOURCE/FIDELITY:326555 asserts NONEXISTENCE of CMDRR(5,3), not its negation. k=3 SPOUSE PAIRS by the explicit paper-definition binding; never encode3rounds. Final2015source Definition1.2/Conjecture2.4 reviewed across all22pages (printed66-67/69); no rounds/resolvability assumption. A game is an UNORDERED pair of mixed teams with DISTINCT men and women, schedule initially arbitrary finite occurrences with source partnership/opposition multiplicities. Define literal source predicates, not answer-encoding parity/cycle predicates. The source says every nonspouse mixed pair partners and opposes once, spouses never share a game, same-sex pairs meet once except each SINGLE repeats against ONE OTHER SINGLE (specialization to two singles must be derived). Formalize exactly and include source-to-model equivalence/count bridges. Do not silently assume occurrence injectivity, inverse maps, row/column types, counts22/11, odd/even signs or final contradiction as fields/hypotheses. Final endpoint must cover arbitrary5-element male and female types with arbitrary matching of size3, via explicit bijective relabeling to canonical three spouse indices and preservation of counts. A canonical Fin5 theorem alone remains an unpaid source bridge. Faithful finite games may use Sym2 or an equivalent quotient/Finset representation with a proved unordered/source correspondence; no schedule enumeration/SAT/CAS or unchecked certificates. Kernel decide on tiny Boolean arithmetic is permissible; no native_decide, native compute axiom, external solver, added axioms, sorry/admit/unsafe/partial/extern/implementedBy.

DEPENDENCY PIPELINE (ordinary proof already independently checked; implement all of it, repair only on actual evidence):
1 Literal games, occurrences, spouse matching, source counts, normalization and transport;22allowed partnership cells,11games, mixed-opposition-derived row/column inverses, no fixed points.
2 Two-cycle games are distinct; only singles pair45 may repeat globally. Spouse rows on4symbols must be4cycles; complementary edge45 iff edgejk via degree counts. Fully justified game incidence counts A,B,z give A+B=1+z. A single-row2cycle must be45, remainder3cycleH; implies A=0 and B=2-z, hence2z=1 impossible. All single rows5cycles; prove full sex-swap transport to columns, not merely assert analogy.
3 Genuine permutations U,C,T of exactly22allowed cells; T fixed-point-free involution with11 two-orbits; C composed T=U with correct orientation; row/column disjoint supports give signU=signC=-1, signT=-1 yet multiplicativity forces+1. Formal cycle/sign lemmas can use pinned mathlib with exact hypotheses proved. No proxy endpoint/finite search.
4 Assemble universal noCMDRR(5,3) with all source relabeling and occurrence bridges; exact literal theorem/source map. Broad model constraints cannot be added just to simplify proof.

EXECUTION DISCIPLINE: every mathematical/API/documentary subprocess/read/audit/render under OWN supplied capped runner; use `source ABS_LANE/env.sh` before direct runner calls, then `timeout 140 python3 -I -B ABS_LANE/runner.py UNIQUE_LABEL -- COMMAND ARGS`. check.sh/checker.sh source env automatically. check.sh MODULE uses lean4.34.1 -j1 -M3500 -DwarningAsError=true, ownbuild ONLY + upstream packages. Module-name checker.sh MODULE uses pinned PATH. No tail pipelines, true exits/full logs/receipts every attempt; preserve failed attempts and never rerun unchanged failed source. Use write_lane.py via python3-I-B for all authored own files; input is STDIN (TEXT ONLY), not --base64. For rendered/document binaries use an explicitly documented capped lane-contained generator; don't pass binary data to this text writer. Build wrappers/runner immutable: caps2cores CPU120, AS12GiB, sampled groupRSS6GiB, devguard130s, wall140, arena2. All groups reaped; disclose sampling limits instead of asserting perfect cgroup enforcement. PINS.json is IMMUTABLE: verify supplied binary hashes and actual mathlib revision metadata without git; version invocation under runner permitted. Any pin mismatch stops acceptance. Build/extraction plan MUST have another filename; never overwrite PINS or frozen manifests, even with same-purpose generated content.

AUDIT/CLOSEOUT (all required before technical PASS): strict builds and leanchecker of EVERY production module; whole-environment enumeration incl private/generated production declarations and transitive body-origin DAG; no hidden trusted conclusion, unsupported imported theorem or nonallowed axiom. Only propext/Classical.choice/Quot.sound allowed. Record complete declaration names/counts, exact per-endpoint closures and axioms from actual audit, do not extrapolate. Include source-definition printouts/maps and semantic negative controls that fail as expected under intentional statement/model mutations with their true exit/logs. Positive controls must be substantive and nonvacuous. Fresh extracted source-only rebuild from EMPTY build, pinned upstream-only LEAN_PATH (no legacy/author oleans), identical source hashes, checker all modules. Verify hashes AFTER checker. Preserve every failed command as nonpass, not overwritten by success.

Write readable complete manuscript with source statement, exact definitions, whole ordinary argument, scope/source gloss explanation, formal theorem, audit/replay evidence, and all prior/access/process limits. For PDF creation read available PDF SKILL.md using runner, announce skill use, execute its authoring marker exactly ONCE for planned PDF; this explicit external skill access is allowed. No install/LaTeX dependency required; available groff/reportlab etc allowed. PDF under output/pdf, render all pages and actually visually inspect each (direct image display permitted for OWN rendered/documentary images; record invocation/scope as distinct UI evidence, not false process telemetry). Do not claim a body read from failed OCR; copied scanned final may be rendered read-only. All source claims must cite actual copied primary pages, not search snippets. No worldwide novelty claim; explicitly retain unread2013companion limit and root prospective decision.

At seal: verify_frozen.py after (cannot edit frozen files), results/326555.json credit0/campaign55of60, SUMMARY.md, CHECKPOINT.md, receipt+source+olean+log inventory and actual SHA256 manifest including ALL completed receiptJSONs, copied inputs, helpers, plans, sources, paper/renders. Name exact terminal noncircular self-exclusions (manifest and final seal receipt/log), no vague excludes. Preserve all prior deviations; do not assert universal procedural compliance merely from hashes. No ledger mutation/selfacceptance. Independent full final source-to-Lean/proof/audit/manuscript review and root acceptance remain separate. Final handback only ACTUAL disk state with links, exact last exits/hashes, remaining obligations if partial. All processes reaped. No additional delegates.
'''
task=task.replace('ABS_LANE',str(L)).replace('check.sh CMDRRRBase (use the ACTUAL written module name CMDRRBase)','check.sh CMDRRBase')
(L/'TASK.txt').write_text(task)
save(L/'INPUT-ORIGINS.json',origins)
save(L/'ROOT-PREP.json',{'utc':now,'lane':str(L),'mathdb_id':326555,'scope':'Full literal Lean implementation, audits, replay and manuscript; prospective research only','model':'gpt-6.1-sol','provider':'codex','reasoning_effort':'high','service_tier':'default','children':False,'network':False,'helper_origin':str(BASE),'helper_scope':'Generic process wrappers only; no old mathematical source/olean copied','legacy_LEAN_PATH':False,'accepted_new':55,'credit':0,'protected_active_peers':['expanded-corpus-r432','expanded-corpus-r433']})

# Freeze completed provenance and own immutable packet, NEVER active peer files.
frozen=dict(json.loads((R/'frozen-inputs.json').read_text()))
review_manifest=json.loads((R/'SHA256-MANIFEST.json').read_text())
for row in review_manifest['files']:
    q=R/row['path'];assert sha(q)==row['sha256'];frozen[str(q)]=row['sha256']
for name in review_manifest['terminal_noncircular_self_exclusions']:
    q=R/name;frozen[str(q)]=sha(q)
for q in L.rglob('*'):
    if q.is_file():frozen[str(q)]=sha(q)
frozen[str(decision_path)]=sha(decision_path);frozen[str(denpath)]=sha(denpath)
for s,v in frozen.items():
    assert 'expanded-corpus-r432/' not in s and 'expanded-corpus-r433/' not in s
    assert sha(Path(s))==v, s
save(L/'frozen-inputs.json',frozen)
save(ROOT/'cmdrr-formal-r2-ready.json',{'utc':now,'lane':str(L),'task':str(L/'TASK.txt'),'task_sha256':sha(L/'TASK.txt'),'frozen_bindings':len(frozen),'decision':str(decision_path),'latest_denials':str(denpath),'accepted_new':55,'credit':0,'other_active_lanes':['expanded-corpus-r432','expanded-corpus-r433'],'root_execution':'Documentary metadata preparation only; no Lean/math execution'})
print(json.dumps({'ready_lane':str(L),'frozen':len(frozen),'decision':str(decision_path),'task_sha256':sha(L/'TASK.txt')}))
