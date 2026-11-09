import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
R=P/'shoe-pair-discrepancy-formal-sol-r4';O=P/'shoe-pair-discrepancy-source-review-sol-r1'
L=P/'shoe-pair-discrepancy-formal-independent-review-sol-r5'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
assert not L.exists()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((R/'SHA256-MANIFEST.json').read_text());files=m['files']
assert len(files)==581 and all(sha(R/n)==v for n,v in files.items())
frozen=json.loads((R/'frozen-inputs.json').read_text());assert len(frozen)==685
assert all(sha(Path(n))==v for n,v in frozen.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==685 and after['mismatches']==[]
s=json.loads((R/'results/CHECKPOINT.json').read_text());rep=json.loads((R/'results/REPLAY.json').read_text());plan=json.loads((R/'results/PRODUCTION-PLAN.json').read_text());order=plan['order']
assert len(order)==len(set(order))==rep['module_count']==28 and rep['source_only'] and rep['upstream_only']
er=json.loads((R/rep['initial_build_empty_receipt']).read_text());assert er['exit']==0
receipts=[];latest={}
names=[n for n in files if n.startswith('receipt/') and n.endswith('.json')]
names += [n for n in m['exact_terminal_noncircular_self_exclusions'] if n.startswith('receipt/')]
for n in names:
 j=json.loads((R/n).read_text());assert Path(j['log']).resolve().is_relative_to(R)
 assert sha(Path(j['log']))==j['log_sha256'] and j['group_members_left']==[]
 row=dict(path=n,sha256=sha(R/n),label=j['label'],stamp=j['stamp'],exit=j['exit'],guard=j.get('guard'),group_members_left=j['group_members_left']);receipts.append(row)
 if j['label'] not in latest or j['stamp']>latest[j['label']]['stamp']:latest[j['label']]=row
for mod,artifacts in s['module_artifact_hashes'].items():
 for rel,v in artifacts.items():assert sha(R/rel)==v
for row in rep['postchecker_hashes']:
 mod=row['module'];assert mod in order
 assert sha(R/'src'/f'{mod}.lean')==sha(R/'replay/src'/f'{mod}.lean')==row['source_sha256']==row['extracted_source_sha256_after_checker']
 assert sha(R/'replay/build'/f'{mod}.olean')==row['olean_sha256_after_checker']
 for key in ['strict_receipt','checker_receipt']:
  j=json.loads((R/row[key]).read_text());assert j['exit']==0
  lp=j['env']['LEAN_PATH'].split(':');assert lp[0]==str(R/'replay/build') and all('/2026-10-14/formal/.lake/packages/' in q for q in lp[1:])
  if key=='strict_receipt':assert all(t in j['argv'] for t in ['-j1','-M3500','-DwarningAsError=true'])
 assert latest['lean_'+mod]['exit']==0
a=json.loads((R/s['audit']).read_text())
audit_summary={k:a[k] for k in ['axioms','complete','node_count','root_count','scope','tool_module','unsafe','not_final_transport_audit']}
audit_summary['endpoint_counts']={k:dict(count=v['count'],axioms=v['axioms'],unsafe=v['unsafe']) for k,v in a['endpoints'].items()}
assert a['complete'] and not a['unsafe'] and a['root_count']==259 and a['node_count']==29367
parent=P/'shoe-pair-discrepancy-formal-parent-integration-sol-r4.json'
save(parent,dict(utc=now,mathdb_id=324571,source_lane=str(R),manifest_files_verified=len(files),manifest_sha256=sha(R/'SHA256-MANIFEST.json'),manifest_mismatches=[],frozen_verified=len(frozen),frozen_mismatches=[],frozen_after=after,
 receipts=receipts,receipt_count=len(receipts),receipt_exit_counts=dict(collections.Counter(str(q['exit']) for q in receipts)),source_only_module_order=order,module_classifications=s['module_classifications'],replay=rep,audit_author_summary=audit_summary,
 nat_endpoint=s['nat_endpoint'],countable_endpoint=s['countable_endpoint'],paid_author_claims=s['paid'],unpaid=s['unpaid'],current_deviations=s['continuation_deviations'],historical_deviations=s['inherited_deviations'],prior_limits=s['prior_limits'],
 root_status='FULL_COUNTABLE_ENDPOINT_RECEIPTS_VERIFIED__INDEPENDENT_FINAL_REVIEW_UNPAID',root_scope='Documentary integrity/orchestration only, no mathematical/compiler/audit execution or independent source/body/visual verification',
 reporting_cautions=['23core/3controls/2named audits=28checked modules, separate audit tool is not a mathematical result','Historical no-final-endpoint/no-PDF statement refers to earlier stage, not current endpoint/paper','Final-source TV personal display was late, earlier machine read does not equal personal review','Sampled per-group/native/writer telemetry limits retained'],credit=0,accepted_new=55,target_new=60,previous_accepted=39))
L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json']:cp(R/n,n)
assert 'os.chdir(lane)' in (L/'runner.py').read_text()
for n in ['src','build','audit','receipt','logs','tmp','cache','results','output/pdf']:(L/n).mkdir(parents=True,exist_ok=True)
pins=json.loads((L/'PINS.json').read_text());assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
upstream=[str(Path(pins['packages_root'])/n/'.lake/build/lib/lean') for n in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
(L/'env.sh').write_text('#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\nLEAN_BIN='+str(Path(pins['lean_bin']).parent)+'\nexport PATH="$LEAN_BIN:$PATH"\nexport LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n')
C=P/'cmdrr-five-three-formal-sol-r4'
(L/'display_log.py').write_text((C/'display_log.py').read_text().replace(str(C),str(L)))
for mod in order:
 cp(R/'src'/f'{mod}.lean',f'inputs/author-src/{mod}.lean');cp(R/'src'/f'{mod}.lean',f'src/{mod}.lean')
for n in ['ShoeReachableAudit.lean','NegativeNoninjectiveCoding.lean']:
 cp(R/'src'/n,'inputs/author-audit-src/'+n)
for n in ['SUMMARY.md','TASK.txt','PINS.json','INPUT-ORIGINS.json','RUNNER-DELTA.json','DISPLAY-CALLS.jsonl','frozen-before.json','frozen-after.json','frozen-inputs.json','SHA256-MANIFEST.json','results/CHECKPOINT.json','results/324571.json','results/COMPLETED-RECEIPTS.json','results/FAILURES.json','results/INVENTORY.json','results/PRODUCTION-PLAN.json','results/REPLAY.json','results/SOURCE-MAP.json','audit/final-reachable-nodes.json','audit/final-reachable-report.json','audit/merge_final_reachable.py','audit/merge_reachable.py','manuscript/PAPER.txt','manuscript/paper.roff','output/pdf/shoe-discrepancy-completion.pdf']:
 cp(R/n,'inputs/author/'+n)
for row in receipts:
 n=row['path'];cp(R/n,'inputs/author/'+n);j=json.loads((R/n).read_text());rel=str(Path(j['log']).relative_to(R));cp(R/rel,'inputs/author/'+rel)
for n in ['REVIEW.md','INDEPENDENT-PROOF.md','DORMANT-OBLIGATIONS.md','keyedreview.json','SHA256-MANIFEST.json']:
 cp(O/n,'inputs/ordinary-review/'+n)
for n in ['literal324571.jsonl','literal-provenance.json','original-fixed20.jsonl','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','accepted55-routing.json','prior39-routing.json','registry-inventory.json','read-inventory.json','access-inventory.json','prior-reconciliation.json','sources/shoes.pdf','sources/shoes.txt','sources/shoes-final.pdf','sources/shoes-final.txt']:
 cp(O/'inputs'/n,'inputs/source/'+n)
for n in ['sources/multicolor-primary.pdf','sources/multicolor-primary.txt']:
 # Source filename is selected from the completed ordinary-review manifest below, not guessed delivery.
 pass
om=json.loads((O/'SHA256-MANIFEST.json').read_text());ofiles=om.get('files',om.get('sha256',{}))
names=list(ofiles) if isinstance(ofiles,dict) else [x['path'] for x in ofiles]
for n in names:
 if n.startswith('sources/') and Path(n).suffix in ['.pdf','.txt']:
  cp(O/n,'inputs/ordinary-primary/'+n)
cp(parent,'inputs/root/AUTHOR-R4-INTEGRATION.json')
cp(P/'shoe-pair-discrepancy-formal-parent-integration-sol-r3.json','inputs/root/HISTORICAL-R3-INTEGRATION.json')
cp(ROOT/'inherited-denials-r437.json','inputs/root/INHERITED-DENIALS.json')
save(L/'SOURCE-ORDER.json',order);save(L/'INPUT-ORIGINS.json',origins)
save(L/'ROOT-PREP.json',dict(utc=now,role='Independent full countable-law mathematical/formal/source/body-audit/manuscript review',mathdb_id=324571,model='gpt-6.1-sol',reasoning='high',service='default',children=False,network=False,protected_peers=['cmdrr-five-three-formal-independent-review-sol-r5','binary-projection-ratio-source-review-sol-r1'],credit=0,campaign=55,previous=39))
prefix=(P/'cmdrr-five-three-formal-independent-review-sol-r5/TASK.txt').read_text().split('Read inputs/source exact literal')[0]
prefix=prefix.replace(str(P/'cmdrr-five-three-formal-independent-review-sol-r5'),str(L)).replace('MathDB326555 CMDRR(5,3)','MathDB324571 equal-law shoe discrepancy').replace('shoe-pair-discrepancy-formal-sol-r4 and expanded-corpus-r437','cmdrr-five-three-formal-independent-review-sol-r5 and binary-projection-ratio-source-review-sol-r1')
detail='''Read copied literal, actual original/final shoe source, prior ordinary independent proof/review, source map, current and historical root integrations, audit tool and exact failed-memory history. No network needed/authorized. Exact final-source Section4 TV convention, strict alternation Sections9.1/9.2 Conj4eq19 and originaleq30 must be independently personally read BEFORE certification; inspect relevant full final context and any material visuals under own runner. Author's final-source TV personal display was late after compilation (earlier body machine read). Your fresh personal reading is independent review, not a retroactive procedural waiver. Original arxiv1211.6486v2, finalAAP47(2015)292-305 DOI10.1239/aap/1427814592. Current bound claimed on all PMF Nat and all countable color types, equal laws p=q, with strict left/right chronology L1,R1,L2,R2,..., collision first when either side matches an earlier/current opposite side, source independent-pair conditional color law vs chronological first-match color law; do not replace with simultaneous independent pairs, Poisson/random-side draws, finite support, positive-mass-only/finite-prefix restriction or caller-supplied distribution identities. Actual source endpoint supremum over all discrete laws strictly less1, strongeruniform255/256 bound; not merely each individual law<1.

Perform independent COMPLETE ordinary mathematics and source-to-Lean proof-body review, not just compiler success. Source order SOURCE-ORDER.json has28 proof/control/named-audit modules (23core,3control,2named-audit); separate tool ShoeReachableAudit and intentional negative are not mathematical results. Own build starts EMPTY (record before) and strict+module checker ALL28 copied sources, upstream-only no author/legacy oleans. Verify binary and actual package metadata pins BEFORE compiler. Fresh independent source-only replay and postchecker source/olean hashes. Do not edit author/frozen inputs; if proof fix necessary report exact minimal gap/fix, do not silently certify a repaired different theorem. Own independent audit/control modules allowed.

Audit ALL core bodies: iid measure/PMF/independence/cylinder probabilities, measurability, source conditional pair distribution p_i²/s on countably infinite support including s>0 and singleton/zero-probability colors, exact chronological first time+winner and a.s. termination/fallback irrelevance, actual disjoint unique-color GOOD blocks, isolated event bound minus collision union, strict-alternation indexing and off-by-one endpoints, K=floor(1/(4sqrt(s))) small-s and K>=1, K²-count and disjointness, Bernoulli/square-root inequalities with all cases including large-s shortcut, coordinatewise winningLaw_i>=p_i²/(256s), infinite summations/normalization/countableTV vs source subset/absolute-value convention, overlap->TV bound <=255/256, bounded supremum andstrict<1, sourceY/conditionalColorMeasure_toPMF bridges CONSUMED in endpoint. Author ordinary derivation used a conditional block argument; formal uses unconditioned four-coordinate lower bound E>=p_i²/2 and competing union<=K²p_i²s<=p_i²/16 giving >=7p_i²/16>=p_i²/4. Independently verify actual definitions/multiplicity/distinctness and every inequality, not just accept a different proof outline.

Review generic COUNTABLECOLOR transport and finite zero extension: actual injection colors->Nat/pushforward PMF, iid product measure under coordinate coding, first matchingtime and mark/color correspondence with source fallback only a.s., conditional pair measure transport and probability normalization, winner law pushforward, total variation subset-supremum equality, outside image/mass-zero coordinates, arbitrary countable/finite/empty alphabet hypotheses and PMF nonempty consequence. All promises in source map/endpoint names must be really proved and used rather than assumed law equivalences. Countable_color_strict_universal_supremum should consume Natbound through proved semantictransport, not new definition as answer or conclusion-bearing premise. Verify finite zeroExtension discrepancy and OUTSIDE zero-mass certificates are not merely a pointwise function extension unrelated to normalized source laws.

Independent DEEPBODY audit: enumerate whole environment origin metadata; select actual production-module roots INCLUDING private/generated, all their transitive TYPE/BODY dependencies, opaque-body dependencies where actual Lean permits extraction, exact perendpoint closures/axiom unions/origins/unsafe flags, memoized DAG and closure validation. Do not dump all unrelated imported bodies. Author reports259 roots/29367unionnodes/11exactclosures; only permitted propext Classical.choice Quot.sound. Rebuild/check actual audit tool, independently validate emitted edges and JSON merge roots/dependencies/counts; direct #print axioms alone is insufficient. Source-local names and generated instance/proof constants count too. No sorry/admit/new axiom/unsafe/partial/native_decide/extern/implementedBy or hidden unsupported theorem. Namespaced theorem wrapper alone is no source-fidelity evidence. Needed closures include countable_color_strict_universal_supremum, source_strict_universal_supremum, winningLaw_minorization, sourceTV_eq_countableTV, sourceY_eq, conditionalColorMeasure_toPMF, generic transport/finite endpoint and normalization. First3oldfullimported-universeaudits died-6 under-M3500; no unchanged rerun/cap raise. Use actual production+REACHABLE-body graph; split sequential root-batches if necessary, consistentmetadata union must be proved complete. Auditors/tools/controls classify separately, no inflated declaration count or claim every imported theorem independently mathematically re-proved.

Review and rerun meaningful positive/nonvacuity/source controls and isolated semantic-mutation negative controls with true expected outcomes, no wrong-import false failures. Author current positive coding strict/checker0 and noninjective mutation1. Also test original chronology/normalization/TV hypotheses via proof controls as appropriate; sourceuniversalendpoint all edge cases should be paid, not blocked by a vacuous model. No mathematical Python/numeric experiments/enumeration/CAS/solver. Documentation/hash/PDF processing scripts allowed.

PRIOR/SIGNIFICANCE: read actual cached ordinary primary paper/proof and94 accepted scopes, no oldcertificateaudit. Independentordinaryreview found1311.4243v5 multicolor collision-time asymptotics uses randomized side/time and does not give marked-color law bound under strict alternation. Check this full bridge/nonmatch independently from copied actual body. Galbraith-Holmes2012 A non-uniform birthday problem with applications to discrete logarithms DAM1601547-1560 remains404unread across all deliveries, no new fetch allowed. It is a disclosed bounded-access limit, not a generic worldwide-unknown veto or automatic clearance. If an actual specific applicable unread theorem is identified state precise HOLD. For routine exclusion supply complete earlier theorem-to-target bridge and strongest contrary case; standard coupling/shortness/weakconstant alone insufficient. Current registry evidence/chronology limitations retained; no worldwidenovelty or currentproof-bodymatching claim from roothead/nohit. Root alone prospective significant-family adjudication; one result max, no parameter/relabel variant credits.

Read-only manuscript review: use installed PDFSKILL via runner, announce, no authoring marker needed. Independently render inputs/author/output/pdf/shoe-discrepancy-completion.pdf, actually view EVERY one of5pages and inspect proof/source/formula/allcounts/reporting/prior/process statements. Report precise errata/page+minimal suggested text, no edit author/PDF, no new manuscript required. Stage-index historical no endpoint/PDF claim as earliersegment; currentfive-pagepaperexists. Avoid copyingauthorvisualQAasowninspection. Document native image/memory telemetrylimits.

PROCESS separately: all inherited direct uncapped/runpy/overlap/render/audit/threadsession failures preserved in copied currentCHECKPOINT/rootpreviousintegration. Currentr4 standalone display helper is prospective exact self-capexception; does not retroactively clear prioruncappedreads. Bulkreceiptmetadata machine-read doesnotmean every entry personallydisplayed. Final-source TV personal displaylate remains currentdeviation, while actual independentlyreadfinalsource+freshproofcheck may establish technical correctness. Per-group sampling not globalcgroup. No universalproceduralPASS or authorselftechnicalPASS. Disclose anynewownbreachandstopaffectedactivity, no historicalreceiptbackfill/ledgeredits/automaticwaivers. Root process adjudication distinct from independent mathematical/source/formal gates.

DELIVER FINAL-REVIEW.md, keyed review.json (324571) with separate literal/original/finalsource, ordinary probability proof, semantictransport, proofbody, freshstrict+kernel/source-onlyreplay, deepbodyaudit, controls, manuscript, prior/novelty/significance/family, historical/currentprocess, overallrecommendation gates. Include full source-to-definition map, objections+strongestcontrarycases, exactfreshbuild/checker/audit/controls receipts/hashes, complete dependency DAG/closure evidence, actualsource/visual/read/resourceinventories and all5pageQA. TechnicalPASSisnotacceptance. Recommendaccept/revise/exclude withprecisereasons; report exactminimal fixes withoutproductionedits. Continue fullauthorizedindependentreviewpersonally. Nochildren/nofallback. Current55/60beyond39 remainsunchanged, credit0 and rootacceptanceunpaid. Finalstandaloneverify_frozen after, no laterfrozenwrites, actualmanifest everycopiedinput/helper/pin/plan/source/replayolean/log/completedreceipt/audit/render/report with EXACTterminalnoncircularselfexclusions. Alljobsreaped; actualdiskhandbackonly.
'''
(L/'TASK.txt').write_text(prefix+detail)
bind={str(R/n):v for n,v in files.items()};bind.update(frozen)
bind[str(R/'SHA256-MANIFEST.json')]=sha(R/'SHA256-MANIFEST.json')
for n in m['exact_terminal_noncircular_self_exclusions']:bind[str(R/n)]=sha(R/n)
for rel in origins:
 if not rel.startswith('src/'):bind[str(L/rel)]=sha(L/rel)
for n in ['env.sh','display_log.py','SOURCE-ORDER.json','INPUT-ORIGINS.json','ROOT-PREP.json','TASK.txt']:bind[str(L/n)]=sha(L/n)
save(L/'frozen-inputs.json',bind)
assert all(sha(Path(n))==v for n,v in bind.items())
save(ROOT/'shoe-review-r5-ready.json',dict(utc=now,lane=str(L),target=324571,model='gpt-6.1-sol',reasoning='high',service='default',modules=len(order),frozen=len(bind),task_sha256=sha(L/'TASK.txt'),credit=0))
print(json.dumps(dict(parent=str(parent),author_manifest=len(files),author_frozen=len(frozen),receipts=len(receipts),exits=dict(collections.Counter(str(q['exit']) for q in receipts)),review_lane=str(L),modules=len(order),review_frozen=len(bind))))
