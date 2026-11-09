"""Prepare clean disjoint discovery and a bounded independent source review."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,shutil,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';AUTHOR=P/'expanded-corpus-r465'
R=P/'percolation-hub-source-review-sol-r1';assert not R.exists()
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
for n in [463,465,466]:
 x=json.loads((P/f'expanded-corpus-r{n}-parent-integration.json').read_text());assert x['verified_original_bindings'] and x['credit']==0
 assert bool(x['quarantine'])==(n in [463,466])
den=json.loads((ROOT/'inherited-denials-r466.json').read_text());den['utc']=now
den['root_r463_r466_quarantine']='r463and r466 FAIL_QUARANTINE after actual prohibited history reads, including Hat formal flat parent integrations. r463two exact Hat files; r466ownreport98 flagged protected paths including Hat/code-loop/Polynexus/crown/bunkbed. ALLoutputs/acquisitions/claims quarantined,no candidates/reuse,clean frozen hashes doNOTcure. ROOTintake only own evidence/corpus, no protected externalpathfollow. Future constructor filters EVERYrelative pathpart including flatbasename BEFOREstat/open/hash; histories exclude463/466andparentrecords. Oldallowlisting neveroverridesboundary. This is not a new network denial on every original work.'
den['root_r465_scope']='Cleanreported465ownhistory784checkednamesnoHatentries,39wrapperpasses.330008finitehubrho1/sitebond uniquecluster authorproposalPARK at informalfiniteasymptotic/laterlocallyfiniteinfinite scope and specific1610.04897comparison; independentreviewassigned,noformal/credit.333772sourceownBergeTheorem3full0;360708actualKousek2026Props5.1/6.5publicboth-density-refutations0.334190recursive2increasingclassification and353432equaldegreefree/nonfreeincidencepair gaps,369863strictnesscorrection0.197ownfiles20originalbindings13frozenverified. No newdenials.'
denpath=ROOT/'inherited-denials-r467.json';save(denpath,den)
R.mkdir();(R/'inputs').mkdir()
base=P/'expanded-corpus-r433'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:
 shutil.copyfile(base/name,R/name)
shutil.copyfile(ROOT/'charge_search.py',R/'charge_search.py');shutil.copyfile(denpath,R/'inherited-denials.json')
raw=(AUTHOR/'provenance/330008.raw.jsonl').read_bytes();original=json.loads(raw);assert original['mathdb_id']==330008
(R/'inputs/original330008.jsonl').write_bytes(raw);save(R/'inputs/literal330008.json',original)
gates=json.loads((AUTHOR/'results.json').read_text());save(R/'inputs/author-gates330008.json',gates['330008'])
text=(AUTHOR/'DERIVATIONS.md').read_text();start=text.index('## 330008:');end=text.index('\n## 334190:',start)
(R/'inputs/author-proof330008.md').write_text(text[start:end]+'\n')
for name in ['percolation.pdf','percolation.txt','percolation-followup.pdf','percolation-followup.txt']:
 shutil.copyfile(AUTHOR/'sources'/name,R/'inputs'/name)
for name in ['get-percolation.json','get-percolation-followup.json','read-figure-inventory.json']:
 shutil.copyfile(AUTHOR/name,R/'inputs'/name)
shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json'
assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3'
shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
save(R/'reservation.json',dict(ids=[330008],rows=[original],purpose='Independent ordinary/source/prior/significance review only; no formal execution or credit'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n')
save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
task=f'''GPT-6.1 Sol high effort/default speed ONLY. Independent review of MathDB330008, finite-hub percolation nonuniqueness proposal. Work personally; no children/provider fallback/formal tools/self-credit. Root count57/60 beyond39 prior,96total.

FIRST shell command exactly:
timeout 20 python3 -I -B {R}/bootstrap.py
Read COMPLETE TASK/AGENTS. SECOND exactly:
timeout 140 python3 -I -B {R}/verify_frozen.py before
These are complete commands, no trailing punctuation. Bootstrap and standalone before/after verifiers are explicit cap exceptions. Every other substantive local operation must use immutable ABSOLUTE {R}/run.py with a fresh label and Python stdin, and own writes through immutable ABSOLUTE {R}/write_lane.py. Child cwd is ownlane. Never rerun bootstrap or edit frozen helpers/inputs/TASK/caps. Preserve genuine failures; change failed invocations before retrying. Ordinary local typo/serialization errors are documented, not automatically external access-policy breaches. Actual access/protected-file/guard/counter/cap violations retain stop/quarantine rules.

Assignment: independently prove or break the finite-family argument, authenticate literal/source quantifiers and site-versus-bond models, compare the actual applicable prior proof, and adjudicate significance with strongest contrary cases. Do not merely repeat the author. No mathematical programs, enumeration, numerics, experiments, CAS, solvers, Lean/compiler/checker/formalAPI. Documentary/provenance/PDF processing only under caps. Do not manufacture a formal proposition when the literal's asymptotic quantifiers are informal.

All authorized historical inputs are the explicit FROZEN OWN inputs/ files. NO historical campaign file or parent integration may be read/stat/hashed/listed, and no embedded input path may be followed. Protected active/planned peers expanded-corpus-r467 and expanded-corpus-r468 entirely forbidden evenmetadata. All old formal/code-loop/Polynexus/crown/tournament/bunkbed/Hat bodies and flat integration basenames forbidden. r463 and r466 ALLoutputs/acquisitions quarantined; never use them. An old allowlist is NOT permission. This review has no historical allowlist on purpose. Do NOT inspect the author lane or ROOT files; use own frozen copies. ROOT supplied trusted57+39 full scopes for family comparison, not old certificate audits.

Read exact original JSONL/literal and the complete two-page percolation.pdf actual1503.00410v1. Personally read relevant definitions and full proofs around Theorems20/24/Corollary25 in percolation-followup.pdf actual1505.03963v5, including standing locally-finite/infinite hypotheses and reference66. Inspect actual material figure/equation pages when needed; do not claim visual inspection from extracted text. If using PDF, announce/read /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. No PDF authoring requested.

Author proposal, NOT accepted: bidirected star or triangle with m pendant leaves, exact nonbacktracking radius0 or1; fixedp1/2 gives a unique macroscopic component with positive conditional site probability, or whp in the stated bond readings, despite p*rho<1. Independently check spectral block argument, strong connectivity, directed/undirected cluster conventions, occupation models, all probability bounds, positive-fraction definition, conditional whp, graph-sequence class, unbounded hub degree, and whether standing OLG irreducibility or local-finiteness applies to Conjecture2 itself. Separate ordinary finite-family correctness from literal ambiguity and intended-source scientific content. Do not claim an infinite locally finite counterexample or introduce an unprinted degree bound as fact.

Specific unpaid primary comparison: arXiv1610.04897, Exponential decay of connectivity and uniqueness in percolation on finite and infinite graphs. This work is identified but unread and NOT denied. Acquire its actual applicable statement/proof if possible within rules, and show a complete applicable source-to-target bridge, a bounded nonmatch, or an exact residual HOLD. Check actual final/publication/correction status only within budget and work-wide denials. Distinguish already public omitted-hypothesis/limit correction from a substantive new finite-graph result. Smallness/shortness/standard tools alone are not routine exclusion grounds; a routine exclusion needs a COMPLETE actual-primary-to-target reduction and the strongest contrary significance argument. No worldwide novelty inference from no-hits. A concrete matching unread proof is a precise HOLD; generic worldwide unknown alone is not a veto.

Read ENTIRE inherited-denials.json before networking; recover material truncations. All work-wide unavailability rules remain. Sole GET client immutable source_get_guard.py under run.py, ONE manually selected persisted exact plan per invocation, fields url/routes/destination/source_identity/purpose; routes ['330008']; unique new sources/ destination; identity/purpose>=12characters. Review maximum8 GET HOPS total, redirects charged, and at most2 native searchcalls/6exactquerystrings WHOLEreview. No custom HTTP/requests/curl/wget/HEAD/nativeopen-fetch/browser/account/API/POST/TLS/cookie/JS/meta-refresh workaround. Every failure makes identifiedwork unavailable across ALLnewhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveries. No retry/alternateidentitycorrection/indirectrecovery. Four blocked registry-root metadata artifacts cannot be refreshed/reconstructed; dated heads are navigation only. Distinct primary publications may be studied; do not overextend a work-specific failure to every topic paper.

Before each native search persist an exact queries-list plan via writer, then charge via immutable absolute charge_search.py under run.py. LIVE counter/charge continuity required; never manually edit/reset/refund search-budget.json or search-charges.jsonl. Save FULLactual response immediately before otherwork. Plain JSON/string serialization; btoa/TextEncoder unavailable. Preserve errors and save the same in-memory response without another networkcall. Search snippets are navigation, not primary proof. On actual policy/budget/access violation STOPnetwork/mathematics and quarantine, preserve original evidence and report exact cause; do not repair/erase history. A failed ordinary GET is unavailable, not automatically a policy breach.

Resource caps fixed: affinity<=2, childCPU115/supervisor120, AS6GiB, sampled groupRSS6GiB, deadline130/outer140, arena2. Standalone verifierCPU120 explicit exception. True receipts/outputs and synchronous reaping; no backgroundjobs. AllwritesOWNlane only, no/tmp/parent/shared/dependency changes/git/install/publish/accounts/messages. Native telemetry/writer peaks/transients unavailable; do not assert universal process compliance.

Deliver actual REVIEW.md, keyedreview.json for330008 with separate literal/source/ordinary/prior/novelty/significance/family/formal/independent/procedure/acceptance gates, full independent proof or exact GAP.md, complete strongest prior/adaptation bridge or bounded nonmatch, objections and contrary cases, source map and exact proof/read/figure/access/search/resource inventories. Record candidate math/source corrections without silently changing literal. Prospective PASS is not root acceptance; credit0. Only if full scope and scientific qualification survive, provide a conditional DORMANT-SOL-FORMAL-PLAN.md with exact objects/endpoint/bridges; no dispatch. No partial Lean or helpers.

Finish with standalone verify_frozen.py after, then actual byte manifest including completed receiptJSONs, frozeninputs, payloads/plans/full responses/guard ledger/reports/frozen-after. Name terminal noncircular exclusions precisely. No subsequent frozenwrites. Complete the bounded actual review, not just source acquisition or acknowledgment. Prior failures and limits remain explicit. Root decides acceptance.
'''
(R/'TASK.txt').write_text(task)
freeze=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir())
save(R/'frozen-inputs.json',{str(q):sha(q) for q in freeze})
review_ready=dict(utc=now,lane=str(R),mathdb_id=330008,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(freeze),model='gpt-6.1-sol',reasoning='high',service='default',credit=0,accepted_new=57,protected_peers=['expanded-corpus-r467','expanded-corpus-r468'],source_copy_scope='Explicit cleanr465 target-only inputs; no quarantined source or historical paths copied')
save(ROOT/'percolation-review-r1-ready.json',review_ready)
save(ROOT/'selection-routing-percolation-review-r1.json',dict(ids=[330008],sources=['https://arxiv.org/abs/1503.00410','https://arxiv.org/abs/1505.03963'],task_sha256=review_ready['task_sha256'],lane=str(R),metadata_only=True))
basecfg=json.loads((ROOT/'r466-config.json').read_text());excluded=set(basecfg['excluded_ids'])|{330008};excluded_sources=set(basecfg['excluded_sources'])|{'https://arxiv.org/abs/1503.00410','https://arxiv.org/abs/1505.03963'}
for n in [463,466]:
 routing=json.loads((ROOT/f'selection-routing-r{n}.json').read_text());excluded.update(routing['ids']);excluded_sources.update(routing['sources'])
steering=basecfg['steering']+'\nLATEST ROOT: r463 and r466 are FAIL_QUARANTINE for protected historical reads, including flat Hat formal parent integrations; r466 own report flags98paths including other protected formal families. All of their outputs/acquisitions/claims are INELIGIBLE: no read/reuse, no K2,3-house367685 candidate routing, no old source acquisition reuse/refetch seed. Their reservations remain occupied. Clean frozen hashes do NOT waive the breach. New constructor filters protected tokens in EVERY relative path part including flat basenames BEFOREstat/open/hash, and excludes both histories/parentrecords. You must retain this pre-access boundary even if an old entry is allowlisted. This is a file/evidence quarantine, not a new network denial on every original work. Cleanreported r465 had noHat entries in its saved784-file access inventory.330008finitehubrho1/sitebond proposal is PARKED at informalfiniteasymptotic scope versus actual infinite locallyfinite result and unread1610.04897; independent dedicated review now assigned, do not duplicate.333772sourceown fullBerge theorem0;360708actualKousek2026Props5.1/6.5 refute bothdensityclaims withcomplete bridges0;334190global2increasingclassification and353432equaldegreeincidencefreedom gaps,369863strictnesscorrection0. Root documentaryintakes verified184/197/111 ownfiles and each20original/13frozen; no scientific credit,57/60.\n'
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
ready=[]
for n,peers,routing_files in [(467,['expanded-corpus-r468',R.name],['selection-routing-percolation-review-r1.json']), (468,['expanded-corpus-r467',R.name],['selection-routing-percolation-review-r1.json','selection-routing-r467.json'])]:
 config=dict(number=n,protected_peers=peers,completed_discovery_numbers=list(range(421,463))+[464,465],quarantined_discovery_numbers=[395,463,466],denials=str(denpath),excluded_ids=sorted(excluded),excluded_sources=sorted(excluded_sources),peer_routing_files=routing_files,steering=steering)
 save(ROOT/f'r{n}-config.json',config);item=module.prepare(config);ready.append(item)
 allow=json.loads((Path(item['lane'])/'historical-results-allowlist.json').read_text())
 forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
 assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
 assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
assert not set(ready[0]['ids'])&set(ready[1]['ids'])
save(ROOT/'history-flat-boundary-fix-20261108.json',dict(utc=now,preparation_helper_sha256=sha(ROOT/'prepare_discovery_packet.py'),actual_failure='r463 andr466 protected flat history integrations opened despite allowlisting',fix='Filter every relativepathcomponent including flatbasename BEFOREstat/open/hash; filter root parent-integration collection similarly; exclude quarantined histories/parents',verified_new_history_allowlists=[dict(lane=x['lane'],sha256=sha(Path(x['lane'])/'historical-results-allowlist.json'),no_protected_component=True,no_quarantined_history=True) for x in ready],old_frozen_helpers_modified=False,old_quarantine_waived=False,root_external_protected_paths_followed=False))
print(json.dumps(dict(accepted_new=57,review=review_ready,discovery=ready,history_filter_checks='Both new actual allowlists contain no protected component or quarantined history; no old frozen packet edited')))
