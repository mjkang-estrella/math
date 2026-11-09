"""Prepare immutable delegate packets and disjoint metadata routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,shutil,datetime,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
    assert not p.exists(),str(p)
    p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'ledger.json')['accepted_new']==57
report=read(ROOT/'r503-r505-intake-report.json')
assert set(report['records'])=={'503','504','505'} and report['no_root_mathematical_work']
DEN=ROOT/'inherited-denials-r516.json'
NAMES=['subcritical-covariance-source-review-sol-r1','planar-laplacian-congruence-source-review-sol-r1']
assert not any((P/x).exists() for x in NAMES) and not (P/'expanded-corpus-r506').exists()

COMMON='''Use ONLY GPT-6.1 Sol, HIGH reasoning, DEFAULT speed. Personally perform the independent review; NO children, model/provider fallbacks, mathematical programs/enumeration/numerical experiments/CAS/solvers, Lean/compiler/checker/formal API, self-credit, git/install/publication/accounts/browser/external messages. Root orchestrates; you do mathematics and source qualification. Complete a bounded proof AND source/significance investigation, not acquisition-only. Campaign57/60 NEW beyond39prior,96total unchanged. No formal dispatch authorized.

FIRST shell command EXACTLY (one standalone command, no punctuation/chaining):
timeout 20 python3 -I -B {lane}/bootstrap.py
Read COMPLETE printed AGENTS/TASK. SECOND shell command EXACTLY:
timeout 140 python3 -I -B {lane}/verify_frozen.py before
No reads/probes/planning/extra shell commands before those. Bootstrap and standalone frozen verifiers explicit cap exceptions. Every OTHER substantive local shell/document/source/PDF operation: immutable ABSOLUTE {lane}/run.py UNIQUE_LABEL Python stdin, outer timeout140. Authored writes immutable ABSOLUTE {lane}/write_lane.py. Do not edit frozen helpers/inputs/TASK/caps or rerun bootstrap. Preserve true failures; targeted diagnostic repairs permitted. Actual protected/frozen/access/guard/counter/cap breach STOP/quarantine, no reset; ordinary documentary typo/render/serialization failure is not automatically a policy breach.

SOLE target {id}. Protected ACTIVE peers {peers} ENTIRELY including metadata/stat/read/hash/list/glob/poll/reservations/flat integrations. Access ONLY OWN supplied inputs/products and explicit PDF skill. NO ROOT/campaign/author/sibling/history/embedded-path access, no historical allowlist; source-map filenames are provenance, not permission to follow them. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat bodies AND flat integrations protected. ENTIRE r395/r463/r466/r482 permanently quarantined, no reuse/refetch seeds. No parent/shared/tmp writes; own absolute lane only. Trusted supplied57+39 exact scopes are routing truth, not permission to inspect accepted certificates or audit upstream truth. Independent review is independent verification, not independent invention; this task already discloses the mechanism.

Read own exact raw/literal and personally reconstruct mathematical proof or precise GAP BEFORE opening author FULLCANDIDATE.md or author ordinary routes. Inspect actual source definitions and relevant theorem/proof bodies; then adversarially audit author proposal and dependencies. A declared open label, a source summary or paper abstract does not prove novelty. Complete proof must pay the exact literal scope, all parameters and every source-to-endpoint bridge; nearby helpers/corrections do not earn credit. Record literal, original source, final/correction, ordinary, prior, novelty, significance, family, formal, process and acceptance gates separately. Specific applicable unread proof remains a precise HOLD; generic worldwide unknown is not itself proof of duplication or a blanket veto. Strongest positive AND negative substantive cases required. Public/routine exclusion requires actual primary theorem/proof plus COMPLETE all-hypotheses/conclusion reduction; standardness, shortness, familiar tools and snippet similarity alone do not establish it. Domain/wording corrections receive zero credit under campaign policy, distinguished from an authenticated earlier exact public result.

Compare ALL supplied accepted57+prior39 exact scopes personally, extracting actual scope fields; file loading/topic matches alone not a family comparison. No ROOT ledger mutation or acceptance. No formal tools even if source proof is complete; conditional dormant Sol formal brief only if exact ordinary/source/scientific gates prospectively survive.

Use and announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. Personally visually inspect material actual source glyphs (definitions, quantifiers, formulas and figures), not just extracted text/author images. PDF creation/conversion/processing under runner. Read-only NATIVE presentation of permitted OWN rendered pages explicitly authorized; no other native filesystem/network bypass. Native/transient/separate-writer/supervisor peaks remain unknown; do not claim universal cgroup/process-cap compliance. No PDF authoring needed for this review.

Before ANY request read COMPLETE own inherited-denials.json with material truncation recovery. Every identified failed work is unavailable for ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries; no retry, identity correction, HTTP-to-HTTPS upgrade or alternate recovery. Explicit predelivery cached copies only, not final-equivalence evidence. Distinct works are not blanket denied. Registry FOUR ROOT metadata artifacts remain closed; no README/tree/API/branch/version/mirror refresh or reconstruction. ErdosProblems642/809/881/1187 exact challenge-bearing pages closed; transport200/guard success histories remain immutable and no bypass or mathematical proof from challenge pages.

Independent review network budget: max6 guarded GET HOPS (redirects included), max2 native SEARCH calls/6 EXACT querystrings, own counters start0. Sole GET via immutable ABSOLUTE own source_get_guard.py UNDER own run.py, ONE manually chosen persisted exact plan per invocation, routes=[str({id})], actual observed primary URL, NEW own sources destination, source_identity and purpose>=12chars. No guessed URL or batching. Every plan must precede invocation; no modifying helper/caps or refreshing forbidden work under another identity. All subprocesses synchronous, true exits/reaping, no background.

Before EACH search persist exact queries-list plan through writer, READ LIVE counters/ledger, precharge immutable ABSOLUTE charge_search.py under own runner, then save FULL ACTUAL native response IMMEDIATELY before further work as ordinary JSON/string; no btoa/TextEncoder, truncated synopsis or search-result-only proof. A local serialization failure may recover SAME in-memory response, never refetch, reset/refund or replace live counters. SEARCH is navigation only. No APIs including /server/api/ bitstreams/custom transport, curl/wget/requests/HEAD/native URLopen/browser/accounts/POST/TLS/cookie/JS/meta-refresh workarounds. Guard rejection or required STOP retains true failure receipts and immutable ledger, NO unavailable-row backfill; stop network/mathematical work as required and document precise gaps. Normal source failure closes identified work; no bypass. Local documentary mistakes alone are not transport denials.

Caps: affinity<=2,childCPU115/supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Standalone verifierCPU120 exception NOT nested under child115. All completed receipts/logs/failed attempts retained. No claims about unknown native/transient/writer/supervisor peaks.

Deliver REVIEW.md, independent PROOF.md or GAP.md, source-map and keyed review.json for{id} with separate gates, adversarial objections, actual primary full bridges or precise bounded nonmatches, read/visual/access/search/resource inventories and receipt inventory. Distinguish supplied/fresh/unread/rendered/actually-viewed bodies. Conditional dormant formal plan ONLY if prospective gates survive. At completion run standalone verify_frozen.py after THEN seal exhaustive OWN byte manifest incl ALL completed receipt JSONs/helpers/inputs/plans/payloads/fullresponses/ledgers/products; precisely name terminal noncircular self-exclusions, no later frozen writes. Credit0,57/60 unchanged. Stop at handback.
'''

COV='''Decisive target317413: Janson-Luczak susceptibility covariance-polynomial identity in0806.0252. Literal has corpus token "chat P"; actual hats and normalization must come from source, not a silent repair. FIRST establish actual definitions and index ranges of S_k(t),p_k(x),AsN,hat P_k/hat P_{k,l},P_{k,l}; personally trace Sections3,5,6, Theorems3.4,5.9,5.10,Conjecture5.11,6.1 and joint covariance construction. Resolve fixed nt=c versus near-critical nt->1, source centering/scaling, mixed covariances versus diagonal examples and uniqueness/noncircularity. The cached actual p17 prints AsN(n p_k(x),hatP_k(x)) without an apparent n in variance; degree2k-3 conflicts with examples4k-3, hatP2=2x5 conflicts with Theorem5.9 n(2x5-2x4) in fixed-c regime. These are UNRESOLVED flags, not root conclusions. Do NOT ask root to choose normalization. Prove an unambiguous literal reading from source body or give precise GAP; never silently impose author correction, assume inconsistent formulas as premises, or claim typo-only falsification. Actual covariance-defined MathDB identity may still be unambiguous despite source typos; decide with evidence, not typography preference. If definitions cannot be bound, label full literal HOLD even if moment helper correct.

Author mechanism to audit AFTER independent reconstruction: G(n,p),p<=1/(2n),Z=S_k=sum_component |C|^k. Group independent edges in ROWS R_i=(i,j),j>i; replace one row by independent copy G^i. Union H_i=G union G^i differs only in edges incident i. Outside union component C_i all components agree; prove |Z-Z^i|<=|C_i|^k for all fixed k (actual source range; k1 if included), without missing both-sided sum factors. Adaptive BFS of C_i: root dominated Bin(n,2p), nonroot Bin(n,p), including unseen-edge conditioning, dependence and fictitious padding. Uniform exponential/component moments using a=11/10,theta=1/100 and exact elementary inequalities; n1,p0 boundary handled. Row Doob D_i=E[Z-Z^i|F_i], conditional resampling identity/Jensen, L4<=K. Fourth expansion/Hölder gives A_i<=A_prev+6A_prev^.5K²+4A_prev^.25K³+K⁴, induction A_i<=100K⁴i², uniform O(n²) centered fourth moments. Audit martingale cubic/mixed terms/constants, independence and all fixed parameters. Edge-by-edge grouping does not give the claimed strength, so do not replace row proof with a weaker bound.

Intended all-index bridge: choose any c in(0,1/2),t=c/n,p=1-exp(-t)<=1/(2n),x=(1-c)^-1 in(1,2). Actual source ES_k=n p_k(x)+O(1), joint Gaussian CLT construction and Theorem6.1 covariance asymptotics must be justified in THIS regime with the ACTUAL same centering/scaling. L4 implies uniform integrability of mixed products, clipped bounded continuous products pass expectations; recover covariance equality on real interval and polynomial identity for every k,l, not just diagonal/k2/k3 or one parameter. Audit meanshift, Cramer-Wold/joint law and covariance construction, finite/infinite source index ranges and absence of circular use of desired moment convergence. Do not substitute fixed-c helper for literal all-polynomial endpoint or use unpaid all-index binomial-convolution/Lyapunov route.

Original/final ENTIRE work is newly CLOSED after DOI10.1063/1.2982848->AIP403:0806.0252,JMP49(2008)125207,all versions/hosts/body/METADATA/query/correction/author/cache/mirror/API/indirect deliveries. No fresh original/arxiv/final metadata search or retrieval; own copied predelivery covariance.pdf/.txt/metadata only, no final equivalence. Distinct actual primary martingale/resampling/subcritical-component papers are NOT blanket denied. If source fidelity fails, document paid helper and precise source gap rather than spending whole budget on a different normalized theorem.

SIGNIFICANCE: strongest positive case is a full all-fixed-index moment condition explicitly highlighted as the open sufficient condition by source, through independent-row resampling; not a small parameter instance. Strong contrary case is a COMPLETE classical subcritical-component exponential-tail plus martingale-resampling theorem application, possibly routine. Need actual primary theorem/proof and complete bound-to-polynomial bridge before routine/public exclusion; do not infer from familiar tails or no search hits. No specifically matching earlier proof authenticated by author. Current prior investigation bounded, worldwide novelty unestablished. If formal route prospectively justified, exact source polynomials/CLT/moment-to-covariance/all-index identity must all be represented, not define both polynomials equal by construction or assume the endpoint.
'''

PLANAR='''Decisive target328851: Huang-Yau-Yueh1409.5853v3 Conjecture4.11. Connected PLANAR graphs admitting sphere embeddings whose duals are isomorphic AS MULTIGRAPHS have integrally equivalent combinatorial-Laplacian quadratic forms. Inspect Section2 graph/Laplacian conventions and Section4 exact conjecture plus surrounding proofs/terminology. Check primal simple/loopless versus multiple-edge conventions, dual loops/parallel edges, connected/finite/one-vertex/empty-edge assumptions, quadratic equivalence means actual integer unimodular congruence U^T L1 U=L2 with det±1, not rational/reduced/stable congruence or isospectrality. A simple dual dropping multiplicities is not the given endpoint. Source metadata v3current/no displayedjournal does NOT prove no final/correction. Source itself not inherited denied, no unneeded reacquisition of own supplied body; investigate actual current final/correction evidence only within budget.

Author mechanism to adversarially audit AFTER independent reconstruction: orient edges, incidenceB and L=BB^T, integral cut lattice im(B^T) with Euclidean dot product. Connectedness gives kernel of B^T=constant integer functions by paths; all incidence rows except root form a Zbasis with Gram reducedL. Compatible sphere orientations identify primal cut lattice with dual integral flow lattice ker B_dual using facial boundaries, INCLUDING loops/parallel edges/bridges. Directed integral circulation decomposes as signed cycles by subtracting cycle with positive multiplicity, decreasing l1; one-edge loops/two-edge parallel cycles are included. A sphere simple cycle bounds a disk; sum facial boundaries cancels interior edge SIDES with signs, leaving boundary cycle. Connected sphere embedding is cellular (tree-complement disk then edge additions), so facial integral span is entire integral flow kernel, not just real-vector dimension or finite-index sublattice. Check weak face boundaries/repeated sides/bridge cancellation, orientation consistency, cycle decomposition for negative flows and integrality. No assumption equivalent to desired duality inserted into a new definition.

Dual abstract multigraph isomorphism gives signed coordinate permutation preserving integer flow lattice and Euclidean form. Pull back isometry of primal integral cut lattices; Euler V-E+F=2 and same dual V/E imply equal primal vertex counts. Root-row Zbases give A in GL(n-1,Z), A^T L1red A=L2red. Full singular quadratic forms: x_root=t,x_v=y_v+t is integral unimodular coordinate change, full L congruent diag(Lred,0); insert diag(A,1) and restore coordinates for FULL n by n congruence. One-vertex zero form, trees with bridge-dual loops, parallel-dual edges, orientation signs, root choices and determinant/inverse integrality all paid explicitly. Higher-genus extension328852 is NOT claimed; nonfacial H1 obstructs this argument. Alternative Whitney-switch potential map is navigation only until a full actual Whitney decomposition theorem/proof and bridge are read.

SIGNIFICANCE central unpaid gate. Strong positive case: full all-graphs explicit integral-form conjecture with nontrivial integral generation/radical bridges, no finite endpoint/domain typo. Strong contrary case: a COMPLETE application of classical integral cut/flow lattice duality, graphic-lattice isometry or Whitney2-isomorphism may already subsume it. Find/read actual primary theorem AND proof, give full hypotheses/conclusion-to-literal reduction before exact-public/routine exclusion. Merely saying planar duality is standard or citing a lattice abstract is insufficient. Potential navigation only, NOT authenticated matching theorem: Bacher-de la Harpe-Nagnibeda, The lattice of integral flows and the lattice of integral cuts on a finite graph (1997). Authenticate actual bibliographic identity/observed URLs before requests. Full printed exact result vs your new reduction must be distinguished. If no complete earlier bridge established, bounded nonmatch is not worldwide novelty; specific applicable unread proof remains precise HOLD.

If scientific prospective gates survive, dormant formal blueprint must handle actual finite connected planar sphere embedding/dual multigraph and integer unimodular full Laplacian congruence. No assumed cut-flow equality, conclusion-bearing planar certificate, rational substitute or only reduced form. No Lean/formal execution now. Compare all96 trusted scopes, including graph/lattice/isometry neighbors, with exact endpoints rather than words.
'''

readies=[]
for number,mid,name,detail in [(503,317413,NAMES[0],COV),(504,328851,NAMES[1],PLANAR)]:
    A=P/f'expanded-corpus-r{number}';R=P/name;R.mkdir();(R/'inputs').mkdir()
    for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:
        shutil.copyfile(A/h,R/h)
    shutil.copyfile(DEN,R/'inherited-denials.json')
    if number==503:
        raw=A/f'originals/{mid}.jsonl';prov=next(x for x in read(A/'literal-bindings.json') if x['id']==mid)
        supplied=['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ORDINARY-ATTEMPTS.md','source-read-inventory.json','NEW-UNAVAILABLE.json','search-one-response.json','search-two-response.json','search-three-response.json']
        sourcefiles=['covariance.pdf','covariance.txt','covariance-metadata.html']
        plans=['plans/covariance.json','plans/cov-metadata.json','plans/cov-final.json']
    else:
        raw=A/f'literals/{mid}.jsonl';prov=read(A/'originals.json')[str(mid)]
        supplied=['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ORDINARY-ROUTES.md','search01-response.json','search02-response.json','search03-response.json']
        sourcefiles=['planar-original.pdf','planar-original.txt','planar-metadata.html']
        plans=['plan-get01.json','plan-get06.json']
    literal=json.loads(raw.read_text());shutil.copyfile(raw,R/'inputs'/f'original{mid}.raw.jsonl')
    save(R/'inputs'/f'literal{mid}.json',literal);save(R/'inputs'/f'provenance{mid}.json',prov)
    save(R/'inputs'/f'author-gates{mid}.json',read(A/'results.json')[str(mid)])
    for x in supplied:shutil.copyfile(A/x,R/'inputs'/x)
    for x in sourcefiles:shutil.copyfile(A/'sources'/x,R/'inputs'/x)
    for x in plans:shutil.copyfile(A/x,R/'inputs'/Path(x).name)
    # Target-only payload-origin evidence, no permission to follow external evidence paths.
    events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()]
    save(R/'inputs/source-origin-evidence.json',dict(author_lane=str(A),author_manifest_sha256=sha(A/'SHA256-MANIFEST.json'),events=[e for e in events if (e.get('routes')==[str(mid)] or e.get('destination','').split('/')[-1] in sourcefiles or str(mid)== '317413' and ('0806.0252' in e.get('url','') or '10.1063/1.2982848' in e.get('url','') or 'pubs.aip.org/jmp/article/49/12/125207' in e.get('url','')))],do_not_follow_external_paths=True))
    shutil.copyfile(ROOT/'accepted57-review-context.json',R/'inputs/accepted57-scopes.json')
    prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json'
    assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3'
    shutil.copyfile(prior,R/'inputs/prior39-scopes.json')
    save(R/'reservation.json',dict(ids=[mid],rows=[literal],purpose='Independent full literal/source/ordinary/actual-primary/significance review; no formal tools'))
    (R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n')
    save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
    peers=[x for x in NAMES if x!=name]+['expanded-corpus-r506']
    task=COMMON.format(lane=R,id=mid,peers=', '.join(peers))+'\nTARGET-SPECIFIC REVIEW\n'+detail
    (R/'TASK.txt').write_text(task)
    frozen=[x for x in R.iterdir() if x.is_file() and x.name!='search-budget.json']+list((R/'inputs').iterdir())
    save(R/'frozen-inputs.json',{str(x):sha(x) for x in frozen})
    ready=dict(utc=now,lane=str(R),mathdb_id=mid,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(frozen),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers)
    slug='subcritical-covariance-review-r1' if number==503 else 'planar-laplacian-review-r1'
    save(ROOT/(slug+'-ready.json'),ready)
    save(ROOT/('selection-routing-'+slug+'.json'),dict(ids=[mid],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True))
    readies.append(ready)

base=read(ROOT/'r505-config.json')
base.update(number=506,protected_peers=NAMES,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{503,504,505}),peer_routing_files=['selection-routing-subcritical-covariance-review-r1.json','selection-routing-planar-laplacian-review-r1.json'],denials=str(DEN),quarantined_discovery_numbers=[395,463,466,482],year_floor=1900,candidate_pool=1000)
base['excluded_ids']=sorted(set(base['excluded_ids'])|{317413,328851})
base['excluded_sources']=sorted(set(base['excluded_sources'])|{'https://arxiv.org/abs/0806.0252','https://arxiv.org/abs/1409.5853','https://www.erdosproblems.com/642'})
for n in [503,504,505]:base['steering']+='\n'+read(P/f'expanded-corpus-r{n}-parent-integration.json')['scientific_summary']
base['steering']+='\nNEW entire-work closure Janson-Luczak Susceptibility in subcritical random graphs0806.0252/JMP49(2008)125207/DOI10.1063/1.2982848 afterAIP403; all NEW body/METADATA/query/versions/hosts/arxiv/authors/cache/mirror/DOI/API/indirect delivery forbidden. Explicit oldcachedcopy not final equivalence. Distinct subcritical papers not blanket denied. NEW entire exactErdosProblems642 page closed after manualchallenge rawbyte31197,transport200/guard success unchanged; allnewdeliveries forbidden,no bypass,retry or inferredprimary-proof/current status. Independent317413/328851reviews protected inentirety.\n'
save(ROOT/'r506-config.json',base)
constructor=Path(base['metadata_constructor'])
assert constructor==ROOT/'prepare_discovery_packet_soft_asymp.py' and sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b'
assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('constructor_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
discovery=module.prepare(base)
allow=read(Path(discovery['lane'])/'historical-results-allowlist.json')
for filename in allow:
    rel=Path(filename).relative_to(P)
    assert not any(word in part.lower() for part in rel.parts for word in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
    assert not any(part in NAMES or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r503-r505-next-routing.json',dict(utc=now,reviews=readies,discovery=discovery,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(reviews=readies,discovery=discovery,credit=0,accepted_new=57)))
