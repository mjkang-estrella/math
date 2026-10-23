#!/usr/bin/env python3
"""Prepare distinct Source324 discovery after full Structural199 closure."""
from pathlib import Path
import datetime,hashlib,json,re
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];ET=C/'expanded-target-2026-10-17'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'intake.json')['disposition']=='PASS_TECHNICAL_CLOSED_ZERO_COUNT'
assert read(P/'contribution-r1-adoption/adoption.json')['condition']=='DISCHARGED'
oldraw=(ET/'fresh-structural-r199-brief.txt').read_bytes();assert sha(oldraw)=='0ac6eae36c204bdae0415b813e4915a0da0f2f95d54919f9874768641bc47652'
old=oldraw.decode().splitlines();header=old[:38]
brief=ET/'fresh-structural-r200-brief.txt';output=C/'fresh-structural-discovery-r200'
assert not brief.exists() and not output.exists()
registry_raw=(C/'tasks.json').read_bytes();registry=json.loads(registry_raw);checks=[]
for i,e in enumerate(registry['tasks']):
 if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']:
  assert e['parent_thread']!=owner,'Owned task still pending'
  b=(PROJECT/e['brief']).read_bytes();assert b.count(b'*structural*r200*')>=1
  checks.append({'task_index':i,'brief':e['brief'],'sha256':sha(b),'bytes':len(b),'literal_guard_count':b.count(b'*structural*r200*'),'status_source':'Shared registry metadata only; no task-status request or mathematical body inspection.'})
assert checks
header[0]='Structural discovery r200 — Source324: Lipschitz equivalence and c0 absorption; distinct operative-proof discovery.'
header[1]='Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r200/.'
pos=header[9].index('The ORIGINAL INITIAL brief of Arithmetic162r')
header[9]=header[9][:pos]+('The ORIGINAL INITIAL brief of Arithmetic162t (idx691, foreign owner, recorded running in shared coordination state) contains literal *structural*r200* before this root or brief exists. Exclude the ENTIRE *arithmetic*r162* namespace, *owner-recovery*, and every peer body/parent/brief/copy/derivative/status/activity alias. Do not inspect, poll or steer any peer. Structural199 is CLOSED at its entire unchanged Cohen-extension separable-quotient independence scope, including the stronger preselected paths/all-final-subspaces assertion, correctness PASS / contribution TECHNICAL, condition DISCHARGED, ZERO count. Structural198,197,196,195 are also closed PASS/TECHNICAL, zero count. Exclude their entire author, review and parent namespaces, including no-r aliases; no body exception is admitted. Do not rename, weaken or seek another grade on those targets. Every previously listed live or completed namespace remains excluded. Install the no-r twin of EVERY wildcard and compare all literal guards and twins BEFORE traversal, including *k369r134-* and *t185r144-*. Own structural200 namespace is excluded from broad authored-history scans; own files are usable. Exact admitted original-source/history paths do not admit containing directories. No peer result or status may be used as a premise. These are prospective prompt-level guards, not operating-system isolation.')
start=549528
with (PROJECT/'sources/CONTENTS.md').open('rb') as f:f.seek(start);nav=f.read(4000)
end=start+nav.index(b'**325.');body=nav[:end-start]
assert end==550877 and body.startswith(b'**324.') and b'lean/docs/324.md' in body
assert sha(body)=='e3562484e1e7d24d23d5412cee06304af733d6f7eb4f37d08ad67590835654a4'
folders=['preprints/Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026/','preprints/Bi-Lipschitz-Absorption-of-c0-Without-a-Linear-Copy-of-c0-September-26-2026/']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb);assert not tree['truncated'];canonical=[]
for folder,nentries,nblobs,size,git in zip(folders,[14,16],[11,13],[1849,1719],['5ace96a48854c12e2878f30282467c5094417f76','b9ab961a84e25bdbf1dc3d8c7710d2a0d1e773eb']):
 entries=[e for e in tree['tree'] if e['path'].startswith(folder)];blobs=[e for e in entries if e['type']=='blob'];assert len(entries)==nentries and len(blobs)==nblobs
 wrapper=next(e for e in blobs if e['path']==folder+'build/main.tex');assert wrapper['size']==size and wrapper['sha']==git
 canonical.append({'folder':folder,'entries':nentries,'blobs':nblobs,'wrapper':{k:wrapper[k] for k in ['path','sha','size']}})
with (PROJECT/'frontier/NEW-TEN-2026-10-14.md').open('rb') as f:f.seek(4801);acceptance=f.read(6347-4801)
assert sha(acceptance)=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
target=[
'',
'Also prospectively prune FULL-PATH substrings .diff, state_probe, consolidate and activity BEFORE the first traversal/body selection. These supplement EVERY inherited guard and close disclosed alias omissions from completed work. Do not rerun broader old scans. For applicable AGENTS.md read only the exact project-root path already admitted; no descendant or ancestor filename inventory is needed or authorized.',
'',
f'Catalogue access for THIS round, if needed: ONLY direct binary seek/read sources/CONTENTS.md[{start},{end}), exact Source324 body, SHA256 '+sha(body)+'. No whole-catalogue read/decode, new heading search, second family or catalogue traversal. Parent bounded navigation read4000bytes from549528 to locate the325 heading; earlier navigation incidentally displayed325/326 only. Only324 is selected. Parent has read no mathematical source theorem/proof body for this round.',
'',
'Your ONE developed family is Source324, Lipschitz equivalent Banach spaces need not be linearly isomorphic, INCLUDING its c0-absorption companion. The complete pinned tree has TWO canonical folders, BOTH mandatory: '+folders[0]+' (14 entries/11 blobs; build/main.tex 1849bytes Git blob 5ace96a48854c12e2878f30282467c5094417f76) AND '+folders[1]+' (16 entries/13 blobs; build/main.tex 1719bytes Git blob b9ab961a84e25bdbf1dc3d8c7710d2a0d1e773eb). Authenticate all24 canonical blobs. Each folder includes README.md, build/main.tex, build/references.bib, one build/figures/*.tex body, operative build/sections/*.tex bodies and paper.pdf. Establish actual include order and all operative dependencies from BOTH wrappers. The first has six sections (introduction, free-graph, triangular, localization, hilbert, assembly); the second has eight (introduction, absorption, weights, shift, tests, molecules, no-c0, assembly). Filenames are navigation, not proof reading. Read actual statements, all operative proofs and any required further companions before extended deductions or drafting. Reading one abstract or one companion alone is insufficient.',
'',
'The catalogue has a Lean link: fetch/read the exact pinned lean/docs/324.md as navigation, authenticate any indicated comparator and determine its actual coverage. Parent has not read this documentation or any formal body for this round. A comparator pointer, declaration or placeholder is not formal proof coverage. Determine genuine companions from actual canonical documents without drifting to another family. No downstream formalization is authorized.',
'',
'The source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Catalogue navigation describes separable real Banach spaces globally bi-Lipschitz equivalent but not linearly isomorphic, and a separable real Z with no linear copy of c0 yet bi-Lipschitz equivalent to Z direct-sum-infinity c0; that same Z bi-Lipschitz contains every separable metric space. These summaries are NOT substitutes for the exact actual constructions, constants, quantifiers or dependencies. Every operation already proved in either manuscript is PAID wherever it applies. Do not audit upstream truth or challenge stipulated results using external conjectural expectations.',
'',
'Develop a DISTINCT substantial full-scope consequence or extension after the strongest compatible source/classical/primary/original-history reduction. First identify what BOTH full source proofs already make routine. Iterating absorption, taking direct sums, equivalent renorming, transporting metric universality, or restating a nonlinear/linear distinction does not automatically supply substantial contribution. Conversely carry the strongest integrated construction and compatibility steps concretely before declaring a residual unpaid. Track real versus complex fields, global versus local/coarse maps, embeddings versus surjections, separability, norm completeness, exact distortion and uniformity. Distinguish a linear copy from a complemented copy or a quotient; do not infer a linear splitting or linear derivative from a Lipschitz bijection without all hypotheses. A genuine stronger construction or hypothesis removal is eligible only with a proved residual after actual source operations; do not freeze from the catalogue.',
'',
'Original-history navigation must use ACTUAL construction and primitive aliases learned from both sources, in addition to precise terms Lipschitz equivalence, Lipschitz isomorphism, bi-Lipschitz absorption, c0 absorption, Lipschitz-free, free graph, localization, terminal scalar, molecules and metric universality only where operative. Avoid bare ubiquitous words where a precise compound identifies the construction. Read strongest actual primary proofs, not abstracts or agent summaries. Install every guard before traversing eligible authored originals; follow operative sections to the next equal/higher heading, record exact read extents and limitations. Inaccessibility or coarse exclusions are not novelty evidence. Preserve every old target encountered. Exclude peer/derivative bodies even if their names resemble this mechanism. No projectwide filename inventory followed by filtering is authorized.',
'',
'No completed-round mathematical body is directly admitted. Structural199/198/197/196/195 remain closed full-scope PASS/TECHNICAL zero-count, with no retry or renamed weaker substitute. All previous structural/arithmetic/analytic archives retain exact original scopes. On eligible historical overlap read the actual original scope before claiming distinctness; an excluded root is not licensed by overlap. Disclose resulting limits without inferring acceptance, exhaustion or a favorable grade. The parent has not established history clearance for Source324.',
'',
'Carry sustained mathematical work with durable derivations. Complete operative reading and strongest-composition comparison before freezing a viable exact theorem, then prove the ENTIRE frozen scope. If it does not close, preserve that statement and identify the exact unresolved obligation; if no viable theorem emerges, report PREFREEZE/no nominee with actual derivations and gaps. Do not self-assign correctness/contribution/acceptance/count. Seal YOUR OWN exact selected packet ONCE, with detached FINAL/MANIFEST/outside REPORT hashes, a read-only explicit-anchor verifier binding exact selection and modes, and proportionate tiny copied controls. Protected bodies and named metadata remain private/local. No nested agents, git/shared writes, public actions, browser UI, or downstream formal/manuscript/release work.',
'',
]
standing=next(i for i,s in enumerate(old) if s.startswith('--- COMPLETE ORIGINAL STANDING BRIEF'))
text='\n'.join(header+target+old[standing:])+'\n'
patterns=lambda s:set(re.findall(r'\*[^\s,;]+\*',s))
assert patterns(oldraw.decode())<=patterns(text)
assert header[8]==old[8] and header[12]==old[12] and header[21:38]==old[21:38]
assert text[text.index('--- COMPLETE ORIGINAL STANDING BRIEF'):]==oldraw.decode()[oldraw.decode().index('--- COMPLETE ORIGINAL STANDING BRIEF'):]
assert all(s in text for s in ['.diff','state_probe','consolidate','activity','*structural*r200*','*arithmetic*r162*'])
assert (C/'tasks.json').read_bytes()==registry_raw
brief.write_text(text)
meta={'observed_utc':now,'path':str(brief.relative_to(C)),'sha256':sha(brief.read_bytes()),'bytes':brief.stat().st_size,'output':'fresh-structural-discovery-r200','catalogue_extent':[start,end],'catalogue_sha256':sha(body),'canonical_manuscripts':canonical,'canonical_blobs':24,'tree_entries':30,'operative_section_bodies':14,'figure_bodies':2,'lean_navigation':'Exact lean/docs/324.md indicated by catalogue; not read by parent. Child must inspect actual documentation and coverage.','source_body_read_by_parent':False,'acceptance_extent':[4801,6347],'acceptance_sha256':sha(acceptance),'provenance':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'xhigh','serviceTier':'default'}}}
(P/'next-discovery-preparation.json').write_text(json.dumps(meta,indent=2)+'\n')
isolation={'observed_utc':now,'brief':meta,'foreign_original_guard_checks':checks,'brief_finalized_and_peer_guard_checked_before_root':True,'all_prior_literal_guards_preserved':True,'complete_original_standing_brief_preserved':True,'new_substring_guards':['.diff','state_probe','consolidate','activity'],'mutual_guard':'New brief excludes entire arithmetic162 and owner-recovery namespace; current original peer brief already excludes structural200. All literal/no-r/substring guards retained.','limits':'Prompt-level chronology, not OS/perfect isolation. No foreign result/body/liveness inspection or steering. Parent handoff filename-only inventory lapse disclosed in contribution adoption assessment; no body admission resulted. Exact-root AGENTS-only instruction prospectively retained.'}
(P/'prospective-isolation-structural200.json').write_text(json.dumps(isolation,indent=2)+'\n')
print(json.dumps(meta,indent=2));print('Foreign initial guard checks:',len(checks))
