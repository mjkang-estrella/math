#!/usr/bin/env python3
"""Prepare distinct Source323 discovery after full Structural198 closure."""
from pathlib import Path
import datetime, hashlib, json, re
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; ET=C/'expanded-target-2026-10-17'
sha=lambda b:hashlib.sha256(b).hexdigest(); read=lambda p:json.loads(p.read_text())
owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'intake.json')['disposition']=='PASS_TECHNICAL_CLOSED_ZERO_COUNT'
assert read(P/'contribution-r1-adoption/adoption.json')['condition']=='DISCHARGED'
oldraw=(ET/'fresh-structural-r198-brief.txt').read_bytes(); assert sha(oldraw)=='07b114869686b2e7b4332a798d497c7f2ab1b2073587d6c24ea7abbea1f37f0c'
old=oldraw.decode().splitlines(); header=old[:38]
brief=ET/'fresh-structural-r199-brief.txt'; output=C/'fresh-structural-discovery-r199'
assert not brief.exists() and not output.exists()
registry_raw=(C/'tasks.json').read_bytes(); registry=json.loads(registry_raw); checks=[]
for i,e in enumerate(registry['tasks']):
 if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']:
  assert e['parent_thread']!=owner,'Owned task still pending'
  b=(PROJECT/e['brief']).read_bytes(); assert b.count(b'*structural*r199*')>=1
  checks.append({'task_index':i,'brief':e['brief'],'sha256':sha(b),'bytes':len(b),'literal_guard_count':b.count(b'*structural*r199*'),'status_source':'Shared registry metadata only; no task-status request or mathematical body inspection.'})
assert checks
header[0]='Structural discovery r199 — Source323: relative independence of the separable quotient problem; distinct operative-proof discovery.'
header[1]='Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r199/.'
pos=header[9].index('The ORIGINAL INITIAL brief of Arithmetic162o')
header[9]=header[9][:pos]+('The ORIGINAL INITIAL brief of Arithmetic162r (idx686, foreign owner, recorded running in shared coordination state) contains literal *structural*r199* before this root or brief exists. Exclude the ENTIRE *arithmetic*r162* namespace, *owner-recovery*, and every peer body/parent/brief/copy/derivative/status/activity alias. Do not inspect, poll or steer any peer. Structural198 is CLOSED at its entire unchanged sphere-phase-isometry classification AND stronger all-normed-space sign-lift scope, correctness PASS / contribution TECHNICAL, condition DISCHARGED, ZERO count. Structural197,196,195 are also closed PASS/TECHNICAL, zero count. Exclude their entire author, review and parent namespaces, including no-r aliases; no body exception is admitted. Do not rename, weaken or seek another grade on those targets. Every previously listed live or completed namespace remains excluded. Install the no-r twin of EVERY wildcard and compare all literal guards and twins BEFORE traversal, including *k369r134-* and *t185r144-*. Own structural199 namespace is excluded from broad authored-history scans; own files are usable. Exact admitted original-source/history paths do not admit containing directories. No peer result or status may be used as a premise. These are prospective prompt-level guards, not operating-system isolation.')
start=548447
with (PROJECT/'sources/CONTENTS.md').open('rb') as f:f.seek(start); nav=f.read(4000)
end=start+nav.index(b'**324.'); body=nav[:end-start]
assert body.startswith(b'**323.') and b'lean/docs/323.md' in body
folder='preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/'
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated']; entries=[e for e in tree['tree'] if e['path'].startswith(folder)]; blobs=[e for e in entries if e['type']=='blob']
assert len(entries)==16 and len(blobs)==14
wrapper=next(e for e in blobs if e['path']==folder+'build/main.tex'); assert wrapper['size']==2076 and wrapper['sha']=='40418f8c28a4aa9df16ee8bb65a8b281dd88bf15'
target=[
'',
f'Catalogue access for THIS round, if needed: ONLY direct binary seek/read sources/CONTENTS.md[{start},{end}), exact Source323 body, SHA256 '+sha(body)+'. No whole-catalogue read/decode, new heading search, second family or catalogue traversal. Parent bounded navigation read4000bytes from548447 to locate the324 heading; it incidentally displayed324/325 as navigation only. Only323 is selected. Parent has read no mathematical source theorem/proof body for this round.',
'',
'Your ONE developed family is Source323, Relative independence of the separable quotient problem. The complete pinned tree has ONE canonical folder '+folder+' with16 entries/14 blobs: README.md, build/main.tex (2076bytes, Git blob 40418f8c28a4aa9df16ee8bb65a8b281dd88bf15), build/references.bib, TEN build/sections/*.tex bodies, and paper.pdf. Authenticate every canonical blob and establish the operative include order and dependencies from the actual wrapper. The sections are branches, evaluation, exact-pairs, introduction, models, norming, paths, positive, predual and scalar-fields; filenames are navigation, not statements or proof reading. Read actual statements, all operative proofs and required companions before extended deductions or drafting.',
'',
'The catalogue has a Lean link: fetch/read the exact pinned lean/docs/323.md as navigation, authenticate any indicated comparator and determine its actual coverage. Parent has not read this documentation or any formal body for this round. A comparator pointer, declaration or placeholder is not formal proof coverage. Determine genuine companions from actual canonical documents without drifting to another family. No downstream formalization is authorized.',
'',
'The source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Catalogue navigation describes relative consistency/independence for the existence of infinite-dimensional separable quotients of infinite-dimensional real and complex Banach spaces, using a measurable-cardinal consistency assumption for the global assertion and only ZFC consistency for density aleph1. These summaries are NOT substitutes for actual model-theoretic quantifiers. Read the source for its exact positive/negative hypotheses, density restrictions, field transfers and all operative construction interfaces. Every operation already proved there is PAID wherever it applies. Do not audit upstream truth or challenge stipulated results using external conjectural expectations.',
'',
'Develop a DISTINCT substantial full-scope consequence or extension after the strongest compatible source/classical/primary/original-history reduction. First identify what the full source proof already makes routine. Reformulating quotient existence as an operator/kernel/dual statement, realification/complexification, equivalent renorming, cardinal relabeling, or transporting a source model does not automatically supply substantial contribution. Conversely carry the strongest integrated construction and its compatibility steps concretely before declaring a residual unpaid. Keep ambient model, field, dimension, norm density, separability, closure, forcing/consistency assumptions and uniformity quantifiers explicit. Distinguish internal existence from external coding, and relative consistency from a theorem of ZFC. A stronger construction or genuine hypothesis removal is eligible only with a proved residual after actual source operations; do not freeze from the catalogue.',
'',
'Original-history navigation must use ACTUAL construction and primitive aliases learned from the source, in addition to separable quotient, Banach quotient, quotient problem, norm density, nonseparable, weak-star, exact pair, norming, predual, branch, path and forcing only where operative. Avoid bare ubiquitous words when a precise compound identifies the construction. Read strongest actual primary proofs, not abstracts or agent summaries. Install every guard before traversing eligible authored originals; follow operative sections to the next equal/higher heading, record exact read extents and limitations. Inaccessibility or a coarse exclusion is not novelty evidence. Preserve every old target encountered. Exclude peer/derivative bodies even if their names resemble the selected mechanism. Also install plain full-path substring activity before navigation.',
'',
'No completed-round mathematical body is directly admitted. Structural198/197/196/195 remain closed full-scope PASS/TECHNICAL zero-count, with no retry or renamed weaker substitute. All previous structural/arithmetic/analytic archives retain exact original scopes. On eligible historical overlap read the original scope before claiming distinctness; an excluded root is not licensed by overlap. Disclose resulting limits without inferring acceptance, exhaustion or a favorable grade.',
'',
'Carry sustained mathematical work with durable derivations. Complete operative reading and strongest-composition comparison before freezing a viable exact theorem, then prove the ENTIRE frozen scope. If it does not close, preserve that statement and identify the exact unresolved obligation; if no viable theorem emerges, report PREFREEZE/no nominee with actual derivations and gaps. Do not self-assign correctness/contribution/acceptance/count. Seal YOUR OWN exact selected packet ONCE, with detached FINAL/MANIFEST/outside REPORT hashes, a read-only explicit-anchor verifier binding exact selection and modes, and proportionate tiny copied controls. Protected bodies and named metadata remain private/local. No nested agents, git/shared writes, public actions, browser UI, or downstream formal/manuscript/release work.',
'',
]
standing=next(i for i,s in enumerate(old) if s.startswith('--- COMPLETE ORIGINAL STANDING BRIEF'))
text='\n'.join(header+target+old[standing:])+'\n'
patterns=lambda s:set(re.findall(r'\*[^\s,;]+\*',s))
# The source filename glob is a new navigation expression, not a relaxed guard.
assert patterns(oldraw.decode())<=patterns(text)
assert header[8]==old[8] and header[12]==old[12] and header[21:38]==old[21:38]
assert (C/'tasks.json').read_bytes()==registry_raw
brief.write_text(text)
meta={'observed_utc':now,'path':str(brief.relative_to(C)),'sha256':sha(brief.read_bytes()),'bytes':brief.stat().st_size,'output':'fresh-structural-discovery-r199','catalogue_extent':[start,end],'catalogue_sha256':sha(body),'canonical_folder':folder,'canonical_blobs':14,'tree_entries':16,'wrapper':{k:wrapper[k] for k in ['path','sha','size']},'lean_navigation':'Exact lean/docs/323.md indicated by catalogue; not read by parent. Child must inspect actual documentation and coverage.','source_body_read_by_parent':False,'provenance':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'xhigh','serviceTier':'default'}}}
(P/'next-discovery-preparation.json').write_text(json.dumps(meta,indent=2)+'\n')
isolation={'observed_utc':now,'brief':meta,'foreign_original_guard_checks':checks,'brief_finalized_and_peer_guard_checked_before_root':True,'all_prior_literal_guards_preserved':True,'mutual_guard':'New brief excludes entire arithmetic162 and owner-recovery namespace; current original peer brief already excludes structural199. All literal/no-r/substring guards retained.','limits':'Prompt-level chronology, not OS/perfect isolation. No foreign result/body/liveness inspection or steering.'}
(P/'prospective-isolation-structural199.json').write_text(json.dumps(isolation,indent=2)+'\n')
print(json.dumps(meta,indent=2)); print('Foreign initial guard checks:',len(checks))
