#!/usr/bin/env python3
"""Prepare distinct Source322 discovery after full Structural197 closure."""
from pathlib import Path
import datetime, hashlib, json, re
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; ET=C/'expanded-target-2026-10-17'
sha=lambda b:hashlib.sha256(b).hexdigest(); read=lambda p:json.loads(p.read_text())
owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'intake.json')['disposition']=='PASS_TECHNICAL_CLOSED_ZERO_COUNT'
assert read(P/'contribution-r1-adoption/adoption.json')['condition']=='DISCHARGED'
oldraw=(ET/'fresh-structural-r197-brief.txt').read_bytes(); assert sha(oldraw)=='b42b2a37d2006f2c5fde173487a955a243ae9b90fbecc11b68323ab687094e47'
old=oldraw.decode().splitlines(); header=old[:38]
brief=ET/'fresh-structural-r198-brief.txt'; output=C/'fresh-structural-discovery-r198'
assert not brief.exists() and not output.exists()
registry_raw=(C/'tasks.json').read_bytes(); registry=json.loads(registry_raw); checks=[]
for i,e in enumerate(registry['tasks']):
 if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']:
  assert e['parent_thread']!=owner,'Owned task still pending'
  b=(PROJECT/e['brief']).read_bytes(); assert b.count(b'*structural*r198*')>=1
  checks.append({'task_index':i,'brief':e['brief'],'sha256':sha(b),'bytes':len(b),'literal_guard_count':b.count(b'*structural*r198*'),'status_source':'Shared registry metadata only; no task-status request or mathematical body inspection.'})
assert checks
header[0]='Structural discovery r198 — Source322: Tingley sphere-isometry extension; distinct operative-proof discovery.'
header[1]='Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r198/.'
pos=header[9].index('The ORIGINAL INITIAL brief of Arithmetic162n')
header[9]=header[9][:pos]+('The ORIGINAL INITIAL brief of Arithmetic162o (idx678, foreign owner, recorded running in shared coordination state) contains literal *structural*r198* before this root or brief exists. Exclude the ENTIRE *arithmetic*r162* namespace, *owner-recovery*, and every peer body/parent/brief/copy/derivative/status/activity alias. Do not inspect, poll or steer any peer. Structural197 is CLOSED at its entire unchanged all-rank twisted-profile/every-cover D(2) scope, correctness PASS / contribution TECHNICAL, condition DISCHARGED, ZERO count. Structural196 and195 are also closed PASS/TECHNICAL, zero count. Exclude their entire author, review and parent namespaces, including no-r aliases; no body exception is admitted. Do not rename, weaken or seek another grade on those targets. Every previously listed live or completed namespace remains excluded. Install the no-r twin of EVERY wildcard and compare all literal guards and twins BEFORE traversal, including *k369r134-* and *t185r144-*. Own structural198 namespace is excluded from broad authored-history scans; own files are usable. Exact admitted original-source/history paths do not admit containing directories. No peer result or status may be used as a premise. These are prospective prompt-level guards, not operating-system isolation.')
start=547380
with (PROJECT/'sources/CONTENTS.md').open('rb') as f:f.seek(start); nav=f.read(4000)
end=start+nav.index(b'**323.')
body=nav[:end-start]; assert body.startswith(b'**322.') and b'lean/docs/322.md' in body
folder='preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/'
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated']; entries=[e for e in tree['tree'] if e['path'].startswith(folder)]; blobs=[e for e in entries if e['type']=='blob']
assert len(entries)==5 and len(blobs)==4
wrapper=next(e for e in blobs if e['path']==folder+'build/main.tex'); assert wrapper['size']==35253 and wrapper['sha']=='ab9bd82b388ec4e55a333d05c61c853b7941798b'
lean=read(P/'private-next-source322/lean-receipt.json'); assert lean['sha256']=='5b8a07a1aa25bbca2c2a9ddd101fe2c7d2af88dceb7a975981f046e43e8f781c'
target=[
'',
f'Catalogue access for THIS round, if needed: ONLY direct binary seek/read sources/CONTENTS.md[{start},{end}), exact Source322 body, SHA256 '+sha(body)+'. No whole-catalogue read/decode, new heading search, second family or catalogue traversal. Parent bounded navigation read4000bytes from547380 to locate the323 heading; it incidentally displayed323/324 and the start of325 as navigation only. Only322 is selected. Parent has read no mathematical source theorem/proof body for this round.',
'',
'Your ONE developed family is Source322, A positive solution to Tingley\'s problem. The complete pinned tree has ONE canonical folder '+folder+' with5 entries/4 blobs: README.md, build/main.tex (35253bytes, Git blob ab9bd82b388ec4e55a333d05c61c853b7941798b), build/references.tex (5302bytes), and paper.pdf. Authenticate every canonical blob and establish the actual operative input order and dependencies from the wrapper and bodies. Filenames are navigation, not content. Read actual statements, all operative proofs and required companions before extended deductions or drafting.',
'',
'The catalogue has a Lean link: fetch/read the exact pinned lean/docs/322.md,933bytes,SHA256 5b8a07a1aa25bbca2c2a9ddd101fe2c7d2af88dceb7a975981f046e43e8f781c, as navigation. It links only the above paper and lean/ComparatorChallenges/TingleySphereIsometry.lean. This is a scope/comparator pointer, not a claim of inspected Lean proof coverage. Parent read this documentation only; no formal theorem body or proof was read. Determine any genuine companion or formal interface from actual canonical documents without drifting to another family. No downstream formalization work is authorized.',
'',
'The source AND ALL operative upstream proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Per catalogue/scope navigation, every surjective sphere isometry of nonzero real Banach spaces extends uniquely to a surjective real-linear isometry, with no dimension/separability/reflexivity/convexity restrictions. The headline and its actual maximal-defect enlargement, extremal-chord alignment, support/convexity and Darbo fixed-point operations are PAID wherever their actual hypotheses apply. Read the proofs for exact interfaces. Do not audit upstream truth or challenge the stipulated theorem using external expectations. For complex spaces viewed as real, real linearity is not complex linearity; approximate or nonsurjective statements do not follow from the headline alone.',
'',
'Develop a DISTINCT substantial full-scope consequence or extension after the strongest compatible source/classical/primary/original-history reduction. First identify what the full source proof already makes routine. Standard radial extension, Mazur-Ulam transport, realification, equivariant reformulation, or parameter changes are not automatically substantial. Conversely carry the strongest integrated extension/stability/geometry reduction concretely before declaring a compatibility step unpaid. A quantitative conclusion or genuine removal of a hypothesis is eligible only with an identified proved residual, not just a renamed estimate or an unproved bridge. Keep exact surjectivity, metric, field, completeness, dimension and uniformity quantifiers visible. Do not freeze from the catalogue.',
'',
'Original-history navigation must use ACTUAL construction and primitive aliases learned from the source, in addition to Tingley, sphere isometry, radial extension, Banach geometry, Mazur-Ulam, maximal defect, common support, extremal chord and fixed point only where operative. Read strongest actual primary proofs, not abstracts or agent summaries. Install every guard before traversing eligible authored originals; follow operative sections to the next equal/higher heading, record exact read extents and limitations. Inaccessibility or a coarse exclusion is not evidence of novelty. Preserve every old target encountered. Exclude peer/derivative bodies even if their names resemble the selected mechanism. Also install plain full-path substring activity before navigation.',
'',
'No completed-round mathematical body is directly admitted. Structural197/196/195 remain closed full-scope PASS/TECHNICAL zero-count, with no retry or renamed weaker substitute. All previous structural/arithmetic/analytic archives retain exact original scopes. On eligible historical overlap read the original scope before claiming distinctness; an excluded root is not licensed by overlap. Disclose resulting limits without inferring acceptance, exhaustion or a favorable grade.',
'',
'Carry sustained mathematical work with durable derivations. Complete operative reading and strongest-composition comparison before freezing a viable exact theorem, then prove the ENTIRE frozen scope. If it does not close, preserve that statement and identify the exact unresolved obligation; if no viable theorem emerges, report PREFREEZE/no nominee with actual derivations and gaps. Do not self-assign correctness/contribution/acceptance/count. Seal YOUR OWN exact selected packet ONCE, with detached FINAL/MANIFEST/outside REPORT hashes, a read-only explicit-anchor verifier binding exact selection and modes, and proportionate tiny copied controls. Protected bodies and named metadata remain private/local. No nested agents, git/shared writes, public actions, browser UI, or downstream formal/manuscript/release work.',
'',
]
assert old[53].startswith('--- COMPLETE ORIGINAL STANDING BRIEF')
text='\n'.join(header+target+old[53:])+'\n'
patterns=lambda s:set(re.findall(r'\*[^\s,;]+\*',s))
assert patterns(oldraw.decode())==patterns(text)
assert header[8]==old[8] and header[12]==old[12] and header[21:38]==old[21:38]
assert (C/'tasks.json').read_bytes()==registry_raw
brief.write_text(text)
meta={'observed_utc':now,'path':str(brief.relative_to(C)),'sha256':sha(brief.read_bytes()),'bytes':brief.stat().st_size,'output':'fresh-structural-discovery-r198','catalogue_extent':[start,end],'catalogue_sha256':sha(body),'canonical_folder':folder,'canonical_blobs':4,'tree_entries':5,'wrapper':{k:wrapper[k] for k in ['path','sha','size']},'lean_navigation':lean,'source_body_read_by_parent':False,'provenance':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'xhigh','serviceTier':'default'}}}
(P/'next-discovery-preparation.json').write_text(json.dumps(meta,indent=2)+'\n')
isolation={'observed_utc':now,'brief':meta,'foreign_original_guard_checks':checks,'brief_finalized_and_peer_guard_checked_before_root':True,'all_prior_literal_guards_preserved':True,'mutual_guard':'New brief excludes entire arithmetic162 and owner-recovery namespace; current original peer brief already excludes structural198. All literal/no-r/substring guards retained.','limits':'Prompt-level chronology, not OS/perfect isolation. No foreign result/body/liveness inspection or steering.'}
(P/'prospective-isolation-structural198.json').write_text(json.dumps(isolation,indent=2)+'\n')
print(json.dumps(meta,indent=2)); print('Foreign initial guard checks:',len(checks))
