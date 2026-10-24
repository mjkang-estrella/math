#!/usr/bin/env python3
"""Prepare one distinct pinned Source104 round; never dispatch or edit shared state."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162aj-parent'
R=B/'fresh-arithmetic-discovery-r162aj'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162aj-brief.txt'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
raw_j=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
tasks=json.loads(raw_t);assert tasks['newAccepted']==19 and tasks['target']==20
own=next(i for i,t in enumerate(tasks['tasks']) if t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ai-codex-astra-r1')
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,t in enumerate(tasks['tasks']):
    if i==own or t.get('status') not in {'running','queued','waiting'}:continue
    if 'brief' not in t:
        assert 'nativeTaskName' in t and 'taskId' not in t;legacy.append(i);continue
    raw=(P/t['brief']).read_bytes();patterns=rules(raw.decode())
    matches={n:[g for g in sorted(patterns) if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,legacy_limit='Historical native entries lack original briefs; no live query or reopening. Recorded status is not fresh liveness.',foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
old_raw=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ai-brief.txt').read_bytes()
assert sha(old_raw)=='3c9ae9f64bf6717f42f1f0d8fc3367b561e2d174644aeac600664ee772ba549e'
old=old_raw.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old_raw.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source103')]
prefix=prefix.replace('Arithmetic discovery r162ai — confirmed logarithmic-space derandomization operative-proof discovery.','Arithmetic discovery r162aj — confirmed mean-payoff/stochastic/parity-game operative-proof discovery.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ai/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aj/.',1)
prefix=prefix.replace('FRESH DISTINCT Source103','FRESH DISTINCT Source104',1)
prefix=prefix.replace('Own r162ai I/O','Own r162aj I/O',1)
instructions='''Read the COMPLETE actual Source104 core and operative companions across all FOUR confirmed folders before selecting a new full-scope operation. Track the actual deterministic and randomized ordinary mean-payoff constructions,the separate stochastic expectation-of-pathwise-liminf threshold theorem,and the separate deterministic mean-payoff-parity theorem. Entire stipulated quasipolynomial bit algorithms,ordinary exact values/optimal positional strategies,randomized certification/expected-time conversion and all stronger source proof operations are ALREADY PAID. Do not nominate their headlines,threshold shifts,standard rational reconstruction,derandomization or routine model substitutions.

Keep complete binary input length as the resource parameter. Signed reward magnitude,exact rational chance probabilities,zero-value endpoints,unrestricted binary priorities,numerical encodings,strategy descriptions,memory,objective quantifiers and bit-operation costs must remain explicit whenever invoked. The separate stochastic and parity extensions do not automatically supply one joint stochastic-parity algorithm. Conversely a failed naive composition does not show that a stronger compatible source/primary operation cannot pay it. No particular new joint objective is imposed by this brief: choose ONE viable full operation only after the actual strongest proof reading,then develop it seriously. No hidden favorable graph,probability,priority,precision or memory restriction may replace a selected full target.

This distinct family does NOT retry high-precision HP. Preserve its exact original scope: ONE deterministic transducer and ONE numerical C for EVERY explicit binary ordered/read-once branching program,every T>=0,w>=1,start,final accepting subset and unary q>=1;on fixed explicit input length N+q,output binary0<=a<=2^(q+2) with |a*2^(-q-2)-Pr[B(U_T)=1]|<=2^-q,using at most C log2(N+q+2) counted work bits and (N+q+2)^C elementary bit operations. Read-only endmarked input and one-way write-only output unavailable as storage;all live registers,addresses,arithmetic,recomputation and encoding validation charged. No fixed-width/horizon,regularity,gap,minimum acceptance,unique-path or favorable-precision substitute. Binary programs were the original selected model,not an arbitrary-real matrix theorem. Neither HP nor its negation is proved;no theorem frozen or grade assigned.

The strongest paid HP comparison retains one regenerated downward-rounded inverse,exact logarithmic short band,ordered Richardson identity/band nilpotence,signed probabilistic realization without a length-normalization loss,normalized coefficient bounds,fully charged matrix powering,clipping,exact-count conversion and streamed output. With B=ceil(log2(N+2)) it still costs O(B log(2+min(T,q)/B)+log(q+2)) space and a generally nonconstant time exponent at full precision. Generic positive contraction/nilpotence still embeds rare exact counts;that is not a lower bound. HP conditionally yields exact polynomial-clock #L path counts. The complete logarithmic-space read-only count-table verifier does not generate its same globally consistent certificate. A full compatible high-precision evaluator or certificate generation remains unpaid;these are sufficient,not necessary/exhaustive routes. Source103's actual arbitrary-precision controller charges its digit clock,not its logarithm. Its compiler is terminating;generated deciders have supplied bounds,without a claimed polynomial compiler runtime in description length. All these scopes and payments stay immutable;do not develop HP in the new game round.

'''
entropy=old[old.index('The old entropy family is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
selected=json.loads((D/'private/intake/Source104-selection.json').read_text())
folders=selected['folders'];blobs=[x for x in selected['entries'] if x['type']=='blob']
assert len(folders)==4 and len(blobs)==52 and len(selected['entries'])==71
wrappers=[]
for folder in folders:
    options=[x for x in blobs if x['path'].startswith(folder+'/') and x['path'].endswith('/main.tex')]
    assert len(options)==1;wrappers.append(options[0])
expected=[('build/source/main.tex',1080,'67dee7dde1ceb8883c452dd48e1b0a5fc4d30764'),('build/main.tex',807,'2321ac23c03712683629eb43be67ac449f8f1500'),('build/source/main.tex',1210,'6b696aff1e9abe160dcfe30e8630c129f0231947'),('build/build/main.tex',2512,'311371b66bc71be93d220c22d6dc895908b01ef5')]
for folder,w,(rel,size,blob) in zip(folders,wrappers,expected):assert w['path']==folder+'/'+rel and w['size']==size and w['sha']==blob
direct=[D/'assessment.md']+[B/'fresh-arithmetic-discovery-r162ai'/x for x in ['FINAL.md','packet/private/scope.md','packet/private/READING-LIMITS.md','packet/private/reading-record.json']]
records=[]
for p in direct:
    raw=p.read_bytes();records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(N/'private/completed-direct-inputs.json',records);dump(N/'private/canonical-selection.json',selected)
section='''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[173031,176416),EXACT Source104 body. The selected title/description was incidentally exposed in an earlier parent bounded recovery;that was not source-proof reading. Parent now selected ONLY104's body in ONE bounded14000-byte read starting173031. Next heading position was located as bytes WITHOUT decoding its title/body. No extra family/title screen,whole-catalogue decoding or ancestor hunt. FOUR confirmed folders have52 blobs/71 complete-tree entries including roots. Parent source-proof body reading:NONE. Metadata is navigation,not proof applicability or clearance.

Confirmed folders and ACTUAL wrappers from complete-tree metadata:
'''
for folder,w in zip(folders,wrappers):section+=folder+'\n'+w['path']+'\nbytes'+str(w['size'])+';Git blob '+w['sha']+'.\n'
section+='''
Fetch pinned raw paths from complete-tree entries under exactly these four folders. Follow actual textual includes/companions;do not guess root main.tex or assume the same build directory. Authenticate every selected object and distinguish PDF authentication from semantic text/rendered reading.

Read these FIVE exact COMPLETED originals as narrow disposition context(project-relative POSIX paths):
'''
section+='\n'.join(x['path'] for x in records)
section+='''
These exceptions authorize no containing namespace,link,old copied/source bundle,prior direct exception,role/brief/status/activity alias or other review. Protected completed bodies AND their named metadata remain PRIVATE/local under original rights;copies/excerpts stay only in your own private root. No old exact exception propagates. Old HP/entropy materials are scope/disposition context,not the new direction.

At most ONE correctly pruned optional original-history traversal is authorized for this DISTINCT family. Apply EVERY inherited guard/substring before descent,filename eligibility or byte reads at EVERY depth. Query genuine authored mechanisms for mean-payoff/stochastic/parity games,threshold objectives,policy/strategy extraction,progress measures,certification,resource parameters and objective compatibility as relevant. No broad O(n)/case-insensitive asymptotic scan,corpus inventory,old scan replay or protected derivative selection. Follow eligible ORIGINAL operative hits through equal/higher headings;record extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no traversal occurs,say so. No live peer/task/status/body query or exhaustive-clearance claim. Actual proof reading remains required even when summaries/metadata are available.

Historical full scopes/dispositions follow as CONTEXT ONLY;they reopen no target or linked path:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162aj* *arithmetic*r162aj*\n\n'
brief=(prefix+instructions+entropy+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162aj*','*arithmetic*r162aj*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,continuation=False,distinct_family=True,source=104,catalogue_extent=[173031,176416],canonical_blobs=52,canonical_entries_including_roots=71,canonical_folders=4,completed_direct_inputs=5,parent_source_body_read=False,navigation_limits=selected['navigation_limits'],publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=52,canonical_entries=71,both_new_literal_twins_verified=True,distinct_family=True)))
