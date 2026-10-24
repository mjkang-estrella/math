#!/usr/bin/env python3
"""Prepare the next exact-C continuation without dispatch or shared writes."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ah-parent'
R=B/'fresh-arithmetic-discovery-r162ah'
OLD=B/'fresh-arithmetic-discovery-r162ag'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ah-brief.txt'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
raw_j=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
tasks=json.loads(raw_t);assert tasks['newAccepted']==19 and tasks['target']==20
own=next(i for i,t in enumerate(tasks['tasks']) if t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ag-codex-astra-r1')
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

old_raw=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ag-brief.txt').read_bytes()
assert sha(old_raw)=='ee72058b684998bcb7510ed7e2d1b037121b8bcb8dda7a2c6f983b245b618be1'
old=old_raw.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old_raw.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('EXACT read-only completed input exceptions')]
prefix=prefix.replace('Arithmetic discovery r162ag — full entropy-overlap continuation.','Arithmetic discovery r162ah — joint entropy-budget continuation.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ag/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ah/.',1)
prefix=prefix.replace('Your completed r162af is PREFREEZE/no nominee:','Your completed r162af and r162ag remain PREFREEZE/no nominee:',1)
prefix=prefix.replace('Own r162ag I/O is explicitly authorized','Own r162ah I/O is explicitly authorized',1)
prefix=prefix.replace('old r162af is strictly read-only through ONLY the exact list below.','old r162af and r162ag are strictly read-only through ONLY the exact list below.',1)
assert prefix.count('fresh-arithmetic-discovery-r162ag/')==0
new_math='''
EXACT continuation after r162ag, beyond the retained r162af payments:
The sealed r162ag notebook is an actual same-author research derivation, not an independently checked proof. Full C is still unchanged/unproved, and no counterexample emerged. Preserve every calculation and its limits rather than offering the Gaussian result, epigraph identity or a conditional bridge as a smaller nominee.

The new common Gaussian rotation supplies the positive conditional Jacobian A DF A+B DG B for A^2+B^2=I and a matrix-log compression with complementary spectral weights. Scalar entropy bounds control full traces, not both arbitrary weighted traces. Retain the exact Jensen remainder and the SAME law/normalization.

The fully derived Gaussian-input comparison is now PAID: if Y is Gaussian and X arbitrary log-concave, Delta(X+Y)>=g tr(Sigma^(-1)CovY), g=log(2pi e)/2-1. It has no minimum-eigenvalue/Poincare or coordinate-independence loss. ONE decreasing covariance flag, conditional scalar entropy-power and SAME source-prefix bounds prove it; retained conditional rough transfer handles singular inputs. Matching a general input to a Gaussian changes the law and cannot be used as an entropy lower comparison without proof.

For TWO arbitrary inputs the exact common chain identity is Delta(S)=sum_i E delta_i(conditional scalar sum)+(1/2)sum_i E log(a_i+b_i)+sum_i I(S_i;(X_<i,Y_<i)|S_<i), with a_i=Var(X_i|X_<i),b_i=Var(Y_i|Y_<i). The scalar gains are paid. The deficit in original covariance must be recovered together with the NEGATIVE log-variance terms using the SAME predictor-information gains; separate winners or simply dropping the information/negative terms is invalid. The complementary spectral weights cannot both be sorted independently while retaining one output chain. An actual isotropic paraboloid log-concave law has final conditional entropy increment g+(1/2)log(d/2+1), so a uniform bound on every individual chain increment is false. This is only a method obstruction, not C's negation.

The simultaneous convex-epigraph lift of ONE output potential decomposition gives Delta(S)>=(1/2)logdet(I+C_res), retaining ALL cross terms after ONE regression on S. Duplicated heights do not manufacture a trace gain. Conditional input potentials are not automatically convex components of the actual convolution potential, and infimal convolution changes its law. A compatible decomposition controlling the original overlap is unconstructed.

The exact dependent positive-definite-matrix test has Delta/kappa ->2log(pi)-1>0 for the specified equal input shapes. Its normalization and covariance are retained; it is one admissible test, not evidence exhausting nonproduct counterexamples.

Spend this continuation on a genuinely JOINT construction at the full C scope. In particular, test whether scalar conditional gains plus the common predictor-information terms can pay all variance/log-variance losses against the ORIGINAL tr M(I-M); try the strongest compatible common/averaged-flag, transport or localization reduction rather than treating one failed coordinate order as an impossibility. The source common-remainder J_C remains another sufficient route. These are suggestions, not an imposed intermediate theorem or an exhaustive list. Any asserted Gaussian replacement, information comparison, tensorization or matrix inequality must be proved for the same actual pair. No hidden universal Poincare/KLS premise, old unproved global stability, positive spectral floor, independent-coordinate assumption, fixed-n compactness-to-universal-rate leap, or incompatible source-surplus spending.

A full proof or a full admissible counterexample is the mathematical objective. If a viable full theorem emerges, freeze EXACT scope before full proof development; independent correctness and contribution review belong to the parent later. If it remains unresolved, retain concrete new derivations, failed compatibility attempts and precise limits; do not spend a round simply restating the joint gap or repeating paid comparisons. No new catalogue/history traversal, old-corpus copying or enlarged artifact-test suite. Reuse actual retained reading honestly, read any newly invoked primary operative proof, and keep evidence proportionate.

'''
direct=[P/x['path'] for x in json.loads((D/'private/completed-direct-inputs.json').read_text())]
direct += [D/'assessment.md']+[OLD/x for x in ['FINAL.md','REPORT.md','packet/private/scope.md','packet/private/research-notebook.md','packet/private/READING-LIMITS.md','packet/private/reading-record.json']]
assert len(direct)==len(set(direct))==43
records=[]
for p in direct:
    assert p.is_file() and not p.is_symlink();raw=p.read_bytes()
    records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(N/'private/completed-direct-inputs.json',records)
section='EXACT read-only completed input exceptions (project-relative POSIX paths):\n'+'\n'.join(x['path'] for x in records)+'\n\n'
section+='''These explicitly enumerated paths authorize no containing namespace,link,old role/brief/status/review or further direct exception. Every prior completed exception is explicitly relisted or forbidden; none propagates automatically. Protected bodies AND their named metadata remain PRIVATE/local under original rights. Copies/excerpts,if needed,stay only inside your own private root with actual reading extents. Do not reuse an inherited manifest. Source101 actual wrapper is build/manuscript/main.tex (2110 bytes,Gitblob208e79bad81ad827bd6da83e44332fd397714940); complete source reading is retained,not recreated by metadata.

The following historical scopes/dispositions are CONTEXT ONLY,retained verbatim. They reopen no target or path. New write root and exact full C govern this continuation:

'''
history=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
extra='\nAdditional prospective literal twins for this continuation:\n*arithmetic*162ah* *arithmetic*r162ah*\n\n'
brief=(prefix+new_math+section+history+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode())
assert {'*arithmetic*162ah*','*arithmetic*r162ah*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,continuation=True,exact_same_full_C=True,no_new_catalogue_or_history_scan=True,source=101,canonical_blobs=13,completed_direct_inputs=len(records),parent_source_body_read=False,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),completed_exact_readonly_inputs=len(records),both_new_literal_twins_verified=True,continuation=True)))
