#!/usr/bin/env python3
"""Prepare two isolated independent full-scope review prompts; no dispatch/shared writes."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
R=B/'fresh-arithmetic-discovery-r162aj'
roles=['proof','contribution']
roots={k:B/f'arithmetic-r162aj-{k}-r1' for k in roles}
briefs={k:B/f'expanded-target-2026-10-17/arithmetic-r162aj-{k}-brief.txt' for k in roles}
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t
t=json.loads(raw_t);assert t['newAccepted']==19 and t['target']==20
own=next(i for i,x in enumerate(t['tasks']) if x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162aj-codex-astra-r1')
names=[p.relative_to(P).as_posix() for p in [*roots.values(),*briefs.values()]]
checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
    if i==own or x.get('status') not in {'running','queued','waiting'}:continue
    if 'brief' not in x:
        assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
    raw=(P/x['brief']).read_bytes();patterns=rules(raw.decode())
    matches={n:[g for g in sorted(patterns) if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,legacy_limit='Historical native records not reopened; recorded status is not fresh liveness.')
dump(D/'review-prospective-isolation.json',guard)
assert all(not p.exists() for p in [*roots.values(),*briefs.values()])
for p in roots.values():p.mkdir()
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162aj-brief.txt').read_bytes()
assert sha(original)=='adc546b93da2de4367ad84854d9b930214f0344a7691208598cda7c9973cc179'
statement=(R/'packet/STATEMENT.md').read_bytes();proof=(R/'packet/AUTHOR-PROOF.md').read_bytes()
assert sha(statement)=='6a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4'
assert sha(proof)=='7980d626908175daf46c3326860a10888f26b61a252379e941b34636585a3817'
m=json.loads((R/'MANIFEST.json').read_text())
base={'packet/STATEMENT.md','packet/AUTHOR-PROOF.md','packet/COMPARISON.md','packet/private/research.md','packet/private/freeze.json','packet/private/READING-LIMITS.md','packet/private/reading-record.json','packet/private/source-authentication.json','packet/private/selected-tree.json','packet/private/primary-access.json'}
admitted=sorted({x['path'] for x in m['files'] if x['path'] in base or x['path'].startswith(('packet/private/upstream/','packet/private/primary/'))}|{'FINAL.md','REPORT.md'})
assert len(admitted)==79
inputs=[]
for rel in admitted:
    p=R/rel;assert p.is_file() and not p.is_symlink();raw=p.read_bytes()
    inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(D/'private/review-inputs.json',inputs)
common='''This is a NEW independent review round in a FRESH child conversation,not an author continuation. Prior independent review findings/responses/objections: NONE; both first-round reviews are being commissioned now. The author reports no remaining mathematical gap. Do not infer a grade from that report,small tests,artifact seals,another agent's reading ledger,or the parent's19/20 context.

Actual model: Codex / GPT-6 Astra / reasoningEffort high / serviceTier default. Campaign19/20 latestR041;parent alone integrates gates/counts. Publication/uploads/submissions/contacts/browser UI STOPPED. No downstream formalization,manuscript,release,nested agents,git/shared writes,heavy installs or unbounded jobs. EVERY command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. All new scratch,fetches,extracts,renders,notes and final seal must remain in YOUR assigned root. Author bytes AND modes are read-only,including the frozen statement and proof.

Read AGENTS.md,sources/upstream.json,and ONLY acceptance journal binary bytes[4801,6347). Do not decode/hash the whole journal. Source104 catalogue access,if needed,is ONLY sources/CONTENTS.md[173031,176416). Use complete sources/preprints-tree.json(13223 entries,4858136 bytes,SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b);ignore truncated tree.json. ALL operative source proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Validate the new deduction/applicability/compatibility,not upstream truth. Actual source and primary proof interfaces must be read;metadata,abstracts,ledgers and copied excerpts are not independent semantic reading.

The ENTIRE unchanged frozen statement and author proof are embedded below and available at exact admitted paths. Statement SHA2566a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4;proof SHA2567980d626908175daf46c3326860a10888f26b61a252379e941b34636585a3817. Preserve ALL quantifiers,zero endpoints,behavioral opponents,possibly infinite-memory semantics,unrestricted binary numerical data,and the decision-only quasipolynomial BIT bound. Do not repair or narrow the theorem silently,substitute strict-positive payoff,assume a probability floor/fixed number of priorities,or add a strategy-output claim.

Author-sensitive interfaces to examine independently,not declared defects: ordinary AS extraction from expectation,gain-bias completion,actual epsilon-zero attainment/one-player prerequisites,positive target/safety semantics,odd excursion potential and conditional-law completeness,all-prefix martingale pasting,monotone fixed-point encoding/polynomial formula expansion,and universal-graph oracle/bit cost. Source ordinary/stochastic/deterministic-parity algorithms and their stronger operative proofs are paid. Primary HS arbitrary-monotone acceleration and GK full split/reset/merge transfer are real available operations;read their actual scope. Check the CDGO limsup distinction and the DM strict-positive/finite-memory distinction against ACTUAL strongest proofs,not headlines. Do not treat a naive failed composition or a slower known recursion as a lower bound.

You must NOT inspect the other review's directory,brief,status,body,findings or result,or query any live peer/task. Do not ask the author or another reviewer for a preferred grade. Parent will handle any necessary repair/new review later. Each review is full-scope and independent;no correctness verdict may substitute for contribution comparison or vice versa.

The exact completed input list below is the ONLY exception to the inherited arithmetic-r162aj guards. No containing namespace,link,previous author direct exception,old role/brief/status/activity alias,control fixture or original-history derivative is admitted automatically. The complete original discovery brief is preserved below as HISTORICAL CONTEXT:its discovery direction,write root,old-body permissions and any instruction to choose/develop a new theorem are superseded by THIS review task. Every inherited wildcard/substring prohibition remains in force on full-project-relative POSIX path.casefold() BEFORE descent/filename/body selection,with your own root and exactly listed readonly inputs as narrow exceptions. In particular BOTH review namespaces are blocked except your own I/O. Do not widen a direct exception by following a link.

At most ONE correctly pruned optional ORIGINAL-history traversal is allowed if relevant to this review. Apply every original literal wildcard/substring first at every depth;do not rerun an old scan,inventory ancestors,select corpus/role/helper derivatives or use a size/extension cutoff after eligibility. No optional traversal means no clearance claim. Record actual extents,late stronger reads,truncations/recoveries,versions/access failures,coarse omissions and false admissions. This is not an exhaustive history or literature-priority task. Essential unverified dependencies must be identified explicitly,not hidden under a PASS.

Protected source/primary/history/search/extract/render/copied bodies AND their named metadata remain PRIVATE/local under original rights. Reuse admitted bytes read-only when sufficient;new searches/downloads/excerpts stay in your own private root. Seal YOUR fresh exact selection once;do not inherit the author's manifest or copy the whole corpus for ceremony. Return your substantive full review,precise dependency/reading limits,outside REPORT,detached FINAL/MANIFEST/REPORT SHA256 anchors,and a small read-only explicit-anchor verifier with proportionate copied controls. Artifact checks are not mathematical gates. Mathematics and actual strongest-primary comparison dominate evidence administration.

'''
role_text={
'proof':'''Task: adversarial FULL CORRECTNESS review of the ENTIRE unchanged frozen theorem AND unchanged author proof. Independently reconstruct every nontrivial deduction,source interface,game-theoretic quantifier and algorithmic bit bound;seek counterexamples and hidden hypotheses. Review actual operative primary dependencies,including any previously unread essential antecedents. A stitched proof summary or tiny finite examples are insufficient. Supply independent derivations and a clear full-scope verdict PASS,NEEDS_REPAIR,or INCOMPLETE. PASS requires no necessary author correction and no essential verification obligation remaining,relative only to stipulated upstream truth. If repair is necessary,identify exact location,reason,full affected scope and concrete example where available;do not modify the author. No substantial-contribution grade,acceptance or count.

''',
'contribution':'''Task: independent FULL SUBSTANTIAL-CONTRIBUTION review,conditional on correctness of the ENTIRE unchanged frozen theorem. Read actual strongest source,companion and primary proof operations and construct the strongest compatible integrated reduction covering EVERY frozen assertion. Assess SUBSTANTIAL,TECHNICAL,or INCOMPLETE at that full scope. For TECHNICAL,give the actual integrated source/classical/primary derivation paying the whole claimed operation;credit all compatibility/cancellation and uniformity steps,not just some sublemmas. For SUBSTANTIAL,identify the precisely closed nonroutine residual and substantiate why the strongest actual known compatible operations leave it,without a priority/exhaustive-search claim. If an essential comparison remains unsettled,return INCOMPLETE rather than inferring either grade from difficulty,novel terminology,a strict-positive gap or a failed naive reduction. Routine transfers,rediscoveries,equivalent formulations and unproved bridges do not count. Do not issue a correctness PASS,acceptance or campaign increment;the other review remains uninspected.

'''}
output=[]
for role in roles:
    root=roots[role].relative_to(P).as_posix()
    header=f'R162AJ independent {role} review — round1.\nWrite ONLY {root}/. Your exclusive root exists empty.\n\n'
    listing='EXACT completed readonly input paths(project-relative POSIX):\n'+'\n'.join(x['path'] for x in inputs)+'\n\n'
    task=(header+role_text[role]+common+listing+'--- IMMUTABLE FROZEN STATEMENT ---\n').encode()+statement+b'\n--- UNCHANGED FULL AUTHOR PROOF ---\n'+proof+b'\n--- COMPLETE ORIGINAL DISCOVERY BRIEF: HISTORICAL CONTEXT; REVIEW OVERRIDES ABOVE ---\n'+original
    assert rules(original.decode())<=rules(task.decode())
    assert task.startswith(header.encode()) and b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n' in task
    briefs[role].write_bytes(task)
    output.append(dict(role=role,root=root,brief=briefs[role].relative_to(P).as_posix(),bytes=len(task),sha256=sha(task),clientRequestId=f'twenty-20261023-arithmetic-r162aj-{role}-codex-astra-r1',title='R162AJ: independent full '+('correctness' if role=='proof' else 'substantial-contribution')+' review',full_original_discovery_brief_embedded=True,full_statement_and_proof_embedded=True,completed_readonly_inputs=len(inputs),all_previous_literal_guards_retained=True,other_review_uninspected=True))
dump(D/'review-preparation.json',dict(reviews=output,statement_sha256=sha(statement),author_proof_sha256=sha(proof),independent_fresh_rounds=True,prior_review_findings=None,publication='STOPPED',count_change=0))
print(json.dumps(dict(reviews=output,foreign_original_briefs_checked=len(checks))))
