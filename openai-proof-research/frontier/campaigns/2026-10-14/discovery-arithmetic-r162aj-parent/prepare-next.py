#!/usr/bin/env python3
"""Prepare a distinct Source105 discovery after conditional contribution intake."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ak-parent'
R=B/'fresh-arithmetic-discovery-r162ak'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ak-brief.txt'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
raw_j=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
t=json.loads(raw_t);assert t['newAccepted']==19 and t['target']==20
own=next(i for i,x in enumerate(t['tasks']) if x.get('clientRequestId')=='twenty-20261023-arithmetic-r162aj-contribution-codex-astra-r1')
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
    if i==own or x.get('status') not in {'running','queued','waiting'}:continue
    if 'brief' not in x:
        assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
    raw=(P/x['brief']).read_bytes();patterns=rules(raw.decode())
    matches={n:[g for g in sorted(patterns) if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,legacy_limit='Recorded status is not live liveness;historical native records not reopened.',foreign_live_queries=False,other_review_status_or_body_not_queried=True)
dump(D/'contribution-integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162aj-brief.txt').read_bytes()
assert sha(original)=='adc546b93da2de4367ad84854d9b930214f0344a7691208598cda7c9973cc179'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source104')]
prefix=prefix.replace('Arithmetic discovery r162aj — confirmed mean-payoff/stochastic/parity-game operative-proof discovery.','Arithmetic discovery r162ak — confirmed perfect-completeness 2-to-1 operative-proof discovery.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aj/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ak/.',1)
prefix=prefix.replace('FRESH DISTINCT Source104','FRESH DISTINCT Source105',1).replace('Own r162aj I/O','Own r162ak I/O',1)
instructions='''Read the COMPLETE actual Source105 theorem/proof construction and its operative companion/primary interfaces before selecting and developing a full result. The entire stipulated perfect-completeness2-to-1 theorem is ALREADY PAID:for EVERY fixed rational delta in(0,1),NP-hardness of distinguishing satisfiable explicit unweighted games from value<=delta,with alphabet depending only on delta and EXACTLY TWO preimages of every right-hand label under every constraint map. Read the actual stronger proof,not just this catalogue headline. Do not nominate routine hardness transfers,alphabet/parameter substitutions,unweighted-multiset conversion or known composition/derandomization already paid by its operative proof.

Track fixed-versus-growing parameters,uniformity and reduction runtime,alphabet dependence,constraint multiplicities,degrees,encoding lengths,exact completeness,regularity and soundness quantifiers. A standard operation can be compatible even when one naive route fails. Do not infer a nonroutine step from an unproved bridge or a familiar transformation's failure. Choose ONE promising full operation after the strongest integrated source/actual-primary reduction;then do sustained mathematical work. No restricted or renamed substitute for any older full target or desired-grade retry. When a viable full theorem emerges,freeze its exact hypotheses,quantifiers,constants and conclusion before extended proof drafting;parent alone commissions independent gates.

R162AJ is a FULL frozen author-proof nominee with an independent full-scope contribution assessment TECHNICAL,CONDITIONAL ON CORRECTNESS OF THE ENTIRE UNCHANGED THEOREM. Separate correctness has not yet been integrated;the condition is NOT discharged. No correctness grade,acceptance or count follows. Do not query/read the correctness task's brief,status,root,body or result,and do not rename/restrict the nominee for another grade. No message is sent to that reviewer carrying this assessment.

Its exact frozen scope is ONE deterministic finite-bit algorithm A and numerical C computing the n-bit winning set for EVERY finite explicit total turn-based Max/Min/chance arena,EVERY signed binary integer reward,EVERY exact rational chance law(nonnegative,row-sum1,including zeros/unreduced encodings),EVERY unrestricted binary nonnegative priority and EVERY exact rational threshold theta:there exists a possibly infinite-memory behavioral Max strategy sigma such that for EVERY behavioral Min strategy tau,the probability of liminf average reward>=theta AND least priority occurring infinitely often even equals1. Complete binary length L counts ALL numerical data/delimiters. Cost<=2^(C log2(L+2)^2) elementary bit operations includes parsing,validation,arithmetic,graph/oracle implementations and output;malformed encodings rejected within that bound. No gap,graph,probability-floor,fixed-priority-count or finite-memory restriction. It is a DECISION-only theorem,not strategy-output/online-response or finite-memory complexity. Statement SHA2566a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4 remains immutable.

The independent TECHNICAL comparison pays zero endpoints by source gain-bias completion,MDP occupation flows and sparse parity trials,GK positional-Min/epsilon-zero attainment transfer and fixed-Min limsup/liminf value equality. It pays CDGO's actual layered decomposition as monotone target/safety equations,all conditional/spoiling/layer obligations,polynomial syntax,and HS universal-graph evaluation on the n-singleton basis with every oracle and bit cost charged. The author's stronger compensated-prefix strategy work is credited;the decision-only theorem is also paid without requiring that stronger two-player invariant as an additional frozen assertion. This is not pathwise limsup/liminf equality,a finite-memory result,a worldwide-priority claim or a claim that one source alone states the result. Do not develop this game nominee in the new2-to-1 family. Its full scope and all old scopes/dispositions remain unchanged.

'''
old_scopes=old[old.index('This distinct family does NOT retry high-precision HP.'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
selected=json.loads((D/'private/contribution-intake/Source105-selection.json').read_text())
folders=selected['folders'];blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(folders)==1 and len(blobs)==13 and len(selected['entries'])==16
folder=folders[0];wrapper=next(x for x in blobs if x['path']==folder+'/build/main.tex')
assert wrapper['size']==2286 and wrapper['sha']=='281661b221e6e51e19658cad1b6df225cf7077fd'
CR=B/'arithmetic-r162aj-contribution-r1';AR=B/'fresh-arithmetic-discovery-r162aj'
direct=[D/'contribution-assessment.md',CR/'FINAL.md',CR/'private/REVIEW.md',CR/'private/READING-LIMITS.md',AR/'packet/STATEMENT.md']
inputs=[]
for p in direct:
    raw=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',selected)
section=f'''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[176416,177336),EXACT Source105 body. Parent decoded only the FIRST TWO numeric-bold TITLE STRINGS105/106 from ONE bounded14000-byte window starting176416,then selected ONLY105 body. Source106 body was NOT decoded/selected. No child title locator,extra catalogue/family screen,whole-catalogue opening/decoding or ancestor hunt. ONE confirmed folder has13 blobs/16 complete-tree entries including root. Parent source-proof reading:NONE;metadata is navigation,not an operative theorem/proof or a clearance certificate.

Confirmed canonical folder:
{folder}
ACTUAL wrapper selected from complete-tree metadata:
{wrapper['path']}
bytes2286;Git blob281661b221e6e51e19658cad1b6df225cf7077fd.
Fetch pinned raw paths under exactly this folder and follow actual textual includes;do not guess root main.tex or other build directories. Authenticate selected objects,read complete operative proof interfaces,and distinguish PDF authentication from semantic reading/rendering.

Read these FIVE exact COMPLETED originals(project-relative POSIX paths):
'''
section+='\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize no containing namespace,link,source/primary body bundle,earlier direct exception,role/status/brief/activity alias or other review. In particular correctness-review material remains blocked. The completed review is scope/payment context,not new-family proof reading. Protected bodies AND their named metadata remain PRIVATE/local under original rights;copies/excerpts stay only in your own private root. No previous exception propagates.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized for this distinct family. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and byte/body reads at every depth. Query genuine authored mechanisms for2-to-1 projection constraints,PCP/Label Cover,perfect completeness,soundness,alphabet/degree/constraint regularization and related operations as relevant. No blanket asymptotic/projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivative selection,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through their equal/higher headings and record exact extents,truncations/recovery,late reads,coarse omissions and false admissions. If no optional traversal is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Earlier full scopes/dispositions follow as CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ak* *arithmetic*r162ak*\n\n'
brief=(prefix+instructions+old_scopes+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ak*','*arithmetic*r162ak*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[:2]==['Arithmetic discovery r162ak — confirmed perfect-completeness 2-to-1 operative-proof discovery.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ak/.']
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=105,catalogue_extent=[176416,177336],canonical_folders=1,canonical_blobs=13,canonical_entries_including_roots=16,completed_direct_inputs=5,parent_source_body_read=False,skipped_source_body_not_selected=106,conditional_technical_disposition_preserved=True,other_review_status_or_body_not_queried=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=13,canonical_entries=16,both_new_literal_twins_verified=True,distinct_family=True)))
