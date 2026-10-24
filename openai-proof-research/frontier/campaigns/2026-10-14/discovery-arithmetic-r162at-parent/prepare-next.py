#!/usr/bin/env python3
"""Prepare Source121 research; all earlier scopes and literal guards retained."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162au-parent';R=B/'fresh-arithmetic-discovery-r162au';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162au-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'));assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==773 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True);dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162at-brief.txt').read_bytes();assert sha(original)=='a9d289e9cd7f0f1b991346ec48ff10f268958b6ad31e08ad5980299c2352fc1c'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source120')].replace('Arithmetic discovery r162at — confirmed almost-linear-exact-matching operative-proof discovery.','Arithmetic discovery r162au — confirmed almost-linear-edit-distance operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162at/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162au/.',1).replace('FRESH DISTINCT Source120','FRESH DISTINCT Source121',1).replace('Own r162at I/O','Own r162au I/O',1)
instructions='''Read the COMPLETE actual Source121 operative proof,all actual includes and strongest primary/companion interfaces BEFORE selecting a full additional theorem. The ENTIRE stipulated source theorem is ALREADY PAID:ONE uniform randomized approximation scheme for unit-cost edit distance of ARBITRARY explicitly stored strings of total length N with polynomially bounded INTEGER symbols;for EVERY FIXED rational epsilon in(0,1),success probability>=2/3 for a(1+epsilon) distance estimate and worst-case EXPECTED logarithmic-word-RAM time N^(1+o(1));equal strings give zero DETERMINISTICALLY. This is the exact fixed-accuracy asymptotic scope. Read stronger actual geometry,seed,cone,band,comparison,regret,accuracy,numerics and work operations;the catalogue is not their boundary. Upstream proofs are stipulated TRUE;do not audit or nominate the main theorem.

Track expected versus all-path/conditional costs,one uniform algorithm versus fixed-accuracy constants,all N including empty/equal/highly unequal strings,integer alphabet/encoding,word size,input/preprocessing,randomness,success and output conventions,numerical precision,alignment versus a value,and every reduction/call/output cost. Weighted,dynamic,streaming,alignment,small-error or finite-bit variants require complete compatible additional proofs;self-reduction,amplification,rank encoding,metric embeddings and source/classical compositions do not count alone. The older R162AE FULL finite-bit all-word embedding diagnostic and all its preprocessing/evaluation/distortion/quantifier obligations remain unchanged and UNPROVED. DO NOT reopen,rename,weaken,or nominate that target or a restricted substitute. Choose a genuinely different full operation from actual proof reading. This family is distinct from the preceding matching task,not a project-history clearance or claim the edit-distance family was never investigated.

Read actual primary mechanisms before choosing ONE viable direction and doing sustained mathematics. Freeze every hypothesis,quantifier,constant,model and conclusion only when a viable additional operation emerges;prove its entire scope. Parent alone commissions independent correctness and substantial-contribution reviews. No desired-grade retry of an older target.

R162AT is archived PREFREEZE/no nominee. No new theorem/diagnostic selected/frozen. The exact one-bit perfect-weight identity assumes a SUPPLIED exact old optimal primal/laminar-dual pair,with D its value,a_e>=0 edge slacks,z_B>=0. For EVERY actual perfect matching N on2r vertices,r+2D-(2c+b)(N)=blue(N)+2sum a_e+2sum z_B q_B(N),q_B=(cut crossings-1)/2. The new optimum has penalty<=blue(M0)<=r. Safe active coefficient clipping and compact laminar-tree arithmetic are paid;the unweighted source does NOT supply the weighted certificate.

Actual Pettie W-stage cardinality reduction,Gabow certification,adaptive probability/dual/preimage/output costs give a compatible bounded-integer NONPERFECT weighted comparison in W(1+log(W+2))^O(1)(n+m+2)^(1+o(1)) operations on O(log(L+2))-bit words. W is its VALUE,not bit length;perfect forcing raises range to O(nW). Certified-source/expected Las Vegas and full DPS scaling comparisons are paid;uncapped repetition is not all-path bounded. Constant penalty3 on arbitrarily large factor-critical blossoms and compact nested quadratic scans refute particular charges/implementations,NOT weighted algorithms/source invariants. Boundary endpoint SETS and odd matching constraints cannot be dropped. The sufficient unclosed route is ONE compatible weighted state plus a JOINT amortized repair/update budget on the SAME state;certificate construction,original binary arithmetic,all calls/output remain charged. No universal weighted/dynamic/capacitated/deterministic/red-edge diagnostic was frozen. Canonical17 texts read completely;three primary matching texts read fully,flow primary partial,transitive ancestry incomplete. TLS-disabled public primary download,version/recovery/late-read limits disclosed,no optional history traversal. Forty finite examples are not gates;no full matching generator ran. All older scopes/dispositions unchanged.

'''
older=old[old.index('R162AS is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source121-selection.json').read_text());assert sel['catalogue_extent']==[201658,202797] and len(sel['folders'])==1 and len(sel['entries'])==20
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==16
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162at/private/MATH.md',B/'fresh-arithmetic-discovery-r162at/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162at/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162at/private/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[201658,202797),EXACT Source121. Parent used ONE bounded14000-byte window at201658,decoded ONLY FIRST TWO numeric-bold TITLE STRINGS121/122,and selected ONLY121 body. Source122 body and remaining window were not decoded. ONE family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance. Prior finite-bit embedding scope remains excluded;no protected body was read to reopen it.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(x for x in blobs if x['path']==folder+'/build/paper.tex');section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='''There are16 blobs/20 entries including root. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow ACTUAL includes under build/;the actual wrapper is build/paper.tex,not a guessed main.tex. Authenticate selected objects,read every operative section/figure/bibliography and relied-upon dependency. lean/docs/121.md is scoped comparator navigation only;inspect actual scope privately without downstream formal work or end-to-end formalization inference. Distinguish metadata/PDF authentication from semantic/rendered reading.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proofs. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored edit-distance,alignment,string algorithm,geometry,accuracy and cost-budget mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ar* *arithmetic*r162au*\n\n';brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ar*','*arithmetic*r162au*','*structural*r220*'}<=rules(brief.decode());assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162au/.';BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=121,catalogue_extent=[201658,202797],canonical_folders=1,canonical_blobs=16,canonical_entries_including_roots=20,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source122_body_not_decoded=True,prior_R162AE_embedding_target_not_reopened=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=16,canonical_entries=20,all_guards_retained=True,distinct_family=True)))
