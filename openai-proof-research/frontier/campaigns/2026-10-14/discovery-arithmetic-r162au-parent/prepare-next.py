#!/usr/bin/env python3
"""Prepare distinct Source124 discovery; preserve scopes, guards, and standing instructions."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4]; B=P/'frontier/campaigns/2026-10-14'; D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162av-parent'; R=B/'fresh-arithmetic-discovery-r162av'; BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162av-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'))
assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==774 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162au-brief.txt').read_bytes();assert sha(original)=='2bcbe035c3ca15ce680604815446e4463476a7eccf1b96d32e119bfa9102211f'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source121')].replace('Arithmetic discovery r162au — confirmed almost-linear-edit-distance operative-proof discovery.','Arithmetic discovery r162av — confirmed three-machine-scheduling operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162au/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162av/.',1).replace('FRESH DISTINCT Source121','FRESH DISTINCT Source124',1).replace('Own r162au I/O','Own r162av I/O',1)
instructions='''Read the COMPLETE actual Source124 operative proof,all actual mathematical includes and strongest primary/companion interfaces BEFORE selecting a full additional theorem. The ENTIRE stipulated source theorem is ALREADY PAID:ONE uniform DETERMINISTIC POLYNOMIAL-TIME algorithm for NONPREEMPTIVE UNIT-LENGTH jobs with ARBITRARY precedence constraints on THREE identical parallel machines,for an EXPLICIT precedence graph;it minimizes makespan,decides deadline feasibility EXACTLY,and CONSTRUCTS a feasible schedule. Read every stronger actual bounded-description,separator,global-boundary,simplification,list,construction and runtime operation. The catalogue is not the boundary of paid operations. Upstream proofs are stipulated TRUE;do not audit or nominate the main theorem.

Track a single uniform algorithm and its full bit/input/output cost;all graph sizes including empty/degenerate instances,precedence and encoding conventions,integer/binary deadlines,feasibility versus optimization versus construction,nonpreemption,identical machines,unit jobs,global inherited boundary consistency and every recursive state/reduction/oracle call. Generalized machine counts,processing times,release/deadline constraints,weighted objectives,counting,enumeration,parallel/dynamic or fine-grained claims require their OWN complete compatible proofs. Standard self-reduction,scaling,amplification,DP compilation and source/primary/classical composition do not count by themselves. Do not freeze a family before reading actual primary operations or select a known-paid corollary as the requested extra finding.

Choose ONE viable genuinely different full operation after reading actual proofs and carry out sustained mathematics. Freeze every hypothesis,quantifier,constant,model and conclusion only when a viable additional operation emerges;prove its ENTIRE scope. Parent alone commissions independent correctness and substantial-contribution reviews. No desired-grade retry or reopening/narrowing/renaming of an older unpaid target. All old scopes and dispositions remain unchanged. This scheduling family is distinct from the preceding weighted edit task;there is no project-history clearance or never-before-investigated assertion.

R162AU is archived PREFREEZE/no nominee;no new theorem/diagnostic selected/frozen. Its retained AUTHOR comparison is,for EVERY FIXED positive integer C and FIXED rational epsilon in(0,1),arbitrary explicit strings of total length N with promised exact STATIC INTEGER metric costs<=(N+2)^C:expected(N+2)^(8/5+o(1)) logarithmic-word operations,integer VALUE always>=distance and<=(1+epsilon)distance with probability>=2/3,equal strings zero deterministically. All metric calls,input/preprocessing,randomness,arithmetic/output charged;explicit full metric-table parsing/storage extra. Not alignment output,all-path time,arbitrary binary/real costs or efficient joint epsilon dependence. Weighted crossing geometry,nested actual-boundary mass-bin nets,shared-cell counts,primary short-target private-stream factor-eight seeds,Lipschitz singleton cones and ONCE-only terminal-frontier error are retained source/primary compositions with conditional first-request work and full numerical/dependency budgets. Largest paid weighted seed remains n^(8/5). A same-domain simultaneous subpolynomial-factor seed costing(1+|I|)N^o(1)conditionally per first request is a SUFFICIENT unclosed route,not a frozen diagnostic or necessary algorithmic condition. Near-linear factor-O(N)coarse estimation fails the UNCHANGED cone/schedule budget;clipped-Lipschitz and atomic-capacity examples refute specified relaxations,NOT weighted algorithms/source proofs. Old R162AE full finite-bit all-word embedding diagnostic remains excluded/unchanged. Canonical15 texts/153982 bytes read completely;DKK v1 entire text read;AKO/Mao-Rubinstein/MTW partial;late reference/start/rendered-page reads disclosed;transitive ancestry incomplete. No optional history traversal. Finite checks are not gates;no full algorithm executed. Artifact limitation:unchanged bundled verifier rejects unique UNSORTED manifest order;parent independently authenticated exact membership/hashes/modes and ran ONE-assertion in-memory uniqueness correction. Original sealed bytes remain unchanged. No correctness/contribution grade or count.

'''
older=old[old.index('R162AT is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source124-selection.json').read_text())
assert sel['catalogue_extent']==[205987,207322] and len(sel['folders'])==1 and len(sel['entries'])==86
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==69
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162au/private/MATH.md',B/'fresh-arithmetic-discovery-r162au/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162au/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162au/private/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[205987,207322),EXACT Source124. Parent used ONE bounded14000-byte window[202797,216797),decoded ONLY FIRST TWO numeric-bold TITLE STRINGS122 and124,and selected ONLY124 body. Source122 trace-reconstruction TITLE was skipped on known completed Structural163 paid-composition context,WITHOUT decoding its body. The next numeric-bold heading was used ONLY as a byte boundary;its title/body and remainder were not decoded. ONE family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(x for x in blobs if x['path']==folder+'/build/paper.tex');section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='''There are69 blobs/86 entries including root:13 non-PDF nonvendor textual objects,one compiled PDF,and55 vendored PGF/runtime blobs. Authenticate exact selected metadata/bytes and read EVERY operative mathematical text,actual include,figure,bibliography and relied-upon dependency. Follow actual build/paper.tex includes;do not guess main.tex. Vendored typography/runtime authentication is separate from mathematical semantic reading;do not count those55 bodies as operative proof reading or silently ignore relied-upon material. Metadata display was truncated in the parent's first large listing;the actual wrapper,nonvendor list and counts were subsequently recovered exactly. Parent source-proof reading:NONE. lean/docs/124.md is scoped comparator navigation only;no downstream formal work or end-to-end formalization inference. Distinguish PDF authentication from rendered/semantic reading.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proofs. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored scheduling,precedence,partial-order,separator,bounded-state and algorithmic-cost mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Seal once with explicit detached anchors and a read-only verifier. Check exact safe UNIQUE membership,hashes,lengths,modes and copies. If you require sorted manifest records,sort before sealing;do not reject a valid ordering after sealing or modify sealed inputs. Distinguish artifact defects and corrected independent authentication from mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162av* *arithmetic*r162av*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162av*','*arithmetic*r162av*','*structural*r220*'}<=rules(brief.decode());assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162av/.';BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=124,catalogue_extent=[205987,207322],canonical_folders=1,canonical_blobs=69,canonical_entries_including_roots=86,nonvendor_texts=13,vendor_runtime_blobs=55,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source122_body_not_decoded=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=69,canonical_entries=86,all_guards_retained=True,distinct_family=True)))
