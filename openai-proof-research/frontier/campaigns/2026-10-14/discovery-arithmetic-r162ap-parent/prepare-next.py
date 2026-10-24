#!/usr/bin/env python3
"""Prepare Source114 discovery while retaining all prior scopes and literal guards."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162aq-parent';R=B/'fresh-arithmetic-discovery-r162aq';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162aq-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'));assert not git('diff','--cached','--name-only').strip();assert t['newAccepted']==19
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==764 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ap-brief.txt').read_bytes();assert sha(original)=='ab7ef172272151fc943f3500369b8969b5b42d3bac9cca17d490abf9d3a0722f'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source113')]
prefix=prefix.replace('Arithmetic discovery r162ap — confirmed perfect-matching counting and entropy operative-proof discovery.','Arithmetic discovery r162aq — confirmed common-integer-polymatroid-base operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ap/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aq/.',1).replace('FRESH DISTINCT Source113','FRESH DISTINCT Source114',1).replace('Own r162ap I/O','Own r162aq I/O',1)
instructions='''Read BOTH COMPLETE actual Source114 operative proofs, all actual includes and strongest primary/companion interfaces BEFORE selecting a full additional theorem. The ENTIRE stipulated counting theorem is ALREADY PAID: an FPRAS for common INTEGER bases of TWO integral polymatroids of equal total rank supplied by exact rank-value oracles,with BINARY capacities/total rank,each integer vector counted ONCE,and every-execution polynomial oracle calls and outside-oracle BIT work in ground-set size,binary input length,inverse relative tolerance and log inverse failure. No labelled-copy expansion is free. The independence-oracle matroid companion,common bases,and common independent sets of prescribed,unrestricted or maximum cardinality even at unequal ranks are also paid. Read and credit every stronger actual port,signature,geometry,evaluation,weighted,conditioning,precision and sampler operation; a catalogue headline is not their boundary. Upstream proofs are stipulated TRUE;do not audit them.

Keep one full oracle/bit model: exact oracle domains and answer costs,rank/submodularity promises,feasibility and zero counts versus small positive counts,integer vectors versus clone labels,binary capacities,ground-set/rank dependence,error/failure parameters,all executions,random bits,preprocessing,output size and every reduction cost. Ordinary replication,padding,truncation,self-reducibility,conditioning,duality,approximate sampling or compatible source/classical compositions do not count alone. Read actual primary mechanisms before choosing ONE viable direction;do sustained mathematics. Freeze a precise full theorem only with a viable additional argument,then prove its entire scope. Parent alone commissions independent correctness and substantial-contribution gates. No restricted/renamed substitute or desired-grade retry of an older target.

R162AP is archived PREFREEZE/no nominee. Preserve FULL E3:EVERY integer m>=1,EVERY finite loopless LABELLED multigraph G on2m vertices with a perfect matching,EVERY real feasible x in its matching polytope INCLUDING ALL boundary faces/zero-one coordinates. F(x)=-sum x_e ln x_e;H_G(x) is maximum Shannon entropy over ALL labelled matching laws with mean x;0ln0=0. Diagnostic:F-H<=(m-1)ln3. No simplicity,connectedness,degree,symmetry,positive marginal floor,interior,rationality or favorable-size restriction;no loops,infeasible mean,zero-count entropy law,algorithm/bit-runtime/output assertion or full equality classification. Neither E3 nor its negation proved;no theorem frozen,grade/count assigned. This is distinct from the continuous entropy-overlap target.

Source113's ENTIRE counting,all-hole/replica/precision and boundary entropy/face-rank/weighted operations are paid. Exact parallel collapse,forced edges/components,SAME crossing-label tight-cut defect additivity,stationary product-weight law D=-ln Z_Q(x),covariance K diag(1/x)K>=K,full-boundary ordinary/all-face hafnian and weighted equivalences,and same-label self-gluing amplification m_k=2^k(m-1)+1,D_k=2^kD are compatible paid reductions. Away from stationarity the variational inequality is D>=-ln Z_Q(x),NOT reversed. A uniform all-instance rate D<=m ln3+o(m) would imply exact E3. The unpaid core is the universal sharp hafnian bound Z_G(x)>=3^(1-m),or another complete E3 argument. A strict-cut positive fixed-point bound plus full induction would suffice;it is not asserted necessary for every proof.

Degree-three/star,bipartite permanent,source equality faces and complete-graph comparisons are paid. Dense strict local maxima and the exact Petersen fixed point with six positive adjacency eigenvalues defeat specific shortcuts while still satisfying E3. Vertex deletion retains a SAME-law conditional-KL cost equal to(m-1)ln3 on equality faces;direct hafnian residuals are nonstochastic and the fixed-point recurrence is tautological. Bounded floating-point tests and exact finite enumeration are not full proofs. Both canonical texts were fully read;transitive primary ancestry incomplete,late revised-ACDD reads/version/access/text-recovery limits disclosed,no optional history traversal. No E3 or restricted matching substitute is reopened here.

'''
older=old[old.index('R162AO is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source114-selection.json').read_text());assert sel['catalogue_extent']==[189149,191164] and len(sel['folders'])==2 and len(sel['entries'])==21
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==15
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162ap/private/MATH.md',B/'fresh-arithmetic-discovery-r162ap/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162ap/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162ap/private/FINAL.md']
inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[189149,191164),EXACT Source114. Parent used ONE bounded14000-byte window at189149,decoded ONLY FIRST TWO numeric-bold TITLE STRINGS114/115,selected ONLY114 body. Source115 body and remaining window were not decoded. ONE new family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance.

Confirmed canonical folders and ACTUAL wrappers from the complete pinned tree:
'''
for folder in sel['folders']:
 section+=folder+'\n';w=next(x for x in blobs if x['path']==folder+'/build/main.tex');section+=f"ACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='''There are15 blobs/21 entries including roots. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow ACTUAL includes;do not guess root main.tex or build/latex/. Authenticate selected objects,read BOTH complete operative proofs and every relied-upon appendix. Distinguish metadata/PDF authentication from semantic or rendered-page reading. lean/docs/114.md is a scoped comparator-navigation pointer only;inspect its actual scope privately without downstream formal work or inference of end-to-end formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proof reading. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored polymatroid/matroid intersection,counting,rank-oracle,exchange,integer-polytope and compatible sampling/optimization mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162aq* *arithmetic*r162aq*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162aq*','*arithmetic*r162aq*','*structural*r220*'}<=rules(brief.decode());assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aq/.'
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=114,catalogue_extent=[189149,191164],canonical_folders=2,canonical_blobs=15,canonical_entries_including_roots=21,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source115_body_not_decoded=True,full_matching_entropy_E3_preserved=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=15,canonical_entries=21,all_guards_retained=True,distinct_family=True)))
