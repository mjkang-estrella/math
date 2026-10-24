#!/usr/bin/env python3
"""Prepare distinct Source113 research with all inherited literal guards intact."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ap-parent';R=B/'fresh-arithmetic-discovery-r162ap';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ap-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'))
assert not git('diff','--cached','--name-only').strip();assert t['newAccepted']==19
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==741 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 raw=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(raw)==x['brief_sha256']
 ms={n:[z for z in rules(raw.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ao-brief.txt').read_bytes();assert sha(original)=='b44d2f0290b0c95912c7b99499c2948b94bd95a093b80d9672ccf64a1d29a756'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source112')]
prefix=prefix.replace('Arithmetic discovery r162ao — confirmed depth-three Boolean-circuit operative-proof discovery.','Arithmetic discovery r162ap — confirmed perfect-matching counting and entropy operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ao/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ap/.',1).replace('FRESH DISTINCT Source112','FRESH DISTINCT Source113',1).replace('Own r162ao I/O','Own r162ap I/O',1)
instructions='''Read the COMPLETE actual Source113 counting AND entropy proofs, all operative includes/appendices and strongest primary/companion mechanisms BEFORE selecting a new full theorem. BOTH supplied conclusions are ALREADY PAID: a fully polynomial randomized approximation scheme for perfect matchings in arbitrary finite simple undirected graphs, exact zero detection, relative error epsilon and failure delta in worst-case bit time polynomial in input length,epsilon^-1,log(delta^-1); and the complete entropy/face-dimension theorem for every feasible perfect-matching marginal vector in a loopless LABELLED multigraph on 2m>=2 vertices, INCLUDING boundary faces. The supplied entropy bound F(x)-(2-2/m)B(x)<=H(x)<=F(x) and sharp support/face bound |supp(x)|-dim(F_x)<=3m-2 are not nominees. Read and credit the actual stronger weighted,optimization,odd-cut,decomposition and precision operations; the catalogue headline is not their boundary. Upstream truth is stipulated; do not audit it.

Track graph/multigraph labels,loops and parallel edges,weights and zero support,feasible boundary versus interior marginals,dimension and equality cases,zero counts versus small counts,relative/absolute errors,failure probability and every quantifier; finite precision,explicit encodings,all randomness,preprocessing,oracle calls,output size and worst-case/expected bit time. Classical self-reducibility,approximate sampling,conditioning,replication,convex duality or already compatible weighted/face transfers do not count alone. Do not park a source-level theorem as an additional operation. Choose ONE viable direction from actual operative proofs and do sustained mathematics; freeze only a precise full theorem with a viable new mechanism,then prove its complete scope. Full statement,dependencies and exact primary comparisons must be reviewable. Parent alone requests independent correctness and substantial-contribution gates. No restricted/renamed substitute or desired-grade retry of an older full target.

R162AO is archived PREFREEZE/no nominee. Preserve its FULL unfrozen/unproved AC diagnostic:ONE language L* subset {0,1}*,ONE deterministic finite-alphabet Turing machine M,fixed positive integers C,a,EVERY n-bit input decided in C(n+1)^a elementary bit steps. For EVERY real A>0 there is N_A such that for EVERY n>=N_A EVERY nonuniform unbounded-fan-in OR-AND-OR circuit of TOTAL AND/OR gates<=2^(A sqrt(n)),INCLUDING bottom/output gates,has whole-uniform-cube TWO-SIDED error STRICTLY >1/3 against L*. L*,M,C,a precede A;N_A need not be effective. Arbitrary fan-out/sharing,free literal negations,optional constants/unary gates,NO width/wire/description/uniformity restriction. Membership has no advice,promise,randomness,preprocessing oracle or free field construction. No favorable distribution,slice,subsequence,one-sided/tiny-error/fixed-overlap replacement. Neither AC nor its negation proved;no freeze,grades/count.

Paid Source112/classical construction:explicit balanced field-tower full-input evaluator,JOINT random hash/coefficient/restriction event before fixing slices,all-input narrow-CNF correlations,global shared wide-clause truncation,exact/one-sided/fixed-overlap consequences,and adaptive subcube robustness. The source modulus-input evaluator has a particular reducible-modulus approximation with error1/4;this does not refute AC and the tower candidate avoids that sector. Unpaid for the pursued candidate:ONE joint SAME approximate-cover estimate E[g 1_(sum H_i>0)] with constant-error/truncation budgets,or another full AC construction. Inclusion-exclusion absolute mass2^S-1,first-violation growth,Bonferroni multiplicity remainder,an ABSTRACT positive-intersection moment example and common-switching residual logS are retained route limits,not AC impossibility or actual uniform-cube CNF counterexamples. Full eleven canonical texts were read;primary ancestry remains incomplete,no optional history traversal,late visual pages disclosed. Do not reopen AC or a weaker circuit target in this matching family.

'''
older=old[old.index('R162AN is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source113-selection.json').read_text())
assert sel['catalogue_extent']==[186982,189149] and len(sel['folders'])==2 and len(sel['entries'])==28
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==21
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162ao/private/MATH.md',B/'fresh-arithmetic-discovery-r162ao/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162ao/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162ao/private/FINAL.md']
inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[186982,189149),EXACT Source113. Parent used ONE bounded14000-byte window at186982,decoded ONLY FIRST TWO numeric-bold TITLE STRINGS113/114 and selected ONLY113 body. Source114 body and remainder window were not decoded. ONE new family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance.

Confirmed canonical folders and ACTUAL wrappers from the complete pinned tree:
'''
for folder in sel['folders']:
 section+=folder+'\n'
 wrapper=next(x for x in blobs if x['path']==folder+'/build/main.tex')
 section+=f"ACTUAL wrapper:{wrapper['path']} bytes{wrapper['size']};Git blob{wrapper['sha']}.\n"
section+='''There are21 blobs/28 entries including roots. Parent source-proof reading:NONE. Retrieve exact pinned raw paths and follow ACTUAL includes;do not guess root main.tex or build/latex/. Authenticate all selected objects and read BOTH complete operative proofs including appendices. Distinguish metadata/PDF authentication from semantic or rendered-page reading. The catalogue's lean/docs/113.md is a scoped comparator-navigation pointer only;inspect its actual scope privately without downstream formal work or inferring end-to-end formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''
section+='\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No permissions in older files propagate. They supply prior-scope/payment/reading-limit context ONLY,not this family's source proof reading. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query actual authored matching-counting,entropy,odd-cut,polytope,sampling and compatible optimization mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Source113 may overlap older mechanisms;actual comparison is required before any novelty claim.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ap* *arithmetic*r162ap*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ap*','*arithmetic*r162ap*','*structural*r220*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ap/.'
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=113,catalogue_extent=[186982,189149],canonical_folders=2,canonical_blobs=21,canonical_entries_including_roots=28,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source114_body_not_decoded=True,full_approximate_circuit_diagnostic_preserved=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=21,canonical_entries=28,all_guards_retained=True,distinct_family=True)))
