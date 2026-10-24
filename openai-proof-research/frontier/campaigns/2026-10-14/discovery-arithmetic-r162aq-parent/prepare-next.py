#!/usr/bin/env python3
"""Prepare Source116 research; all earlier scopes and literal guards retained."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ar-parent';R=B/'fresh-arithmetic-discovery-r162ar';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ar-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'));assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==768 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True);dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162aq-brief.txt').read_bytes();assert sha(original)=='3635fca4a73ae5e8e165258bdd7de79eab32f1b0ececfaf3b9361afc36e40851'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read BOTH COMPLETE actual Source114')].replace('Arithmetic discovery r162aq — confirmed common-integer-polymatroid-base operative-proof discovery.','Arithmetic discovery r162ar — confirmed noncommutative-identity-testing operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aq/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ar/.',1).replace('FRESH DISTINCT Source114','FRESH DISTINCT Source116',1).replace('Own r162aq I/O','Own r162ar I/O',1)
instructions='''Read ALL THREE COMPLETE actual Source116 operative proofs,all textual includes/appendices and strongest primary/companion interfaces BEFORE selecting an additional full theorem. All supplied hitting results are ALREADY PAID:ONE deterministic polynomial-BIT constructor for promised prime p in BINARY and n,s in unary producing a SINGLE tuple over F_p of dimension O(n^3 s^6) hitting EVERY nonzero size-s division-free noncommutative formula over EVERY coefficient field of that characteristic,including arbitrary extension coefficients and characteristic2,plus the actual acyclic path-program scope;the SINGLE rational tuple dimension O(ns^2) for division-free formulas over EVERY characteristic-zero field;and polynomial-size rational-matrix hitting LISTS for admissible noncommutative RATIONAL formulas over Q of bounded TREE size,with a defined INVERTIBLE value at some tuple and NO separate inverse-depth or rational-constant-height bound. Every matrix dimension,entry bit length,total output length and constructor cost is charged. Read actual hypotheses and stronger internal operations;the catalogue is not their boundary. Upstream truth is stipulated;do not audit it.

Keep exact formula/circuit/ABP/tree-size models,degree,size,number of variables,coefficient field,characteristic/admissibility/domain,zero versus nonzero/invertible evaluation,one tuple versus a list,uniformity and construction/evaluation costs. Track binary/unary encodings,prime promise,extension-field representation,coefficient heights,inverse nesting,all scalar/bit operations,output length,preprocessing and advice. Direct block sums,field embeddings,linearization,rank reductions,standard substitutions and compatible source/classical consequences do not count alone. Read actual primary mechanisms before choosing ONE viable direction and doing sustained mathematics. Freeze a precise full theorem only when a viable additional mechanism emerges;prove every quantifier. Parent alone commissions independent correctness and substantial-contribution reviews. No restricted/renamed substitute or desired-grade retry of an older full target.

R162AQ is archived PREFREEZE/no nominee. No additional theorem OR diagnostic was selected/frozen. The fully charged compatible reduction already supplies EXACT uniform common INTEGER-base sampling for two deterministic exact rank-value-oracle polymatroids of equal binary total rank/capacities,each vector once,exact emptiness,boundary/trivial cases,and EXPECTED polynomial oracle AND outside-oracle bit cost. Query/answer encodings,all randomness,preprocessing and explicit output are paid;oracle promises are not claimed efficiently validated. Prefix boxes become capped/translated submodular ranks;fixed-base median supports are precision-independent;SAME sampled estimator values determine proposal/rejection products;aggregate law tabulation is2^poly(L)poly(k),and known rare residual correction pays exactness. This is source/classical composition,not a nominee.

The specified exhaustive correction lacks a polynomial-in-log-tail guarantee on a rank-one family;this refutes THAT implementation,not another algorithm. Fastest-copy stopping can bias output. No full exact-tail diagnostic was selected/frozen. Root-direction log-concavity and TU central-box midpoint arguments leave a four-family polymatroid intersection interface unpaid;finite probes prove neither a universal joint-displacement inequality nor its negation. No enlarged-chain/repair theorem was established. Both canonical proofs AND both cell-bounded/exact ordinary-table operative companions were fully read and paid,including finite bounded directed-flow counting and stronger ordinary-table repair/aggregate-law operations. Primary ancestry incomplete;older/newer versions,recoveries and late visual pages disclosed,no optional original-history traversal. All E3,AC and older full targets/dispositions remain unchanged and are not reopened.

'''
older=old[old.index('R162AP is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source116-selection.json').read_text());assert sel['catalogue_extent']==[192843,195501] and len(sel['folders'])==3 and len(sel['entries'])==40
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==30
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162aq/private/MATH.md',B/'fresh-arithmetic-discovery-r162aq/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162aq/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162aq/private/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[192843,195501),EXACT Source116. Parent used ONE bounded14000-byte window at191164,decoded ONLY FIRST TWO numeric-bold TITLE STRINGS115/116,and selected ONLY116 body. Source115 TITLE was skipped because this completed r162aq packet fully read and paid its cell-bounded/exact ordinary-table operative companions. NO Source115 catalogue body was decoded. Heading117 supplied ONLY the byte boundary;no117 title/body decode. ONE new family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
'''
for folder in sel['folders']:
 ws=[x for x in blobs if x['path'] in [folder+'/build/main.tex',folder+'/build/paper.tex']];assert len(ws)==1;w=ws[0];section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='''There are30 blobs/40 entries including roots. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow ACTUAL includes;do not guess root main.tex or build/latex/. In particular the characteristic-zero paper uses build/paper.tex. Authenticate selected objects,read all THREE complete operative proofs and every relied-upon dependency. Distinguish metadata/PDF authentication from semantic/rendered reading. lean/docs/116.md is scoped comparator navigation only;inspect actual scope privately without downstream formal work or end-to-end formalization inference.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proofs. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored noncommutative identity,formula/rational evaluation,hitting-point,rank and field-construction mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ar* *arithmetic*r162ar*\n\n';brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ar*','*arithmetic*r162ar*','*structural*r220*'}<=rules(brief.decode());assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ar/.';BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=116,catalogue_extent=[192843,195501],canonical_folders=3,canonical_blobs=30,canonical_entries_including_roots=40,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source115_body_not_decoded=True,heading117_byte_boundary_only=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=30,canonical_entries=40,all_guards_retained=True,distinct_family=True)))
