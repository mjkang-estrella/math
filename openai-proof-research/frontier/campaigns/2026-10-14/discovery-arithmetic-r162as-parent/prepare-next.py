#!/usr/bin/env python3
"""Prepare Source120 research; all earlier scopes and literal guards retained."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162at-parent';R=B/'fresh-arithmetic-discovery-r162at';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162at-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'));assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==771 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True);dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162as-brief.txt').read_bytes();assert sha(original)=='bb5fbcad47ce356e1a0bb4c98efeb4d67c44ec08b8b345b3a0bc59b1e57c0ea1'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source118')].replace('Arithmetic discovery r162as — confirmed bin-packing-configuration-gap operative-proof discovery.','Arithmetic discovery r162at — confirmed almost-linear-exact-matching operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162as/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162at/.',1).replace('FRESH DISTINCT Source118','FRESH DISTINCT Source120',1).replace('Own r162as I/O','Own r162at I/O',1)
instructions='''Read the COMPLETE actual Source120 operative proof,all actual includes and strongest primary/companion interfaces BEFORE selecting a full additional theorem. The ENTIRE stipulated source theorem is ALREADY PAID:ONE uniform randomized algorithm on EVERY simple undirected graph producing an EXPLICIT EXACT MAXIMUM-CARDINALITY matching in(n+m)^(1+o(1)) logarithmic-WORD time,with success probability>=2/3,and the running-time bound on EVERY computation path. The prescribed-admissible-degree f-factor reduction,existence decision AND explicit construction with the SAME asymptotic time/probability are also paid. Read every stronger actual matching-state,projection,routing/backend,update,uniformization and f-factor interface;the catalogue headline is not their boundary. Upstream operative proofs are stipulated TRUE;do not audit or nominate the main theorem. Exact maximum-cardinality matching here does NOT by itself assert the separate prescribed-red-edge Exact Matching problem.

Retain one uniform graph/input/output model,word size,randomness,success/failure conventions,all paths versus expected time,matching feasibility versus optimality,zero/empty and degree-boundary cases,construction versus decision,preprocessing,auxiliary graph blowup,all calls,space,bit/word conversions,updates and explicit output. Weighted,capacitated,multigraph,dynamic,certifying or deterministic variants require their actual additional compatible argument;standard reductions,probability amplification,verification or source/classical compositions do not count alone. Read actual primary mechanisms,choose ONE viable direction,do sustained mathematics,and freeze a precise full theorem only when a viable additional operation emerges. Prove every quantifier and total cost. Parent alone commissions independent correctness and substantial-contribution reviews. No restricted/renamed substitute or desired-grade retry of an older target.

R162AS is archived PREFREEZE/no nominee. No additional theorem OR diagnostic selected/frozen. The strongest retained source-compatible comparison gives EVERY fixed integer c>=0,fixed rho>0,EVERY explicit simple graph m>=1 and0<=k<=n,a list of4B rational items STRICTLY>1/5,B-bin completeness from a k-cover,and extraction of a(k+rho*n)-cover from EVERY packing into<=B+c bins. Both full numerical-type and individual-copy configuration LPs equal B on K4,k=2,rho=1/8;the source perfect-completeness reduction gives fixed-c additive NP-hardness. All physical copies,downward closure,numerical collisions,explicit denominators and fixed-parameter polynomial bit/extraction costs are charged. No varying-c polynomial,binary-multiplicity,strong-hardness or three-item theorem is asserted. No independent correctness/contribution review or grade.

Seven post-flag count equations allow FIVE zero-primary patterns. Deleting flags alone fails;relocating NONROOT plus-tree cells by3/4 with roots/jobs fixed excludes the extra GOOD T+YWDG pattern with margin>1/8. The complete source score/prefix/displaced-row/earlier-edge resource proof and pooled-copy fractional witness then pay the four-item comparison. The source leaf recurrence2(4^N-1)/3 yields only a log-star output-length gap along the K4 sequence by direct parameter accounting. Further U/D prepairing fixes labels on pooled tokens;dropping local labels loses vertex quotas;alternative anchor classes lack a common-inventory sorted-deadline proof. These are specific route limits,not impossibility or a selected three-item/rate/strong-hardness diagnostic. Eleven canonical texts read completely;primary ancestry incomplete,late/version/access/recovery limits disclosed,no optional history traversal.715 subclass and10 recurrence finite checks are not proof gates;no full source-size generator executed. All earlier full scopes/dispositions remain unchanged and are not reopened.

'''
older=old[old.index('R162AR is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source120-selection.json').read_text());assert sel['catalogue_extent']==[200390,201658] and len(sel['folders'])==1 and len(sel['entries'])==22
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==18
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162as/private/MATH.md',B/'fresh-arithmetic-discovery-r162as/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162as/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162as/private/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[200390,201658),EXACT Source120. Parent FIRST used a bounded14000-byte window at198360,decoded ONLY numeric-bold TITLE STRINGS119/120,and read119 body[198360,200390). It then rejected that family using prior accepted R020/R022 binary-information STATUS context;NO new protected history/source proof was read. This is a family-selection choice,not a claim all binary-information extensions are solved. SECOND bounded14000-byte window at200390 selected ONLY120 body,with NO additional title decode. Heading121 supplied ONLY a byte boundary;no121 title/body decode. TWO family bodies screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(x for x in blobs if x['path']==folder+'/build/main.tex');section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='''There are18 blobs/22 entries including root. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow ACTUAL includes under build/;do not guess root main.tex,build/source/ or build/latex/. Authenticate selected objects,read every operative section/figure/bibliography and relied-upon dependency. No Lean pointer occurs in this selected catalogue entry;do not invent formal support. Distinguish metadata/PDF authentication from semantic/rendered reading.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proofs. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored matching,f-factor,augmenting-path,projection,routing,graph algorithm and uniformization mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ar* *arithmetic*r162at*\n\n';brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ar*','*arithmetic*r162at*','*structural*r220*'}<=rules(brief.decode());assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162at/.';BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=120,catalogue_extent=[200390,201658],canonical_folders=1,canonical_blobs=18,canonical_entries_including_roots=22,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=2,source119_body_screened_then_rejected=True,heading121_byte_boundary_only=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=18,canonical_entries=22,all_guards_retained=True,distinct_family=True)))
