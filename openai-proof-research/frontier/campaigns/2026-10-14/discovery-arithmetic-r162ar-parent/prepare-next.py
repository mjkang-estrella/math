#!/usr/bin/env python3
"""Prepare Source118 research; all earlier scopes and literal guards retained."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162as-parent';R=B/'fresh-arithmetic-discovery-r162as';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162as-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'));assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==769 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 ms={n:[z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names};assert all(ms.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True);dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ar-brief.txt').read_bytes();assert sha(original)=='9ccde20d9982ea6debd1e24cb57872215505fc0b3a033b3ea657126529025cf4'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read ALL THREE COMPLETE actual Source116')].replace('Arithmetic discovery r162ar — confirmed noncommutative-identity-testing operative-proof discovery.','Arithmetic discovery r162as — confirmed bin-packing-configuration-gap operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ar/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162as/.',1).replace('FRESH DISTINCT Source116','FRESH DISTINCT Source118',1).replace('Own r162ar I/O','Own r162as I/O',1)
instructions='''Read the COMPLETE actual Source118 operative proof,all actual textual includes and strongest primary/companion interfaces BEFORE selecting a full additional theorem. The ENTIRE stipulated source theorem is ALREADY PAID:explicit rational bin-packing instances with UNBOUNDED additive gap between the integral optimum and the standard configuration-LP value;and for EVERY fixed nonnegative integer c,NP-hardness of distinguishing packability into B bins from need for MORE THAN B+c bins. BOTH hold with EVERY item STRICTLY >1/6,thus at most FIVE items per bin. Read the actual stronger instance/tree/interval/completeness/soundness/consequence machinery;the headline is not its boundary. Upstream proofs are stipulated TRUE;do not audit them or nominate their main theorem.

Track one full explicit model:item SIZE versus multiplicity,strict lower threshold,capacity normalization,rational bit lengths,configuration columns and downward closure,LP versus integer optimum,additive constants and asymptotic/instance-size rates,every B/c quantifier,promise and reduction cost. Distinguish explicit item lists from binary multiplicities,uniformity in fixed c,weak/strong hardness,constructibility,output size and all finite-bit operations. Padding,replication,rescaling,rounding,standard packing/covering transfers and compatible source/classical consequences do not count alone. Read actual primary mechanisms before choosing ONE viable direction and doing sustained mathematics. Freeze every hypothesis,quantifier,constant and conclusion only when a viable full additional operation emerges;prove its complete scope. Parent alone commissions independent correctness and substantial-contribution reviews. No restricted/renamed substitute or desired-grade retry of an older target.

R162AR is archived PREFREEZE/no nominee. No additional theorem OR diagnostic selected/frozen. The strongest retained source/classical comparison constructs ONE deterministic polynomial-BIT prime-field hitting LIST for promised binary prime p and unary n,s,with one common matrix dimension and full dense output cost. The SAME list works over EVERY coefficient extension of characteristic p,including2,for EVERY original size-s rational FORMULA TREE with a defined NONZERO evaluation over some extension;one tuple makes ALL original inverse occurrences defined and final output INVERTIBLE. No inverse-depth,coefficient-height/representation or existential witness-dimension bound;unknown-field evaluation is separate from constructor bit cost. This is not an independent correctness PASS or substantial-contribution nominee.

Complete Newton flags/folded-determinant root budgets,source reversal for ALL Laurent subspaces,coprime division lift,original inverse certificates,small-field-only explicit extension search,and ONE simultaneous bad-point count over ALL Frobenius/root components pay the combination. Nonzero nilpotent descent is not invertibility;one good component is insufficient;singleton universal definedness fails at an eigenvalue inverse. These are compatibility checks,not hitting-list counterexamples or nominees. No shared-circuit,optimal-dimension,singleton-domain or parallel-complexity target was selected. All27 canonical texts read completely;primary ancestry incomplete,late recovery/visual pages disclosed,no optional history traversal. Completed notification additionally reports400 bounded integer-parameter sanity checks AFTER the reading-limit draft;no full generator was executed. Treat them only as finite sanity checks,not proof evidence. All earlier full scopes/dispositions remain unchanged and are not reopened.

'''
older=old[old.index('R162AQ is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source118-selection.json').read_text());assert sel['catalogue_extent']==[197114,198360] and len(sel['folders'])==1 and len(sel['entries'])==16
blobs=[x for x in sel['entries'] if x['type']=='blob'];assert len(blobs)==12
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162ar/private/MATH.md',B/'fresh-arithmetic-discovery-r162ar/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162ar/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162ar/private/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[197114,198360),EXACT Source118. Parent used ONE bounded14000-byte window at195501,decoded ONLY FIRST TWO numeric-bold TITLE STRINGS117/118,and selected ONLY118 body. Source117 TITLE was skipped from prior USER status-answer context recording R038's accepted Source117 metric work;NO117 catalogue body or new protected history was read. Heading119 supplied ONLY a byte boundary;no119 title/body decode. ONE new family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor inventory or old scan replay. Bounded navigation is not exhaustive clearance.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''
for folder in sel['folders']:
 w=next(x for x in blobs if x['path']==folder+'/build/source/main.tex');section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='''There are12 blobs/16 entries including root. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow ACTUAL includes under build/source/;do not guess root main.tex,build/main.tex or build/latex/. Authenticate selected objects and read every operative proof/include and relied-upon dependency. Distinguish metadata/PDF authentication from semantic/rendered reading. lean/docs/118.md is scoped comparator navigation only;inspect actual scope privately without downstream formal work or end-to-end formalization inference.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proofs. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts stay only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored bin-packing,configuration-LP,rounding,covering,interval/hypergraph and approximation mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ar* *arithmetic*r162as*\n\n';brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ar*','*arithmetic*r162as*','*structural*r220*'}<=rules(brief.decode());assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162as/.';BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=118,catalogue_extent=[197114,198360],canonical_folders=1,canonical_blobs=12,canonical_entries_including_roots=16,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source117_body_not_decoded=True,heading119_byte_boundary_only=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=12,canonical_entries=16,all_guards_retained=True,distinct_family=True)))
