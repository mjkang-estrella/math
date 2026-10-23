#!/usr/bin/env python3
"""Prepare one new isolated hyperbolicity research brief, without dispatch."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
N = B / 'discovery-arithmetic-r162ac-parent'
R = B / 'fresh-arithmetic-discovery-r162ac'
BP = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162ac-brief.txt'
def sha(b):
    return hashlib.sha256(b).hexdigest()
def dump(p, x):
    p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t = subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
assert (B / 'tasks.json').read_bytes() == raw_t
tasks = json.loads(raw_t)['tasks']
own = next(i for i,t in enumerate(tasks) if t.get('clientRequestId') == 'twenty-20261023-fresh-arithmetic-r162ab-codex-astra-r1')
names = [p.relative_to(P).as_posix() for p in [N,R,BP]]
checks = []; legacy = []
for i,t in enumerate(tasks):
    if i == own or t.get('status') not in {'running','queued','waiting'}:
        continue
    if 'brief' not in t:
        assert 'nativeTaskName' in t and 'taskId' not in t
        legacy.append(i); continue
    raw = (P / t['brief']).read_bytes()
    patterns = [g for g in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if g not in {'*','**'}]
    matches = {n:[g for g in patterns if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()), (i,matches)
    checks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
guard = dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,legacy_limit='Historical native entries were not queried or reopened; committed native_live is empty, not a fresh liveness claim.',foreign_live_queries=False)
dump(D / 'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir(); R.mkdir(); (N / 'private').mkdir()
dump(N / 'prospective-isolation.json',guard)

raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162ab-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = raw.split(marker,1)[1]
assert len(standing) == 5570
old = raw.decode()
prefix = old[:old.index('Catalogue access,if needed:')]
prefix = prefix.replace('Arithmetic discovery r162ab — confirmed subgaussian log-Sobolev operative-proof discovery.','Arithmetic discovery r162ac — confirmed hyperbolicity-cone operative-proof discovery.')
prefix = prefix.replace('fresh-arithmetic-discovery-r162ab/','fresh-arithmetic-discovery-r162ac/').replace('Own r162ab is excluded','Own r162ac is excluded')
prefix = prefix.replace('ONE distinct Source093 family with ONE confirmed canonical manuscript','ONE distinct Source095 family with THREE confirmed canonical companions')
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
previous = '''Arithmetic162ab is CLOSED PREFREEZE/no nominee, with no frozen theorem or gate. Preserve its FULL complete MODIFIED logarithmic Sobolev diagnostic: ONE universal C,EVERY n,m>=1,a>0,EVERY centered log-concave Lebesgue probability with sup_unit_theta E exp(<X,theta>^2/a^2)<=2,and EVERY positive-semidefinite complex m-by-m field F with finite integral trace in the specified relaxed finite-energy domain,satisfy H_mu(F)<=C a^2 I_mu^rel(F). H is unnormalized matrix conditional entropy; I is the FULL logarithm-divided-difference/BKM gradient energy,NOT square-root Hilbert-Schmidt energy. The exact rough domain relaxes smooth bounded uniformly positive fields constant outside compact sets in L1 trace norm,without a common spectral floor,condition-number,support or regularity restriction across the sequence. Scalar source,common fixed-basis fields,complete curvature/tensorization at actual hypotheses,spectral-window comparisons,trace/quantum splitting and whole-scale Gaussian observation ENERGY are PAID. That observation leaves a POSITIVE mixture-relative-entropy term;a smooth constant-trace comparison defeats uniform entropy recovery by this channel. The stronger anisotropic product spends the original entropy again. An actual tensor-covariance example defeats naive rank-one finite-copy transplantation;none refutes the diagnostic. Exact SAME-posterior localization pays terminal entropy <=a^2 I/2. Remaining is ONE bound E integral_0^{a^-2} sum_i gamma_(A_t)(D_i(t))dt <=C0 a^2 I_mu(F),uniformly for ALL full inputs,with Y_t=tX+B_t,A_t=E[F|full observations],D_i=E[(X_i-posterior mean_i)F|same observations]. This residual and complete semigroup entropy half-life are equivalent core formulations up to constants;the full nonsmooth-law/rough-field transfer is paid conditional on that bound. The stronger published curvature-free CP return-time criterion is credited;its infinite Gaussian return time is a method limit,not a counterexample. No fixed-m,commuting,strong-curvature,bounded-support or favorable-posterior substitute. Canonical reading complete,transitive primary reading incomplete;possible tree-signing assembly derivative admission,coarse omissions,recovered seams and late narrow i120/i123 reads are disclosed. Oldr142 and all previous scopes/dispositions remain immutable.

'''
direct = [D/'assessment.md',B/'fresh-arithmetic-discovery-r162ab/FINAL.md',B/'fresh-arithmetic-discovery-r162ab/packet/private/prefreeze-mathematics.md',B/'fresh-arithmetic-discovery-r162ab/packet/private/primary-understanding.md',B/'fresh-arithmetic-discovery-r162ab/packet/private/READING-LIMITS.md']
records = []
for p in direct:
    data=p.read_bytes();records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(data),mode=p.stat().st_mode,sha256=sha(data)))
dump(N/'private/completed-direct-inputs.json',records)
selected=json.loads((D/'private/intake/Source095-selection.json').read_text())
assert len(selected['folders'])==3 and len(selected['entries'])==43
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==33
wrappers=[]
for folder in selected['folders']:
    possible=[x for x in blobs if x['path'] in {folder+'/build/main.tex',folder+'/build/source/main.tex'}]
    assert len(possible)==1;wrappers.append(possible[0])
section='''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[157398,159594),EXACT Source095 body. Parent decoded only the FIRST TWO numeric-bold title strings from ONE bounded14000-byte window starting156394,then selected ONLY095 body as a distinct family. Source094's body was NOT decoded or selected. No child title locator,extra family,catalogue screen,ancestor hunt or whole-catalogue opening/decoding. THREE confirmed folders have33 blobs/43 complete-tree entries including roots. The nonliftability wrapper is build/source/main.tex; the other two wrappers are build/main.tex. Parent source-body reading:NONE. Metadata is navigation,not a theorem/proof interface.

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
'''+ '\n'.join(p.relative_to(B).as_posix() for p in direct)+'''
These exact exceptions never authorize containing namespaces,links,other copied/source bundles,role/brief/status/activity aliases or peer findings. Protected completed bodies AND named metadata remain PRIVATE/local under original rights;any copies stay inside your own root. No old r105,r35,R041,weighted Brunn-Minkowski or any prior exact-body exception propagates. Do not repeat or broaden an old scan.

Your ONE developed family is SOURCE095: HYPERBOLICITY CONES,EXACT SEMIDEFINITE REPRESENTATION AND NONLIFTABILITY. All THREE pinned manuscripts AND ALL operative proofs are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and new deductions,not upstream truth.

Confirmed canonical folders and actual wrapper metadata:
'''
for folder,w in zip(selected['folders'],wrappers):
    section+=folder+'\n'+w['path']+f"\nbytes {w['size']}; Git blob {w['sha']}.\n"
section+='''
Authenticate ALL33 canonical blobs against complete-tree size/Git blob/SHA256,including READMEs,compiled PDFs,figures,references,wrappers and every local object. Read ALL THREE COMPLETE actual theorem/proof bodies and EVERY nested operative include,required companions,strongest relevant ACTUAL primary mechanisms and eligible ORIGINAL-history sections BEFORE extended deductions or author drafting. Follow actual include paths rather than conventions; the strongest nonliftability proof is under build/source/. Read the actual obstruction and separation proof,not just the headlines or a certificate summary. Distinguish semantic proof reading from duplicate PDF/typography/ancillary authentication. Do not rerun source certificates/code to audit stipulated truth. Recover clipped seams;record durable mathematical understanding,exact labels,primary versions/URLs/read extents,access failures and unread ancestry. Mathematics must dominate proportionate evidence work.

The ENTIRE strongest headline is PAID: some CLOSED hyperbolicity cones admit NO exact finite affine semidefinite lift,even with arbitrary real coefficients and ANY finite number of auxiliary variables. This already disproves Projected Lax and hence the generalized Lax assertion. It is not enough to rule out a pencil in the original coordinates,a fixed lift size,rational coefficients or one proposed lift family. Do not nominate another restatement,a mere direct product/section of the same example,or an existential finite-encoding variant already supplied by the actual proof.

The TWO companion results are ALSO PAID and must be distinguished from the stronger example: the explicit degree16,23-variable cone has NO homogeneous real symmetric LMI in its original coordinates,BUT the exact-lift companion supplies a size100 homogeneous real symmetric pencil with307 auxiliary variables representing its ENTIRE CLOSED cone,INCLUDING every singular-X boundary point. Those lift sizes are not claimed minimal. There is no contradiction between non-spectrahedrality and admitting a lift. Do not re-offer that particular cone as nonliftable,ignore its companion,restrict the lift to positive-definite X,or call its already-paid singular-boundary assembly new.

Read ALL stronger proof operations and exact polynomial,cone,basepoint,closure,rank and real-coefficient hypotheses before using the headlines. Their cone/Hankel,separator,obstruction,tangent,norm,angular,slice,matching and boundary mechanisms are paid WHERE ACTUALLY PROVED; section names are not semantic reading. Inspect strongest actual primary hyperbolicity,semialgebraic/semidefinite-lift obstruction,positivity and conic-duality proofs whenever invoked,not abstracts or another ledger. Classical affine/linear changes,direct products,exposed faces,sections,preimages,linear images,duality,homogenization,realification and SOS/Gram reformulations are PAID when ALL closure/feasibility/coefficient hypotheses and budgets match. A failed naive pencil or Schur complement does not show the strongest compatible source/classical operation fails.

Track one polynomial versus its cone,choice of hyperbolicity direction,entire closed cone versus interior or selected rank stratum,homogeneous versus affine lifts,real symmetric versus complex Hermitian representations,arbitrary real coefficients versus rational descriptions,original variables versus auxiliary projections,and exact representations versus approximation. Keep the SAME witness polynomial,linear slice/projective map,positivity domain,slack/separation functional,rank/degree/size budget and boundary convention across every transfer. A dual or projected spectrahedral image need not be closed without the proper interface. A generic positive-definite calculation does not prove the full singular boundary,while a source proof already paying that interface must be credited. An existence or no-lift theorem does not silently supply a polynomial-time bit algorithm,robust approximation lower bound,minimal degree/dimension or quantitative neighborhood obstruction.

A distinct quantitative,relative,coherent-family,algorithmic,hypothesis-removal or structural operation is eligible only after a CLOSED identifiable nonroutine step survives the strongest compatible source/primary reduction. Optimized classical constants,metadata,finite numerics,equivalent formulations and difficult unproved conjectures are not findings. Preserve every old frozen/PREFREEZE target and closed disposition. On overlap read eligible ACTUAL original-history mechanisms under the prospective guards;exact completed exceptions never open linked protected namespaces.

After complete operative reading choose and develop ONE distinct fully specified full-scope operation with sustained CONCRETE mathematics beyond a first failed shortcut. Try the strongest integrated source/primary payment before naming a bridge unpaid. Keep actual polynomials,cones,common witnesses,parameters,degree/rank/size/entropy budgets and ALL compatibility interfaces. Freeze a viable exact theorem BEFORE author-proof development,then close every quantifier/constant/interface. If nothing closes,honest PREFREEZE/no nominee with exact gaps;no weaker substitute,self-grade,count,exhaustive clearance,global impossibility or worldwide-priority claim.

Keep ALL source/primary/history/search/extract/render/copied bodies AND named metadata PRIVATE/local under original rights. Prospectively serialize EVERY literal wildcard/substring rule below before optional filename traversal/body selection beyond narrow exceptions,retaining r/no-r,flat/compound/role aliases. At most ONE correctly pruned original-history traversal with no size/extension cutoff on eligible authored UTF8 after pruning;no projectwide rg-then-filter,broad untracked inventory or old scan rerun. Disclose false admissions,coarse omissions,versions/read extents,truncation recovery,late reads and incomplete transitive ancestry. Seal YOUR own fresh exact selection ONCE with detached FINAL/MANIFEST/outside REPORT anchors,a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over fewer files. Artifact checks are not math gates. No nested agents,shared/git writes,public/browser actions or downstream formal/manuscript/release work. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews of a viable full author proof.

'''
extra='\nFurther prospective literal twins and opaque derivative alias:\n*arithmetic*162ac* *arithmetic*r162ac* *tree-signing-assembly*\n\n'
brief=(prefix+previous+section+isolation+extra+marker.decode()).encode()+standing
patterns=lambda s:{g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
assert patterns(old)<=patterns(brief.decode())
assert brief.split(marker,1)[1]==standing
BP.write_bytes(brief)
dump(N/'private/canonical-selection.json',selected)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,source='095',catalogue_extent=[157398,159594],source094_body_not_selected=True,canonical_blobs=33,canonical_entries_including_roots=43,completed_direct_inputs=5,parent_source_body_read=False,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=33)))
