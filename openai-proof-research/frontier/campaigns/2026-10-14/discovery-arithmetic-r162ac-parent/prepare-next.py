#!/usr/bin/env python3
"""Prepare one new isolated Steinitz research brief, without dispatch."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
N = B / 'discovery-arithmetic-r162ad-parent'
R = B / 'fresh-arithmetic-discovery-r162ad'
BP = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162ad-brief.txt'
def sha(b):
    return hashlib.sha256(b).hexdigest()
def dump(p, x):
    p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t = subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
assert (B / 'tasks.json').read_bytes() == raw_t
tasks = json.loads(raw_t)['tasks']
own = next(i for i,t in enumerate(tasks) if t.get('clientRequestId') == 'twenty-20261023-fresh-arithmetic-r162ac-codex-astra-r1')
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

raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162ac-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = raw.split(marker,1)[1]
assert len(standing) == 5570
old = raw.decode()
prefix = old[:old.index('Catalogue access,if needed:')]
prefix = prefix.replace('Arithmetic discovery r162ac — confirmed hyperbolicity-cone operative-proof discovery.','Arithmetic discovery r162ad — confirmed Euclidean-Steinitz operative-proof discovery.')
prefix = prefix.replace('fresh-arithmetic-discovery-r162ac/','fresh-arithmetic-discovery-r162ad/').replace('Own r162ac is excluded','Own r162ad is excluded')
prefix = prefix.replace('ONE distinct Source095 family with THREE confirmed canonical companions','ONE distinct Source097 family with ONE confirmed canonical manuscript')
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
previous = 'Arithmetic162ac is CLOSED PREFREEZE/no nominee,with no frozen theorem or gate. Preserve the FULL D33 diagnostic: ONE integer M bounds exact real symmetric AFFINE semidefinite lift size for EVERY real PSD-valued homogeneous Q:R3->Sym3 and its SAME source degree20 polynomial p_Q(X,Z,y)=det((det X)Z-Phi_(Q,y)(adj X)),direction e=(I4,I4,0),ENTIRE CLOSED23-coordinate cone K_Q. Phi_(Q,y)([[a,v^T],[v,T]])=[[tr(Q(y)T),-v^TQ(y)],[-Q(y)v,aQ(y)]]. Include zero maps,kernels,rank changes,singular X,arbitrary real coefficients and nonlinear dependence of each pencil on Q;no joint coefficient-affine pencil,bit algorithm,rationality,approximation,minimality or favorable orbit. Auxiliaries compress to <=M(M+1)/2. Neither D33 nor its negation is proved. Strongest source nonliftability and the particular size100/307-auxiliary entire-closed Choi-Lam lift are PAID. SAME-X,y addition plus attained SOS removal reduces D33 up to40 to ALL weak-extremal(3,3)biforms,not one Choi orbit. Actual binary factorization supplies four real linear columns even at singular restrictions. Nuclear/operator-norm duality plus separation supplies ONE contraction matching BOTH angular coefficients for every indefinite S,z;three zero columns give fixed Gram at every angle. Pointwise matching and bounded semialgebraic choices are PAID. Conditional assembly from ONE common function space V_Q of dimension<=d gives a size32d moment pencil,testing EVERY feasible functional directly;D=t vv^T recovers kernel-range and D=X-dagger gives singular Schur. The sufficient unpaid J33 bridge is ONE uniformly bounded-dimensional space for EVERY test S,z with SAME Q and SAME factors,independent of rank/output data. Bounded algebraic complexity does not give finite linear span;denominator clearing changes output moments,and atomic representations do not control every feasible functional. Another common slack/pullback construction could bypass J33;it is not claimed necessary. Stronger primary common-cover/infinitesimal finite-jet obstruction read late was credited,but no compatible same23-coordinate witness or uniform common cover was obtained. No restricted substitute,counterexample,exhaustion or global-impossibility claim. Full I198 approximation-rate and I200 small-positive-regularization targets remain unchanged. Canonical reading is complete,primary/transitive incomplete. The full eligible I198 iteration report was accidentally decoded/copied,exposing unrelated Source100/210 summaries;these were not used,developed or followed. Coarse omissions,false hits,recovered primary seams and late readings are disclosed. All earlier scopes/dispositions remain immutable.\n\n'
direct = [D/'assessment.md',B/'fresh-arithmetic-discovery-r162ac/FINAL.md',B/'fresh-arithmetic-discovery-r162ac/packet/private/prefreeze-mathematics.md',B/'fresh-arithmetic-discovery-r162ac/packet/private/primary-understanding.md',B/'fresh-arithmetic-discovery-r162ac/packet/private/READING-LIMITS.md']
records = []
for p in direct:
    data=p.read_bytes();records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(data),mode=p.stat().st_mode,sha256=sha(data)))
dump(N/'private/completed-direct-inputs.json',records)
selected=json.loads((D/'private/intake/Source097-selection.json').read_text())
assert len(selected['folders'])==1 and len(selected['entries'])==13
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==11
wrappers=[]
for folder in selected['folders']:
    possible=[x for x in blobs if x['path'] in {folder+'/build/main.tex',folder+'/build/source/main.tex'}]
    assert len(possible)==1;wrappers.append(possible[0])
section="Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[160713,161938),EXACT Source097 body. Parent decoded only the FIRST TWO numeric-bold title strings from ONE bounded14000-byte window starting159594,then selected ONLY097 body as a distinct family. Source096's body was NOT decoded or selected. No child title locator,extra family,catalogue screen,ancestor hunt or whole-catalogue opening/decoding. ONE confirmed folder has11 blobs/13 complete-tree entries including roots;actual wrapper build/main.tex. Parent source-body reading:NONE. Metadata is navigation,not a theorem/proof interface.\n\nRead these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:\n"+'\n'.join(p.relative_to(B).as_posix() for p in direct)+'\nThese exact exceptions never authorize containing namespaces,links,other copied/source bundles,role/brief/status/activity aliases or peer findings. Protected completed bodies AND named metadata remain PRIVATE/local under original rights;any copies stay inside your own root. No old I198,I200,r105,r35,R041,weighted Brunn-Minkowski or any prior exact-body exception propagates. Do not repeat or broaden an old scan.\n\nYour ONE developed family is SOURCE097: EUCLIDEAN STEINITZ-BERGSTROM VECTOR SIGNING AND REARRANGEMENT. The pinned manuscript AND ALL operative proofs are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and new deductions,not upstream truth.\n\nConfirmed canonical folder and actual wrapper metadata:\n'
for folder,w in zip(selected['folders'],wrappers):
    section+=folder+'\n'+w['path']+f"\nbytes {w['size']}; Git blob {w['sha']}.\n"
section+='\nAuthenticate ALL11 canonical blobs against complete-tree size/Git blob/SHA256,including README,compiled PDF,reference file,wrapper and every local object. Read the COMPLETE actual theorem/proof body and EVERY nested operative include,required companions,strongest relevant ACTUAL primary mechanisms and eligible ORIGINAL-history sections BEFORE extended deductions or author drafting. Read all actual signing,matrix,Brownian,survival,assembly and consequence bodies,not just the headline or a consequence list. Follow actual include paths rather than filename conventions. Distinguish semantic proof reading from duplicate PDF/typography/ancillary authentication. Do not rerun source code to audit stipulated truth. Recover clipped seams;record durable mathematical understanding,exact labels,primary versions/URLs/read extents,access failures and unread ancestry. Mathematics must dominate proportionate evidence work.\n\nThe ENTIRE strongest headline is PAID: EVERY prescribed-order finite sequence of Euclidean unit-ball vectors in R^d admits ONE signing for which EVERY signed prefix has norm <=C sqrt(d),with C absolute and independent of length. The consequent reordering of EVERY indexed zero-sum unit-ball family gives the SAME order for EVERY unsigned partial sum. The matching lower order S2(d)=Theta(sqrt(d)) is also PAID. Do not offer the prescribed-order signing theorem as an enhancement over reordering,replace zero sum by a source-paid centering argument,or nominate another restatement,equivalent normalization,fixed dimension or direct specialization.\n\nRead actual dimension ranges,constants,rounding/fractional-sign hypotheses,probability events and stronger operative conclusions before using the headline. All standalone source signing,matrix,Brownian,survival,assembly and consequence operations are PAID WHERE ACTUALLY PROVED;section filenames are not semantic reading. Inspect strongest actual primary vector balancing,Steinitz,discrepancy,rounding and geometric-rearrangement proofs whenever invoked,not abstracts or another ledger. Compatible affine/isometric changes,direct sums,centering,transference,rounding,block or dyadic decomposition and tensor/product operations are PAID when their exact hypotheses and common budgets match. A failed naive greedy/Brownian/union-bound argument does not show the strongest compatible source/classical composition fails.\n\nTrack prescribed order versus a freely chosen permutation,signing versus rounding/fractional controls,zero-sum indexed families versus arbitrary endpoints,one common signing versus independently chosen prefixes,finite dimension versus infinite-dimensional Hilbert settings,and Euclidean norm versus other Banach/matrix norms. Keep the SAME vector family,order,index multiplicities,signs/permutation,endpoint constraints,subspace projections,covariance/energy budget and ALL prefix events throughout transfers. An offline existence theorem does not automatically supply an online/adapted rule,efficient algorithm,finite-bit oracle guarantee,coherent infinite signing or common choice for multiple norms/flags. Conversely,any such stronger operation actually proved in the source must be credited. Operator norm,matrix-valued order,all stopping times or multiple simultaneous observables need their own full common-witness compatibility proof;separate winners cannot be combined without paying their interaction.\n\nA distinct quantitative,relative,coherent-family,algorithmic,hypothesis-removal or structural operation is eligible only after a CLOSED identifiable nonroutine step survives the strongest compatible source/primary reduction. Optimized classical constants,metadata,finite numerics,equivalent formulations and difficult unproved conjectures are not findings. Preserve every old frozen/PREFREEZE target and closed disposition. On overlap read eligible ACTUAL original-history mechanisms under prospective guards;exact completed exceptions never open linked protected namespaces.\n\nAfter complete operative reading choose and develop ONE distinct fully specified full-scope operation with sustained CONCRETE mathematics beyond a first failed shortcut. Try the strongest integrated source/primary payment before naming a bridge unpaid. Keep actual vectors,orders,common witnesses,parameters,dimension/probability/energy budgets and ALL compatibility interfaces. Freeze a viable exact theorem BEFORE author-proof development,then close every quantifier/constant/interface. If nothing closes,honest PREFREEZE/no nominee with exact gaps;no weaker substitute,self-grade,count,exhaustive clearance,global impossibility or worldwide-priority claim.\n\nKeep ALL source/primary/history/search/extract/render/copied bodies AND named metadata PRIVATE/local under original rights. Prospectively serialize EVERY literal wildcard/substring rule below before optional filename traversal/body selection beyond narrow exceptions,retaining r/no-r,flat/compound/role aliases. At most ONE correctly pruned original-history traversal with no size/extension cutoff on eligible authored UTF8 after pruning;no projectwide rg-then-filter,broad untracked inventory or old scan rerun. Disclose false admissions,coarse omissions,versions/read extents,truncation recovery,late reads and incomplete transitive ancestry. Seal YOUR own fresh exact selection ONCE with detached FINAL/MANIFEST/outside REPORT anchors,a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over fewer files. Artifact checks are not math gates. No nested agents,shared/git writes,public/browser actions or downstream formal/manuscript/release work. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews of a viable full author proof.\n\n'
extra='\nFurther prospective literal twins and opaque derivative alias:\n*arithmetic*162ac* *arithmetic*r162ad* *tree-signing-assembly* *i198-geometry-representation-discovery*\n\n'
brief=(prefix+previous+section+isolation+extra+marker.decode()).encode()+standing
patterns=lambda s:{g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
assert patterns(old)<=patterns(brief.decode())
assert brief.split(marker,1)[1]==standing
BP.write_bytes(brief)
dump(N/'private/canonical-selection.json',selected)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,source='097',catalogue_extent=[160713,161938],source096_body_not_selected=True,canonical_blobs=11,canonical_entries_including_roots=13,completed_direct_inputs=5,parent_source_body_read=False,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=11)))
