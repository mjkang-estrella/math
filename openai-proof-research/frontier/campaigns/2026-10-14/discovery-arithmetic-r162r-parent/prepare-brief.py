#!/usr/bin/env python3
"""Prepare one distinct source task; preserve all standing and isolation instructions."""
from pathlib import Path
import hashlib,json,re,fnmatch
p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162r-parent'
old=(b/'expanded-target-2026-10-17/fresh-arithmetic-r162r-brief.txt').read_text();root=b/'fresh-arithmetic-discovery-r162s';target=b/'expanded-target-2026-10-17/fresh-arithmetic-r162s-brief.txt'
assert not root.exists() and not target.exists()
iso=json.loads((o/'prospective-isolation-arithmetic162s.json').read_bytes());assert iso['checked_before_new_root_brief'] and iso['peer_original_initial_briefs']
for x in iso['peer_original_initial_briefs']:
 data=(p/x['brief']).read_bytes();assert hashlib.sha256(data).hexdigest()==x['brief_sha256'];patterns=re.findall(r'\*[^\s,;()]*\*',data.decode())
 for path in [root,target,b/'discovery-arithmetic-r162s-parent']:assert any(fnmatch.fnmatchcase(path.relative_to(p).as_posix().casefold(),z.casefold()) for z in patterns)
marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
header=old.split('This is ONE NEW DISTINCT Source082 family',1)[0].replace('r162r','r162s').replace('confirmed triangular-Hilbert annular-variation operative-proof discovery','confirmed Lipschitz-direction Hilbert-transform operative-proof discovery')
header+='''This is ONE NEW DISTINCT Source083 family. Before creation,the entire root/brief/future-parent namespace was checked against the recorded foreign current task's ORIGINAL INITIAL brief. Its *arithmetic*r162* guard covers every new path. Recorded status is not fresh liveness;no foreign live task,body,findings or activity was queried. Own162s is excluded from broad history but own I/O is authorized. This chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162r remains PREFREEZE/no nominee. Preserve its FULL logarithm-free sqrt(n) hard-annular count for EVERYn>=1,EVERYrough complexL3(R2) pair,ALLpositive scales and at mostn disjoint radius intervals chosen pointwise at the output. No supremum overn inside the norm or full strongV2 is asserted. The SAME-family E_e-E_R count atL3xL3->L3/2 is equivalent and remains unpaid. Smoothsqrt(n),hardsqrt(n)log(2+n),fullr>2variation/maximal/jointconvergence and dyadic absolute coefficients are paid. Strongest ACTUAL primary operations additionally pay full POINTWISE V2(E):L4xL4->L2 through bandpass value/short variation,odd-box decomposition and finite Stieltjes superposition. That stronger operation is NOT a nominee. Cyclic interpolation moves selectors onto integration variables;the joint frequency/jump budget still retainslog;actual dyadic embeddings do not yet represent every continuum selector with summable carry costs. No failed method is an operator counterexample. Do not retry with a restricted partition,smoothinput,finite scales,or easier exponents. All previous scopes remain immutable.

'''
header+='Arithmetic162q remains PREFREEZE/no nominee.'+old.split('Arithmetic162q remains PREFREEZE/no nominee.',1)[1].split('Prospective isolation BEFORE FIRST filename traversal',1)[0]
isolation='Prospective isolation BEFORE FIRST filename traversal'+old.split('Prospective isolation BEFORE FIRST filename traversal',1)[1].split('Catalogue access,if needed:',1)[0]
extra=['*arithmetic*162s*','*arithmetic*r162s*']+[v for n in range(201,221) for v in [f'*structural*{n}*',f'*structural*r{n}*']]
isolation=isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings',' '+' '.join(extra)+'\n\nPrune these case-insensitive FULL-PATH substrings',1)
closed='Arithmetic162h remains CLOSED WHOLE-SCOPE'+old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE',1)[1].split('Your ONE developed family is SOURCE082:',1)[0]
direct=json.loads((o/'private/next-direct-originals.json').read_bytes());exceptions='\n'.join(x['path'].removeprefix('frontier/campaigns/2026-10-14/') for x in direct)
body='''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[139784,140896),EXACT Source083 body. Parent decoded ONLY the first TWO numeric-title strings in ONE bounded14000-byte navigation window and ONLY083 body. Labels need not be contiguous. ONE confirmed folder has21descendants/18blobs plus its root;actual wrapper build/main.tex. Parent read NO operative source body. No child title locator,catalogue screen,extra family,opening or whole-file catalogue decode. Selection failure grants no broader access.

Read these FOUR exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
'''+exceptions+'''
No containing namespace,linked body,peer status/activity or review access is admitted. Preserve the full r162r count diagnostic,the SAME-family endpoint-error equivalence,the stronger paid L4V2 operation and precise symmetric gap. Every older scope/disposition remains immutable. Exact completed exceptions never authorize broader traversal or an old-scan rerun.

'''
family='''Your ONE developed family is SOURCE083: HILBERT TRANSFORMS ALONG LIPSCHITZ DIRECTIONS. The pinned source and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural statements. Validate exact applicability and new deductions;do not audit upstream truth.

Confirmed canonical folder:
preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026
Actual wrapper:
preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/build/main.tex
bytes1101;Git blobdda6b8ed6f053f0312f49f3322421b95f22842d0.
Authenticate ALL18 canonical blobs against COMPLETE-tree size/Git blob/SHA256,including README,compiled PDF and every actual local object. Read ALL actual wrappers/FULL theorem interfaces,and COMPLETELY all operative proofs,ancestors,actual includes and required companions supporting the developed operation,strongest relevant ACTUAL primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes,not filename inference. Do not defer canonical proof reading until verification. Distinguish proof text from compiled/typography authentication. Record mathematical understanding,versions and exact extents;recover clipped seams. Metadata,headlines,hashes and others' reading ledgers are not proof-body reading.

The ENTIRE source theorem is PAID: a UNIFORM strongL2 planar directional Hilbert-transform estimate for EVERY Lipschitz UNIT vector field depending on BOTH coordinates,with integration length bounded by the stated absolute multiple of reciprocal Lipschitz seminorm,UNIFORMLY over inner truncations;and the precise bounded principal-value operator/convergence consequences actually proved. The source already establishes the stated short-scale Stein weak-(2,2) conjecture. Do not nominate that result,a one-coordinate/constant/smooth/favorable field restriction,finite inner truncations,weak type obtained from strong type,rescaling to another Lipschitz constant,or routine density/duality/interpolation/convergence restatements.

Read the ACTUAL proof for stronger compatible operations beyond the headline: track direction normalization and degeneracy when the seminorm is zero,global/local domain,hard or smooth cutoff conventions,orientation/sign changes,measurability and quantifier order,truncation length,field dependence of constants,flow versus straight-line sampling,Jacobian and adjoint geometry,packet/tile selection,correlations across output points and scales,and local-to-global/limit interfaces. If the strongest integrated proof ALREADY pays a maximal,variation,vector-valued,weighted,relative,stability,uniform-family or other operation,it must be credited. A pointwise chosen truncation,field or time cannot be moved outside a norm without a compatible actual proof. Conversely a failed naive transfer does not rule out stronger compatible source/primary composition.

Do not silently replace any proposed full scope by extra differentiability,one-coordinate dependence,small slope,favorable support,common truncation,finite rank,independent fields,restricted input,extra curvature/transversality or finite scales. Preserve EVERY earlier triangular-Hilbert count,fixed-slope variation,temporal variation,orthonormal/common-graph,sparse-corner,reflectionless and other scope. A different kernel/geometry does not certify novelty or reopen a settled gate.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated source/primary payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are eligible,but an unproved target is not a finding. Carry sustained CONCRETE mathematics beyond a first failed shortcut;track all joint laws,geometric normalization,scale/energy/cancellation budgets and compatibility interfaces. Preserve failed attempts and exact residuals. Freeze a viable EXACT theorem BEFORE author-proof development,then close EVERY quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with strongest integrated derivation and precise unpaid operation;no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history proof extents,versions,access failures,late reads,truncation recovery,false admissions and coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet ONCE with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief=header+isolation+body+closed+family+marker+standing;og=set(re.findall(r'\*[^\s,;()]*\*',old));ng=set(re.findall(r'\*[^\s,;()]*\*',brief));assert og<=ng and brief.split(marker,1)[1]==standing;assert all(x in ng for x in extra)
for x in direct:
 data=(p/x['path']).read_bytes();assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256']
selection=json.loads((o/'private/next-canonical-selection.json').read_bytes());assert len(selection)==22 and sum(x['type']=='blob' for x in selection)==18
root.mkdir();target.write_text(brief)
prep={'path':target.relative_to(p).as_posix(),'root':root.relative_to(p).as_posix(),'bytes':len(brief.encode()),'sha256':hashlib.sha256(brief.encode()).hexdigest(),'old_literal_guards':len(og),'new_literal_guards':len(ng),'all_guards_and_standing5570bytes_preserved':True,'source_label':'083','catalogue_extent':[139784,140896],'canonical_folders':1,'canonical_descendants':21,'canonical_blobs':18,'parent_operative_proof_read':False,'foreign_original_initial_guards_before_creation':True,'direct_completed_originals_count':4,'prospective_structural_201_to_220_twins_added':True}
(o/'brief-preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
args={'clientRequestId':'twenty-20261023-fresh-arithmetic-r162s-codex-astra-r1','target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},'mode':'async','role':'research','title':'Arithmetic162s: confirmed Lipschitz-direction Hilbert-transform discovery','task':brief}
(o/'private/submitted-prompt.json').write_text(json.dumps(args,indent=2)+'\n');print(json.dumps(prep,indent=2))
