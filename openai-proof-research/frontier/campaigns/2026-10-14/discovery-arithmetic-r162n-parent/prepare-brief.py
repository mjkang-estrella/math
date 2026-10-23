#!/usr/bin/env python3
"""Prepare distinct Source079 while preserving every inherited guard and standing byte."""
from pathlib import Path
import hashlib
import json
import re

p=Path.cwd()
b=p/'frontier/campaigns/2026-10-14'
o=b/'discovery-arithmetic-r162n-parent'
old=(b/'expanded-target-2026-10-17/fresh-arithmetic-r162n-brief.txt').read_text()
root=b/'fresh-arithmetic-discovery-r162o'
target=b/'expanded-target-2026-10-17/fresh-arithmetic-r162o-brief.txt'
assert not root.exists() and not target.exists()
iso=json.loads((o/'prospective-isolation-arithmetic162o.json').read_bytes())
assert iso['checked_before_new_root_brief']
for x in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p/x['brief']).read_bytes()).hexdigest()==x['brief_sha256']
marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1]
assert len(standing.encode())==5570
header=old.split('This is ONE NEW DISTINCT Source078 family',1)[0]
header=header.replace('r162n','r162o').replace('confirmed three-dimensional Bochner-Riesz operative-proof discovery','confirmed three-dimensional wave local-smoothing operative-proof discovery')
header+='''This is ONE NEW DISTINCT Source079 family. The ENTIRE root/brief/future parent namespace was checked against *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Recorded status is not fresh liveness. Parent queried no foreign live status,body,findings or activity. Own162o is excluded from broad history but direct own I/O is authorized. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162n remains PREFREEZE/no nominee. Its full diagnostic is fixed-radius sparse domination of order1/8 three-dimensional Bochner-Riesz at (24/17,12/5) for EVERY bounded compactly supported rough complex test pair. The strongest paid composition already gives (24/17,q) for EVERYq>12/5,including multiscale epsilon removal and recursion,and the special order1/4 Hilbert endpoint. The unpaid sufficient bridge is the uniform cumulative disjoint-cube L^(12/7) estimate with weight2^(-3L(Q)/8),EVERY finite disjoint dyadic family,rough complex cube inputs and bounded scale coefficients,independent of occupied scales. BOTH coefficient-cardinality and cumulative-scale losses must close on the SAME compatible construction. No open-exponent/Hilbert/favorable-scale substitute,no actual counterexample or global impossibility claim. Transitive primary reading remains incomplete. Four exact completed files below preserve this diagnostic and its limits.

'''
prior=old.split('Arithmetic162m is CLOSED WHOLE-SCOPE',1)[1].split('Prospective isolation BEFORE FIRST filename traversal',1)[0]
header+='Arithmetic162m is CLOSED WHOLE-SCOPE'+prior
isolation='Prospective isolation BEFORE FIRST filename traversal'+old.split('Prospective isolation BEFORE FIRST filename traversal',1)[1].split('Catalogue access,if needed:',1)[0]
isolation=isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings',' *arithmetic*162o* *arithmetic*r162o*\n\nPrune these case-insensitive FULL-PATH substrings',1)
closed='Arithmetic162h remains CLOSED WHOLE-SCOPE'+old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE',1)[1].split('Your ONE developed family is SOURCE078:',1)[0]
direct=json.loads((o/'private/next-direct-originals.json').read_bytes())
exceptions='\n'.join(Path(x['path']).relative_to(b).as_posix() if Path(x['path']).is_absolute() else x['path'].removeprefix('frontier/campaigns/2026-10-14/') for x in direct)
body='''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[133395,134257),EXACT Source079 body. Parent decoded ONLY the first TWO numeric-title strings in ONE bounded14000-byte navigation window and ONLY079 body. Labels need not be contiguous. One confirmed folder has17descendants/15blobs plus its root. Actual wrapper is build/main.tex. Parent read NO source proof body. No child title locator,catalogue screen,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read these FOUR exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
'''+exceptions+'''
No containing namespace,linked body,peer status/activity or other review access is admitted. Preserve the full fixed sparse-corner diagnostic,all paid reductions,its exact cumulative-array residual and reading limits. Every earlier target and disposition remains immutable. Exact completed exceptions never authorize a new broad old-scan rerun.

'''
family='''Your ONE developed family is SOURCE079: LOCAL SMOOTHING FOR THE EUCLIDEAN WAVE EQUATION IN THREE SPATIAL DIMENSIONS. The pinned manuscript and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural results. Validate exact applicability and genuinely new deductions;do not audit upstream truth.

Authenticate ALL15 canonical blobs against complete-tree size/Git blob/SHA256,including README,compiled PDF and every actual local object. Read actual README/wrapper,FULL theorem interfaces,and COMPLETELY all operative proofs/ancestors/includes/required companions supporting the developed operation,strongest relevant ACTUAL primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes,not filename inferences. Complete canonical proof reading must not be deferred until verification. Distinguish actual proof text from compiled PDF authentication. Keep durable mathematical understanding and exact extents;recover clipped seams. Metadata,interfaces,hashes and others' reading ledgers are not proof-body reading.

Confirmed folder/wrapper:
preprints/Critical-local-smoothing-for-the-three-dimensional-wave-equation-September-24-2026
preprints/Critical-local-smoothing-for-the-three-dimensional-wave-equation-September-24-2026/build/main.tex
bytes2041;Git bloba2b66419adc9a25640f7115e34a899d5d9173f89.

The ENTIRE Euclidean strict-range conclusion is PAID: for EVERY2<p<infinity,the wave local-smoothing estimate in THREE spatial dimensions holds with Sobolev regularity ABOVE max{0,1-3/p}. In particular the critical L3 estimate with EVERY positive Sobolev loss is paid. Standard L2 unitarity,interpolation,duality,rescaling,finite chart/time partitions,and every actual operative quantitative/conditional consequence in the full source are paid. Do not nominate this theorem,a parameter substitution,standard consequence,or already-closed extremizer/positive-order radius-variation composition. The actual source includes a Bochner-Riesz consequence;read and credit it fully rather than recasting it as new.

Read exact propagation/Fourier conventions,time interval,frequency/Sobolev normalization,phase/amplitude class,regularity,compactness,uniformity/constants,epsilon loss and all cylinder/physical/recovery interfaces from the FULL source proof. Credit EVERY stronger finite-array,lower-dimensional,canonical-name,interior,cylinder-action,round-transfer,entropy and physical-wave operation ACTUALLY established,alongside the strongest compatible primary proofs. A failed naive transfer does not rule out a stronger paid composition.

Distinguish fixed strict regularity from equality endpoints or effective loss dependence;space-time averaging from maximal/variation/arbitrary-time-set claims;Euclidean constant coefficients from variable metrics/general Fourier-integral operators;single wave from multiple/coherent input laws;fixed phase class from uniform families;local time from global time. Do not assume general weights,fractal sampling,variable curvature,boundary propagation,stability or vector estimates merely from the headline. Conversely do not overlook them if actually paid by the full operative proof. No smooth-data,favorable frequency sector,time subset,extra curvature,regular law or transversality may replace a proposed full target. Earlier maximal,shared-profile,weighted-Fourier,Kakeya,sparse-corner and local-smoothing targets keep their exact scopes;paid premises do not reopen protected task namespaces.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are eligible,but an unproved hard target is not a finding. Carry sustained concrete mathematics beyond the first failed shortcut,tracking joint laws,normalizations,rate/entropy/scale budgets and every compatibility interface. Preserve failed attempts and precise residuals. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with the strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history proof extents,versions,access failures,late reads,truncation recovery,false admissions and coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief=header+isolation+body+closed+family+marker+standing
old_guards=set(re.findall(r'\*[^\s,;()]*\*',old));new_guards=set(re.findall(r'\*[^\s,;()]*\*',brief))
assert old_guards<=new_guards and brief.split(marker,1)[1]==standing
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and hashlib.sha256(d).hexdigest()==x['sha256']
root.mkdir();target.write_text(brief)
prep={'path':target.relative_to(p).as_posix(),'root':root.relative_to(p).as_posix(),
    'bytes':len(brief.encode()),'sha256':hashlib.sha256(brief.encode()).hexdigest(),
    'old_literal_guards':len(old_guards),'new_literal_guards':len(new_guards),
    'all_guards_and_standing5570bytes_preserved':True,'source_label':'079',
    'catalogue_extent':[133395,134257],'canonical_folders':1,'canonical_descendants':17,
    'canonical_blobs':15,'parent_operative_proof_read':False,
    'foreign_original_initial_guards_before_creation':True,'direct_completed_originals_count':4}
(o/'brief-preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
args={'clientRequestId':'twenty-20261023-fresh-arithmetic-r162o-codex-astra-r1',
    'target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},
    'mode':'async','role':'research','title':'Arithmetic162o: confirmed three-dimensional wave local-smoothing operative-proof discovery',
    'task':brief}
(o/'private/submitted-prompt.json').write_text(json.dumps(args,indent=2)+'\n')
print(json.dumps(prep,indent=2))
