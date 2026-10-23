#!/usr/bin/env python3
"""Prepare distinct Source080, preserving inherited guards and standing instructions."""
from pathlib import Path
import hashlib
import json
import re

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162o-parent'
old=(b/'expanded-target-2026-10-17/fresh-arithmetic-r162o-brief.txt').read_text()
root=b/'fresh-arithmetic-discovery-r162p';target=b/'expanded-target-2026-10-17/fresh-arithmetic-r162p-brief.txt'
assert not root.exists() and not target.exists()
iso=json.loads((o/'prospective-isolation-arithmetic162p.json').read_bytes());assert iso['checked_before_new_root_brief']
for x in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p/x['brief']).read_bytes()).hexdigest()==x['brief_sha256']
marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
header=old.split('This is ONE NEW DISTINCT Source079 family',1)[0]
header=header.replace('r162o','r162p').replace('confirmed three-dimensional wave local-smoothing operative-proof discovery','confirmed exact Sobolev endpoint Schrodinger-convergence operative-proof discovery')
header+='''This is ONE NEW DISTINCT Source080 family. The ENTIRE root/brief/future parent namespace was checked against *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Recorded status is not fresh liveness. Parent queried no foreign live status,body,findings or activity. Own162p is excluded from broad history but direct own I/O is authorized. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162o remains PREFREEZE/no nominee. Its diagnostic fixes <D>^(-3/4)log(e+<D>)^(-5/8)chi(2^(-K)D),EVERY K>=1,EVERY finite rough complex L2-orthonormal system and complex coefficient vector. One COMMON time in[0,1] occurs in the entire density,with localL2(B) controlled by coefficientell2 independently of BOTH rank andK. Equivalently it needs a uniform quadratic squared-kernel estimate on EVERY measurable common time graph. The strongest same-graph/full-cross-frequency kernel composition retains(1+K)^(1/4),while the stronger scalar critical endpoint gives a different square-root rank loss. A log-free cone-graph estimate suffices but is neither proved nor asserted necessary. Uniformity fora>3/4 is paid and no substitute;no smooth graph,favorable sector,rank/cutoff or positive-Sobolev-loss replacement. Complete canonical but incomplete transitive primary reading remains disclosed. Preserve that exact wave scope and every earlier target.

'''
header+='Arithmetic162n remains PREFREEZE/no nominee.'+old.split('Arithmetic162n remains PREFREEZE/no nominee.',1)[1].split('Prospective isolation BEFORE FIRST filename traversal',1)[0]
isolation='Prospective isolation BEFORE FIRST filename traversal'+old.split('Prospective isolation BEFORE FIRST filename traversal',1)[1].split('Catalogue access,if needed:',1)[0]
isolation=isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings',' *arithmetic*162p* *arithmetic*r162p*\n\nPrune these case-insensitive FULL-PATH substrings',1)
closed='Arithmetic162h remains CLOSED WHOLE-SCOPE'+old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE',1)[1].split('Your ONE developed family is SOURCE079:',1)[0]
direct=json.loads((o/'private/next-direct-originals.json').read_bytes())
exceptions='\n'.join(x['path'].removeprefix('frontier/campaigns/2026-10-14/') for x in direct)
body='''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[134257,135955),EXACT Source080 body. Parent decoded ONLY the first TWO numeric-title strings in ONE bounded14000-byte navigation window and ONLY080 body. Labels need not be contiguous. Two confirmed folders have41descendants/35blobs plus their roots. Actual wrappers are build/main.tex(planar) and build/paper.tex(higher dimensions). Parent read NO source proof body. No child title locator,catalogue screen,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read these SIX exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
'''+exceptions+'''
No containing namespace,linked body,peer status/activity or other review access is admitted. The first four preserve r162o's full diagnostic and limits. The last two preserve r45's EXACT critical Schrodinger graph-Schatten scope and paid strict scalar weighted-tree operations. Do not rename that unpaid full orthonormal improvement as a new family or nominate a favorable subclass. Read the actual original bodies,not only their names or summaries. Every earlier scope/disposition remains immutable. Exact completed exceptions never authorize a broader old-scan rerun.

'''
family='''Your ONE developed family is SOURCE080: EXACT SOBOLEV ENDPOINT FOR FREE SCHRODINGER CONVERGENCE. BOTH pinned manuscripts and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and genuinely new deductions;do not audit upstream truth.

Authenticate ALL35 canonical blobs against complete-tree size/Git blob/SHA256,including READMEs,compiled PDFs and every actual local object. Read BOTH actual READMEs/wrappers,FULL theorem interfaces,and COMPLETELY all operative proofs/ancestors/includes/required companions supporting the developed operation,strongest relevant ACTUAL primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes and driver roles,not filename inferences. Complete canonical proof reading must not be deferred until verification. Distinguish actual proof text from compiled/typography authentication. Keep durable mathematical understanding and exact extents;recover clipped seams. Metadata,interfaces,hashes and others' reading ledgers are not proof-body reading.

Confirmed folders/wrappers:
preprints/Endpoint-convergence-for-the-planar-Schrodinger-equation-September-24-2026
preprints/Endpoint-convergence-for-the-planar-Schrodinger-equation-September-24-2026/build/main.tex
bytes2209;Git blobf5dbf64d18dc0656198cad346991fe8446917dfb.
preprints/Endpoint-pointwise-convergence-for-the-Schrodinger-equation-in-higher-dimensions-September-24-2026
preprints/Endpoint-pointwise-convergence-for-the-Schrodinger-equation-in-higher-dimensions-September-24-2026/build/paper.tex
bytes984;Git blob2e8a8835c0ef98614bff98fe971db4aa25a0e0d0.

The ENTIRE sharp equality theorem is PAID: for EVERY dimensionn>=2 and EVERY f inH^[n/(2(n+1))](R^n),the free Schrodinger evolution converges almost everywhere to f as t decreases to0,including planarH^(1/3). The ACTUAL Gaussian-regularization conventions and one-full-measure/all-time assertions in BOTH manuscripts are also paid: the planar source removes Gaussian regularization first,on one full-measure spatial set for EVERY0<t<1,and obtains continuity at0;the higher-dimensional source describes uniform removal over0<t<1. Read exact hypotheses,normalizations,representatives and limit orders from the operative proofs. Do not nominate the endpoint convergence theorem,a stricter Sobolev subclass,a finite-frequency version,parameter substitution or routine density/Banach-principle corollary. Credit EVERY stronger actual source estimate and construction,not merely the headline.

Track Fourier/evolution signs,homogeneous versus inhomogeneous spaces,dimension dependence,Gaussian cutoff/remove-limit order,all-time versus fixed-time exceptional sets,local spatial versus global statements,pointwise representative versus norm convergence,and actual regularization uniformity/constants. A convergence theorem does not by its headline supply an arbitrary strong maximal-norm,weighted,graph-Schatten,orthonormal,variation,fractal-measure,variable-metric,vector,quantitative-rate or rougher-space theorem. Conversely any such compatible operation ACTUALLY established in the full source or strongest primary proof is paid. A failed naive shortcut does not rule out a stronger compatible known composition.

Do not insert smooth data,favorable Fourier sectors,regular time graphs,transversality,a restricted dimension/time set,a finite rank or a smaller coefficient class to replace a full target. Preserve the exact r45 critical graph-Schatten obligation;source scalar endpoint truth is not itself a new orthonormal result. Preserve r162o's different wave common-graph logarithmic target,r162n's sparse corner,the full4D maximal and every older scope. Paid premises do not reopen protected task namespaces or authorize desired-grade retries. The actual planar/higher-dimensional compatibility,tree/conditional laws and summation/regularization operations must be understood before extending them.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are eligible,but an unproved hard target is not a finding. Carry sustained concrete mathematics beyond the first failed shortcut,tracking joint laws,normalizations,rate/entropy/scale budgets and every compatibility interface. Preserve failed attempts and precise residuals. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with the strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history proof extents,versions,access failures,late reads,truncation recovery,false admissions and coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief=header+isolation+body+closed+family+marker+standing
og=set(re.findall(r'\*[^\s,;()]*\*',old));ng=set(re.findall(r'\*[^\s,;()]*\*',brief))
assert og<=ng and brief.split(marker,1)[1]==standing
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and hashlib.sha256(d).hexdigest()==x['sha256']
root.mkdir();target.write_text(brief)
prep={'path':target.relative_to(p).as_posix(),'root':root.relative_to(p).as_posix(),
    'bytes':len(brief.encode()),'sha256':hashlib.sha256(brief.encode()).hexdigest(),
    'old_literal_guards':len(og),'new_literal_guards':len(ng),'all_guards_and_standing5570bytes_preserved':True,
    'source_label':'080','catalogue_extent':[134257,135955],'canonical_folders':2,
    'canonical_descendants':41,'canonical_blobs':35,'parent_operative_proof_read':False,
    'foreign_original_initial_guards_before_creation':True,'direct_completed_originals_count':6}
(o/'brief-preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
args={'clientRequestId':'twenty-20261023-fresh-arithmetic-r162p-codex-astra-r1',
    'target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},
    'mode':'async','role':'research','title':'Arithmetic162p: confirmed exact Sobolev endpoint Schrodinger-convergence discovery','task':brief}
(o/'private/submitted-prompt.json').write_text(json.dumps(args,indent=2)+'\n');print(json.dumps(prep,indent=2))
