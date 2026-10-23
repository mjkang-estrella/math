#!/usr/bin/env python3
"""Prepare distinct Source082 while preserving inherited guard/standing instructions."""
from pathlib import Path
import hashlib
import json
import re

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162q-parent'
old=(b/'expanded-target-2026-10-17/fresh-arithmetic-r162q-brief.txt').read_text()
root=b/'fresh-arithmetic-discovery-r162r';target=b/'expanded-target-2026-10-17/fresh-arithmetic-r162r-brief.txt'
assert not root.exists() and not target.exists()
iso=json.loads((o/'prospective-isolation-arithmetic162r.json').read_bytes());assert iso['checked_before_new_root_brief']
for x in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p/x['brief']).read_bytes()).hexdigest()==x['brief_sha256']
marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
header=old.split('This is ONE NEW DISTINCT Source081 family',1)[0]
header=header.replace('r162q','r162r').replace('confirmed higher-codimension Riesz-transform rectifiability operative-proof discovery','confirmed triangular-Hilbert annular-variation operative-proof discovery')
header+='''This is ONE NEW DISTINCT Source082 family. The ENTIRE root/brief/future parent namespace was checked against *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Recorded status is not fresh liveness. Parent queried no foreign live status,body,findings or activity. Own162r is excluded from broad history but direct own I/O is authorized. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162q remains PREFREEZE/no nominee. Its full reflectionless diagnostic retains EVERYd>=4,2<=n<=d-2,positive n-ADRadon measure,uniform scalar-to-vectorL2hard Riesz truncations and vanishing of the ACTUAL mean-zero exterior-subtracted pairing on EVERY compact Lipschitz test. The prospective global constant-density affine n-plane conclusion is unproved;degeneracies are separated and nondegenerate compact supports eliminated,not assumed away. Paid compositions give flat seeds in EVERY ball and finite-energy-to-plane rigidity without a graph or density-tail assumption. The unpaid sufficient bridge is ONE FIXED plane with finite total orthogonal energy for EVERY full input,or another coherent global argument retaining all cross forces. A same-flat-measure annular block is a second sufficient route;independent local planes and localR^(n+1)energy do not supply it. No finite-energy,graph,exterior-flat or favorable-input substitute. Complete canonical but incomplete transitive primary reading remains disclosed.

'''
header+='Arithmetic162p remains PREFREEZE/no nominee.'+old.split('Arithmetic162p remains PREFREEZE/no nominee.',1)[1].split('Prospective isolation BEFORE FIRST filename traversal',1)[0]
isolation='Prospective isolation BEFORE FIRST filename traversal'+old.split('Prospective isolation BEFORE FIRST filename traversal',1)[1].split('Catalogue access,if needed:',1)[0]
isolation=isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings',' *arithmetic*162r* *arithmetic*r162r*\n\nPrune these case-insensitive FULL-PATH substrings',1)
closed='Arithmetic162h remains CLOSED WHOLE-SCOPE'+old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE',1)[1].split('Your ONE developed family is SOURCE081:',1)[0]
direct=json.loads((o/'private/next-direct-originals.json').read_bytes());exceptions='\n'.join(x['path'].removeprefix('frontier/campaigns/2026-10-14/') for x in direct)
body='''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[137284,139784),EXACT Source082 body. Parent decoded ONLY the first TWO numeric-title strings in ONE bounded14000-byte navigation window and ONLY082 body. Labels need not be contiguous. THREE confirmed companion folders have47descendants/39blobs plus their roots. Actual wrappers are build/main.tex in each. Parent read NO source proof body. No child title locator,catalogue screen,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read these FOUR exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
'''+exceptions+'''
No containing namespace,linked body,peer status/activity or other review access is admitted. Preserve the full reflectionless diagnostic,paid finite-energy reduction,coherent same-measure annular interface and exact remaining global gap. No desired-grade retry or restricted replacement. Every older scope/disposition remains immutable. Exact completed exceptions never authorize a broader old-scan rerun.

'''
family='''Your ONE developed family is SOURCE082: ANNULAR VARIATION AND DYADIC ABSOLUTE BOUNDS FOR THE TRIANGULAR HILBERT TRANSFORM. ALL THREE pinned companion manuscripts and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural results. Validate exact applicability and genuinely new deductions;do not audit upstream truth.

Authenticate ALL39 canonical blobs against complete-tree size/Git blob/SHA256,including READMEs,compiled PDFs and every actual local object. Read ALL actual READMEs/wrappers,FULL theorem interfaces,and COMPLETELY all operative proofs/ancestors/includes/required companions supporting the developed operation,strongest relevant ACTUAL primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes,not filename inferences. Complete canonical proof reading must not be deferred until verification. Distinguish actual proof text from compiled/typography authentication. Keep durable mathematical understanding and exact extents;recover clipped seams. Metadata,interfaces,hashes and others' reading ledgers are not proof-body reading.

Confirmed folders/wrappers:
preprints/Annular-variation-of-the-triangular-Hilbert-transform-at-the-symmetric-point-October-5-2026
preprints/Annular-variation-of-the-triangular-Hilbert-transform-at-the-symmetric-point-October-5-2026/build/main.tex
bytes2269;Git blob1a7146f1427414558c6d9ad462742555065c9733.
preprints/An-L3-bound-for-the-dyadic-triangular-Hilbert-form-October-5-2026
preprints/An-L3-bound-for-the-dyadic-triangular-Hilbert-form-October-5-2026/build/main.tex
bytes803;Git blob0dac4f578771c65816e9ab17a4a20acc965d59f8.
preprints/The-maximal-triangular-Hilbert-transform-at-the-symmetric-point-September-24-2026
preprints/The-maximal-triangular-Hilbert-transform-at-the-symmetric-point-September-24-2026/build/main.tex
bytes879;Git blob1f6cd5ed9114cf9eb42a8b5323492d9fa6220e27.

The ENTIRE continuous symmetric theorem is PAID: for arbitrary COMPLEX inputs inL3(R2)xL3(R2),the triangular Hilbert transform has L^(3/2) maximal bounds over BOTH positive hard truncation endpoints;annularr-variation for EVERYr>2,with output-point-dependent partitions over ALL positive scales;and the stated JOINT a.e. and norm principal-value/convergence conclusions. Pairing with a thirdL3 input already settles the symmetric scalar trilinear estimate. Do not nominate any of those statements,a finite-scale/smooth/real-data weakening,an uncountable-to-measurable partition restatement,or routine density/interpolation/duality/convergence consequence.

The ENTIRE dyadic absolute theorem is also PAID: unrestricted realL3xL3xL3 inputs,ANY finite set of scales,sum of ABSOLUTE local contributions bounded by40 times the norm product,with coefficients of modulus<=1 allowed independently among admissible interval triples. Read the actual model and coefficient conventions. Elementary real/imaginary splitting is not a new complex-input theorem. Do not ignore this stronger absolute operation by relying only on the older continuous maximal headline. Read how actual dyadic,continuous,hard/smooth and annular conventions are related and credit EVERY stronger compatible operation established by ALL three full proofs and strongest primary antecedents.

Track exact bilinear/trilinear coordinates,kernel signs/principal-value cancellation,endpoint order,positive-scale geometry,complex phases,coefficient dependence,normalizations,transference,local-to-global and joint-law interfaces from the ACTUAL proofs. Distinguishr>2 from its equality endpoint,one fixed admissible coefficient/model class from arbitrary modulation or weighted variants,and symmetric exponents from other exponent regions. A headline does not supply arbitrary non-dyadic coefficient domination,variable geometric directions,vector-valued/orthonormal,weighted,sparse,multi-parameter,endpoint or quantitative-uniformity extensions. Conversely any such operation ACTUALLY paid by the strongest integrated source/primary proof must be credited. A failed naive transfer does not rule out a stronger compatible known composition.

No fixed/favorable partition,common phase,positive input,smoothness,finite cardinality,regular distribution or extra transversality may replace a proposed full target. Preserve all older scalar temporal-variation,orthonormal/common-graph,sparse-corner,reflectionless and other scopes;neighbors are not automatically reopened or certified novel. Quantifier order and retained measure/input must remain compatible across any transference or cancellation construction.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are eligible,but an unproved hard target is not a finding. Carry sustained concrete mathematics beyond the first failed shortcut,tracking joint laws,normalizations,scale/energy/cancellation budgets and every compatibility interface. Preserve failed attempts and precise residuals. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with the strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history proof extents,versions,access failures,late reads,truncation recovery,false admissions and coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief=header+isolation+body+closed+family+marker+standing;og=set(re.findall(r'\*[^\s,;()]*\*',old));ng=set(re.findall(r'\*[^\s,;()]*\*',brief));assert og<=ng and brief.split(marker,1)[1]==standing
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and hashlib.sha256(d).hexdigest()==x['sha256']
root.mkdir();target.write_text(brief)
prep={'path':target.relative_to(p).as_posix(),'root':root.relative_to(p).as_posix(),'bytes':len(brief.encode()),
    'sha256':hashlib.sha256(brief.encode()).hexdigest(),'old_literal_guards':len(og),'new_literal_guards':len(ng),
    'all_guards_and_standing5570bytes_preserved':True,'source_label':'082','catalogue_extent':[137284,139784],
    'canonical_folders':3,'canonical_descendants':47,'canonical_blobs':39,'parent_operative_proof_read':False,
    'foreign_original_initial_guards_before_creation':True,'direct_completed_originals_count':4}
(o/'brief-preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
args={'clientRequestId':'twenty-20261023-fresh-arithmetic-r162r-codex-astra-r1',
    'target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},
    'mode':'async','role':'research','title':'Arithmetic162r: confirmed triangular-Hilbert annular-variation discovery','task':brief}
(o/'private/submitted-prompt.json').write_text(json.dumps(args,indent=2)+'\n');print(json.dumps(prep,indent=2))
