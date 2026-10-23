#!/usr/bin/env python3
"""Prepare distinct Source081, preserving every inherited literal guard and standing byte."""
from pathlib import Path
import hashlib
import json
import re

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162p-parent'
old=(b/'expanded-target-2026-10-17/fresh-arithmetic-r162p-brief.txt').read_text()
root=b/'fresh-arithmetic-discovery-r162q';target=b/'expanded-target-2026-10-17/fresh-arithmetic-r162q-brief.txt'
assert not root.exists() and not target.exists()
iso=json.loads((o/'prospective-isolation-arithmetic162q.json').read_bytes());assert iso['checked_before_new_root_brief']
for x in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p/x['brief']).read_bytes()).hexdigest()==x['brief_sha256']
marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
header=old.split('This is ONE NEW DISTINCT Source080 family',1)[0]
header=header.replace('r162p','r162q').replace('confirmed exact Sobolev endpoint Schrodinger-convergence operative-proof discovery','confirmed higher-codimension Riesz-transform rectifiability operative-proof discovery')
header+='''This is ONE NEW DISTINCT Source081 family. The ENTIRE root/brief/future parent namespace was checked against *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Recorded status is not fresh liveness. Parent queried no foreign live status,body,findings or activity. Own162q is excluded from broad history but direct own I/O is authorized. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162p remains PREFREEZE/no nominee. The source common-envelope time tree ALREADY pays absolute dyadic-frequency summation and frequency variation at one common time;do not recycle that false candidate. Its remaining temporal diagnostic fixes EVERYn>=2,s_n=n/[2(n+1)],q_n=2(n+1)/(n-1),EVERY rough complexH^s input,translated unit ball,smooth cutoffK>=1 and all measurable finite ordered partitions on[0,1],with localL2(|fK|+temporalV^q) UNIFORM in BOTH cutoff and partition cardinality. Completed estimates retain2^[K(n-1)/(2(n+1)^2)] or m^(1/q). The joint dual time-increment Fourier estimate preserving pointwiseell^(q-prime) coefficients and short-increment cancellation remains unpaid. A moving packet only excludes smaller exponents,not the diagnostic endpoint. No stronger-regularity,finite-cardinality or favorable-input substitute. Complete canonical but incomplete transitive primary reading remains disclosed.

'''
header+='Arithmetic162o remains PREFREEZE/no nominee.'+old.split('Arithmetic162o remains PREFREEZE/no nominee.',1)[1].split('Prospective isolation BEFORE FIRST filename traversal',1)[0]
isolation='Prospective isolation BEFORE FIRST filename traversal'+old.split('Prospective isolation BEFORE FIRST filename traversal',1)[1].split('Catalogue access,if needed:',1)[0]
isolation=isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings',' *arithmetic*162q* *arithmetic*r162q*\n\nPrune these case-insensitive FULL-PATH substrings',1)
closed='Arithmetic162h remains CLOSED WHOLE-SCOPE'+old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE',1)[1].split('Your ONE developed family is SOURCE080:',1)[0]
direct=json.loads((o/'private/next-direct-originals.json').read_bytes())
exceptions='\n'.join(x['path'].removeprefix('frontier/campaigns/2026-10-14/') for x in direct)
body='''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[135955,137284),EXACT Source081 body. Parent decoded ONLY the first TWO numeric-title strings in ONE bounded14000-byte navigation window and ONLY081 body. Labels need not be contiguous. One confirmed folder has16descendants/14blobs plus its root. Actual wrapper is build/paper.tex. Parent read NO source proof body. No child title locator,catalogue screen,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read these FOUR exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
'''+exceptions+'''
No containing namespace,linked body,peer status/activity or other review access is admitted. Preserve the full temporal-variation diagnostic,the paid absolute dyadic-frequency summation and exact remaining cutoff/cardinality losses. No desired-grade retry or restricted replacement. Every older scope and disposition remains immutable. Exact completed exceptions never authorize a broader old-scan rerun.

'''
family='''Your ONE developed family is SOURCE081: RIESZ TRANSFORMS AND UNIFORM RECTIFIABILITY IN HIGHER CODIMENSION. The pinned manuscript and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and genuinely new deductions;do not audit upstream truth.

Authenticate ALL14 canonical blobs against complete-tree size/Git blob/SHA256,including README,compiled PDF and every actual local object. Read actual README/wrapper,FULL theorem interfaces,and COMPLETELY all operative proofs/ancestors/includes/required companions supporting the developed operation,strongest relevant ACTUAL primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes,not filename inferences. Complete canonical proof reading must not be deferred until verification. Distinguish actual proof text from compiled/typography authentication. Keep durable mathematical understanding and exact extents;recover clipped seams. Metadata,interfaces,hashes and others' reading ledgers are not proof-body reading.

Confirmed folder/wrapper:
preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026
preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/build/paper.tex
bytes2308;Git blob662d41330963f9eabcdafbac8ee48d85a40788e0.

The ENTIRE quantitative higher-codimension theorem is PAID: for EVERY integersd>=4,2<=n<=d-2,an n-Ahlfors-David regular Radon measure onR^d is uniformly n-rectifiable whenever its n-dimensional Riesz transform is uniformlyL2-bounded from SCALARL2(mu) to VECTOR-VALUEDL2(mu) over ALL positive HARD truncations. Uniform rectifiability/big-pieces-of-Lipschitz-images bounds depend ONLY on dimensions,AD regularity and operator bounds. Do not nominate this theorem,its qualitative weakening,an equivalent definition,componentwise reformulation,standard smooth/hard truncation comparison or routine quantitative corollary. Read exact kernel,global/local support,AD scale range,truncation convention,operator norm and BPLI constants from the actual proof. No bounded support,finite total mass,compactness,smooth density,integer lattice or favorable codimension hypothesis may be added to replace its full scope.

Credit EVERY stronger corona,stopping-time,energy,transport,reflectionless,flatness,tangent,measure-decomposition,Carleson or quantitative operation ACTUALLY established by the FULL source and strongest compatible primary proofs,not only the headline. Read operative hypotheses and joint-measure compatibility before using any of these names as descriptions. Standard David-Semmes uniform-rectifiability equivalences,known odd-kernel singular-integral consequences,localization,interpolation,duality and scaling are paid whenever their actual hypotheses compose. A failed naive route does not rule out a stronger compatible known operation.

Distinguish uniform individual-truncation operator bounds from a pointwise maximal truncation conclusion;upper growth from two-sided AD regularity;rectifiability from uniform BPLI;dimension-only existence of quantitative constants from an explicit sharp modulus;one fixed measure from families,weighted/deformed/relative measures or limiting laws;positive Radon data from signed/complex measures;the stated higher-codimension range from endpoint/codimension-one/noninteger variants. Such extensions are not supplied merely by a headline,but must be credited if actually paid in the strongest operative proof. No favorable subset,unpaid lower-density regularization,extra tangent hypothesis or independently reselected measure at different scales may silently replace a proposed full target. All old harmonic-analysis and geometric scopes remain unchanged;paid premises do not reopen protected task namespaces.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are eligible,but an unproved hard target is not a finding. Carry sustained concrete mathematics beyond the first failed shortcut,tracking exact measures/joint laws,normalizations,scale/energy/Carleson budgets and every compatibility interface. Preserve failed attempts and precise residuals. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with the strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history proof extents,versions,access failures,late reads,truncation recovery,false admissions and coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief=header+isolation+body+closed+family+marker+standing
og=set(re.findall(r'\*[^\s,;()]*\*',old));ng=set(re.findall(r'\*[^\s,;()]*\*',brief));assert og<=ng and brief.split(marker,1)[1]==standing
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and hashlib.sha256(d).hexdigest()==x['sha256']
root.mkdir();target.write_text(brief)
prep={'path':target.relative_to(p).as_posix(),'root':root.relative_to(p).as_posix(),
    'bytes':len(brief.encode()),'sha256':hashlib.sha256(brief.encode()).hexdigest(),
    'old_literal_guards':len(og),'new_literal_guards':len(ng),'all_guards_and_standing5570bytes_preserved':True,
    'source_label':'081','catalogue_extent':[135955,137284],'canonical_folders':1,'canonical_descendants':16,
    'canonical_blobs':14,'parent_operative_proof_read':False,'foreign_original_initial_guards_before_creation':True,'direct_completed_originals_count':4}
(o/'brief-preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
args={'clientRequestId':'twenty-20261023-fresh-arithmetic-r162q-codex-astra-r1',
    'target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},
    'mode':'async','role':'research','title':'Arithmetic162q: confirmed higher-codimension Riesz-transform rectifiability discovery','task':brief}
(o/'private/submitted-prompt.json').write_text(json.dumps(args,indent=2)+'\n');print(json.dumps(prep,indent=2))
