#!/usr/bin/env python3
"""Prepare one distinct Source078 task, preserving inherited isolation/standing rules."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-contribution-r1-parent'
old = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162m-brief.txt').read_text()
root = b / 'fresh-arithmetic-discovery-r162n'
target = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162n-brief.txt'
assert not root.exists() and not target.exists()
iso = json.loads((o / 'prospective-isolation-arithmetic162n.json').read_bytes())
assert iso['checked_before_new_root_brief']
for x in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p / x['brief']).read_bytes()).hexdigest() == x['brief_sha256']
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old.split(marker, 1)[1]
assert len(standing.encode()) == 5570
header = old.split('This is ONE NEW DISTINCT Source077 family', 1)[0]
header = header.replace('r162m', 'r162n').replace('confirmed positive-curvature Fourier-restriction operative-proof discovery', 'confirmed three-dimensional Bochner-Riesz operative-proof discovery')
header += '''This is ONE NEW DISTINCT Source078 family. The ENTIRE root/brief/future parent namespace was checked against *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Recorded status is not fresh liveness. Parent queried no foreign live status,body,findings or activity. Own162n is excluded from broad history but direct own I/O is authorized. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162m is CLOSED WHOLE-SCOPE PASS/TECHNICAL, contribution condition DISCHARGED, ZERO count. Its entire frozen theorem covers every rough complex normalized Lp extremizing sequence for every finite p>3 on every stipulated compact positive-curvature surface,including smooth boundary,strong compactness modulo plus-sign modulations,attainment,and qualitative stability relative to the entire extremizer set. The full compatible classical derivation pays the stronger L3-to-Lq source interface,two-output-exponent extraction from original weakLp profiles,localized Hilbert square mass,strict complex plus/minus convexity,analytic injectivity,uniform convexity and modulation invariance. No desired-grade retry,renaming,downstream work or narrower replacement. Exact completed comparison files below explain the mechanism; they authorize no namespace traversal.

Arithmetic162l's full critical-prefix target fixes c=1/100 independently of epsilon,EVERY word of floor(c sqrt(N)) and EVERY sufficiently large integerN,with arbitrarily small relative error on the ENTIRE circle. Simultaneous sharp coefficient cube and uniform truncation for the SAME Schur interpolant remain unpaid. Arithmetic162k's full A log(e+B) weighted Fourier endpoint remains unproved;A log²(e+B) is paid. Full4D maximal,same-retained-mass state/velocity/normal-label/recovery/overlap obligations remain unchanged. All earlier frozen/PREFREEZE scopes and closed dispositions remain immutable.

'''
isolation = 'Prospective isolation BEFORE FIRST filename traversal' + old.split('Prospective isolation BEFORE FIRST filename traversal', 1)[1].split('Catalogue access,if needed:', 1)[0]
isolation = isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings', ' *arithmetic*162n* *arithmetic*r162n*\n\nPrune these case-insensitive FULL-PATH substrings', 1)
closed = 'Arithmetic162h remains CLOSED WHOLE-SCOPE' + old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE', 1)[1].split('Your ONE developed family is SOURCE077:', 1)[0]
direct = json.loads((o / 'private/next-direct-originals.json').read_bytes())
exceptions = '\n'.join(x['path'].removeprefix('frontier/campaigns/2026-10-14/') for x in direct)
body = '''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[132535,133395),EXACT Source078 body. Parent decoded ONLY the first TWO numeric-title strings in ONE bounded14000-byte navigation window and ONLY078 body. Two initial heading-regex failures decoded nothing;the previously authorized077 title format was reread before the correct numeric-bold locator. Labels need not be contiguous. One confirmed folder has30descendants/21blobs plus its root. Actual wrapper is build/paper.tex. Parent read NO source proof body. No child title locator,catalogue screen,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read these SEVEN exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
''' + exceptions + '''
No containing namespace,linked body,peer status/activity or other review access is admitted. The first four record the full closed162m technical comparison. The last three record the completed prior positive-order Bochner-Riesz radius-variation application: it reduced to stipulated source/classical operations,with no additional nonroutine result. Preserve its scope/disposition and primary access limitations. No favorable variation exponent or rephrasing may be nominated as new without a distinct closed nonroutine operation. All other old scope archives remain unchanged.

'''
family = '''Your ONE developed family is SOURCE078: THE THREE-DIMENSIONAL BOCHNER-RIESZ CONJECTURE. The pinned manuscript and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural results. Validate exact applicability and genuinely new deductions;do not audit upstream truth.

Authenticate ALL21 canonical blobs against complete-tree size/Git blob/SHA256,including README,compiled PDF,all actual local objects and vendor typography. Read actual README/wrapper,FULL theorem interfaces,and COMPLETELY all operative proofs/ancestors/includes/required companions supporting the developed operation,strongest relevant ACTUAL primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes,not filename inferences. Complete canonical proof reading must not be deferred until verification. Distinguish theorem/proof text from compiled/typography authentication. Keep durable mathematical understanding and exact read extents;recover clipped seams. Metadata,interfaces,hashes and others' reading ledgers are not proof-body reading.

Confirmed folder/wrapper:
preprints/Bochner-Riesz-Multipliers-in-Three-Dimensions-September-24-2026
preprints/Bochner-Riesz-Multipliers-in-Three-Dimensions-September-24-2026/build/paper.tex
bytes2429;Git blob45ee5947f2326543b55ee386d0b030cd560f6423.

The ENTIRE strict-order theorem is PAID: the Bochner-Riesz multiplier (1-|xi|²)_+^delta is bounded on Lp(R3) for EVERY1<=p<=infinity whenever delta>max{3|1/p-1/2|-1/2,0}. In particular L3 boundedness for EVERY positive order,interpolation,duality,scaling and their exact operative quantitative/conditional consequences are paid. Do not nominate that theorem,a parameter substitution,its routine dual/interpolated form,or the already-paid positive-order radius-variation application. Do not assume an endpoint at equality,delta=0,uniform constants asdelta->0,arbitrary weights/nonradial symbols,variable coefficients,simultaneous radii,vector or multiple-phase estimates merely from the headline. Conversely credit EVERY stronger estimate,finite-array operation,entropy/projection/rate-transfer/classical-closure/packet-composition/repayment interface actually established by the FULL proof and strongest compatible primary operations. A failed naive shortcut does not rule out a stronger paid compatible composition.

Read exact Fourier normalization,radius and physical scaling,order/exponent constraints,symbol/support regularity,uniformity/dependence,weight/conditioning hypotheses and all local-to-global interfaces from the full actual proof. Distinguish a fixed strict order and exponent from uniform critical limits,single multipliers from maximal/variation or joint estimates,Euclidean radial geometry from other surfaces/operators,and source proof machinery from any proposed new application. Do not insert smooth data,favorable frequency support,a restricted radius set,extra curvature,regular laws or transversality to replace a full target. Existing Kakeya/restriction/weighted Fourier and radius-variation scopes keep their exact obligations; a paid premise does not reopen protected tasks.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are eligible,but an unproved hard target is not a finding. Carry sustained concrete mathematics beyond the first failed shortcut,tracking joint laws,normalizations,rate/entropy/scale budgets and every compatibility interface. Preserve failed attempts and precise residuals. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with the strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history proof extents,versions,access failures,late reads,truncation recovery,false admissions and coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone commissions independent correctness and separate substantial-contribution reviews of a viable full author proof.

'''
brief = header + isolation + body + closed + family + marker + standing
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
new_guards = set(re.findall(r'\*[^\s,;()]*\*', brief))
assert old_guards <= new_guards and brief.split(marker, 1)[1] == standing
for x in direct:
    data = (p / x['path']).read_bytes()
    assert len(data) == x['bytes'] and hashlib.sha256(data).hexdigest() == x['sha256']
root.mkdir()
target.write_text(brief)
prep = {'path': str(target), 'root': str(root), 'bytes': len(brief.encode()),
    'sha256': hashlib.sha256(brief.encode()).hexdigest(), 'old_literal_guards': len(old_guards),
    'new_literal_guards': len(new_guards), 'old_guards_and_standing5570bytes_preserved': True,
    'source_label': '078', 'catalogue_extent': [132535,133395],
    'canonical_folders': 1, 'canonical_descendants': 30, 'canonical_blobs': 21,
    'parent_operative_proof_read': False, 'foreign_initial_guards_before_creation': True,
    'direct_completed_originals_count': len(direct)}
(o / 'brief-preparation.json').write_text(json.dumps(prep, indent=2)+'\n')
args = {'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162n-codex-astra-r1',
    'target': {'providerInstanceId':'codex','model':'gpt-6-astra',
        'options':{'reasoningEffort':'high','serviceTier':'default'}},
    'mode':'async','role':'research',
    'title':'Arithmetic162n: confirmed three-dimensional Bochner-Riesz operative-proof discovery',
    'task':brief}
(o / 'private/submitted-prompt.json').write_text(json.dumps(args, indent=2)+'\n')
print(json.dumps({k:v for k,v in prep.items() if k!='direct_completed_originals'}, indent=2))
