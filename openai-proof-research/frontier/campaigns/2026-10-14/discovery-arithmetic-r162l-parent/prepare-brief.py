#!/usr/bin/env python3
"""Prepare Source077, retaining all inherited guards and the standing brief."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162l-parent'
old = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162l-brief.txt').read_text()
target = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162m-brief.txt'
root = b / 'fresh-arithmetic-discovery-r162m'
assert not target.exists() and not root.exists()
iso = json.loads((o / 'prospective-isolation-arithmetic162m.json').read_bytes())
assert iso['checked_before_new_root_brief']
for peer in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p / peer['brief']).read_bytes()).hexdigest() == peer['brief_sha256']
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old.split(marker, 1)[1]
assert len(standing.encode()) == 5570
header = old.split('This is ONE NEW DISTINCT Source076 family', 1)[0]
header = header.replace('r162l', 'r162m').replace('confirmed real-Littlewood ultraflatness operative-proof discovery', 'confirmed positive-curvature Fourier-restriction operative-proof discovery')
header += '''This is ONE NEW DISTINCT Source077 family,not a retry of critical-prefix completion,weighted Fourier endpoint or full4D maximal targets. The ENTIRE root/brief/future parent namespace is covered by *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Parent queried no peer live status,body,findings or activity; recorded metadata is not fresh liveness. Exclude all peer/derivative namespaces. Own162m is excluded from broad history but usable through direct own I/O. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162l is PREFREEZE/no nominee. Its full critical-prefix target fixes c=1/100 independently of epsilon,prescribing EVERY word of length floor(c sqrt(N)) for EVERY sufficiently large integerN while retaining arbitrarily small relative ultraflat error on the ENTIRE circle. The classical Schur rational completion and paid saturated-coordinate rounder do not close simultaneous sharp coefficient-cube and uniform truncation bounds for the SAME source-compatible interpolant. No smaller c(epsilon),favorable word,subsequence or weaker nominee is substituted. Canonical reading completed; inaccessible packing and other transitive-primary gaps remain disclosed. Preserve this full target and every prior scope/disposition.

Arithmetic162k's full weighted A log(e+B) endpoint remains unproved; its A log²(e+B) and refined bounded-block baselines are paid. Compatible weighted live/Fisher and predictable-drift control or stronger full-input endpoint summation remains unpaid. The prior full4D maximal target and its same-retained-mass state/velocity/normal-label/recovery/overlap gap remain unchanged. All wholePASS/TECHNICAL zero-count closures and earlier frozen/PREFREEZE scopes stay immutable. No desired-grade retry or worldwide-impossibility inference.

'''
isolation = 'Prospective isolation BEFORE FIRST filename traversal' + old.split('Prospective isolation BEFORE FIRST filename traversal', 1)[1].split('Catalogue access,if needed:', 1)[0]
isolation = isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings', ' *arithmetic*162m* *arithmetic*r162m*\n\nPrune these case-insensitive FULL-PATH substrings', 1)
closed = 'Arithmetic162h remains CLOSED WHOLE-SCOPE' + old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE', 1)[1].split('Your ONE developed family is SOURCE076:', 1)[0]
body = '''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[130739,132535),EXACT Source077 body. Parent decoded only the first two numeric-title strings in one bounded14000-byte window and ONLY077 body. Labels need not be contiguous. Two confirmed folders have35descendants/29blobs plus their two roots. Actual wrappers are build/paper.tex. Parent read NO source proof body. No child title locator,catalogue scan,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read FOUR exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
discovery-arithmetic-r162l-parent/assessment.md
fresh-arithmetic-discovery-r162l/packet/FINAL.md
fresh-arithmetic-discovery-r162l/packet/private/PREFREEZE-CALCULATIONS.md
fresh-arithmetic-discovery-r162l/packet/private/READING-ISOLATION.md
No containing namespace,linked body or peer status/activity access is admitted. Retain the full critical-prefix target,Schur compatibility reduction,paid rounder and simultaneous unpaid bounds. No renamed retry or favorable subclass. All older obligations/dispositions remain unchanged.

'''
family = '''Your ONE developed family is SOURCE077: FOURIER RESTRICTION FOR POSITIVELY CURVED SURFACES IN THREE DIMENSIONS. Both source manuscripts and EVERY operative upstream proof are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and genuinely new deductions;do not audit source truth.

Authenticate ALL29 canonical blobs against complete-tree size/Git blob/SHA256,including READMEs,compiled PDFs and every actual local object. Read both actual READMEs/wrappers,FULL theorem interfaces,and COMPLETELY all operative proofs/ancestors/includes/required companions supporting the developed operation,strongest relevant actual primary proof operations and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested includes,not filename inferences. Canonical complete proof reading must not be deferred until final verification. Keep durable mathematical understanding and exact extents;recover clipped seams. Paths,abstracts,interfaces,hashes and another agent's summaries are not proof-body reading.

Confirmed folders/wrappers:
preprints/Diagonal-Fourier-extension-for-positively-curved-surfaces-in-three-dimensions-September-24-2026
preprints/Diagonal-Fourier-extension-for-positively-curved-surfaces-in-three-dimensions-September-24-2026/build/paper.tex
bytes2230;Git blob14a08d7ee2c285216aa854f642c50402317cc151.
preprints/Elliptic-capacity-propagation-and-Fourier-restriction-to-the-sphere-September-24-2026
preprints/Elliptic-capacity-propagation-and-Fourier-restriction-to-the-sphere-September-24-2026/build/paper.tex
bytes543;Git blob9076e12535ee842fa158c7682b0908abb56d764d.

The strongest catalogue conclusion is PAID: for EVERY compact smooth positively curved surfaceSigma inR3,including smooth boundary,the extension operator maps Lp(Sigma) boundedly to Lp(R3) for EVERY3<p<infinity. The bounded-data sphere theorem L-infinity(S2)->Lp(R3),p>3,and its stated sharp threshold are paid. The compact-paraboloid consequence already yields free Schrodinger local smoothing in two spatial dimensions for everyp>3 and Sobolev orders>2-6/p. These headlines AND EVERY actual operative proof operation are paid input,not nominees.

Read exact curvature,geometry/regularity,chart/support,boundary,scale/epsilon,measure,exponent and constant hypotheses from BOTH full proofs. Distinguish one fixed surface from uniform families,positive curvature from degenerate/mixed signature,constant-coefficient extension from variable phases,bounded data from diagonal Lp,global norm from localized scale estimates,strict p>3 from endpoints,and free local smoothing from variable-coefficient or maximal/variation conclusions. No uniform derivative/curvature dependence,endpoint,oscillatory parameter,weight,vector/multiple-phase or relative transfer follows merely from the headline. Conversely credit every stronger quantitative/weighted/conditional/capacity/propagation operation actually supplied by the strongest integrated proof and primary antecedents.

Standard duality/interpolation,parabolic rescaling,partition-of-unity,epsilon removal,finite chart changes and already-paid source/classical compositions are not substantial nominees. A naive failed bridge does not rule out a stronger compatible known operation. Do not add smooth input,compact support beyond the actual problem,a favorable chart,regular direction law,transversality or stronger curvature to replace a proposed full target. Earlier oscillatory/Kakeya/sparse-sampling targets retain their scopes; source use of their paid hypotheses does not reopen protected tasks or authorize namespace inspection.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,weighted,stability,uniform-family,hypothesis-removal and other directions are not categorically excluded,but an unproved hard target is not a finding. Carry sustained concrete mathematics beyond a first failed shortcut,tracking exact joint distributions,physical/Fourier normalization,scale/entropy/capacity budgets and all compatibility interfaces. Preserve failed attempts and precise residuals. Freeze a viable EXACT theorem BEFORE author-proof development;then close every quantifier/interface. If nothing closes,honest PREFREEZE/no nominee with strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record actual source/primary/transitive/original-history extents,versions,access failures,late reads,truncation recovery,false admissions/coarse omissions honestly. Protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone requests independent correctness and separate contribution reviews of a viable full author proof.

'''
brief = header + isolation + body + closed + family + marker + standing
old_guards = set(re.findall(r'\*[^\s,;()]*\*', old))
new_guards = set(re.findall(r'\*[^\s,;()]*\*', brief))
assert old_guards <= new_guards and brief.split(marker, 1)[1] == standing
root.mkdir()
target.write_text(brief)
prep = {'path': target.relative_to(p).as_posix(), 'root': root.relative_to(p).as_posix(),
    'bytes': len(brief.encode()), 'sha256': hashlib.sha256(brief.encode()).hexdigest(),
    'old_literal_guards': len(old_guards), 'new_literal_guards': len(new_guards),
    'old_guards_and_standing5570bytes_preserved': True, 'source_label': '077',
    'catalogue_extent': [130739, 132535], 'canonical_folders': 2,
    'canonical_descendants': 35, 'canonical_blobs': 29,
    'parent_operative_proof_read': False, 'foreign_initial_guards_before_creation': True}
(o / 'brief-preparation.json').write_text(json.dumps(prep, indent=2) + '\n')
args = {'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162m-codex-astra-r1',
    'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
        'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
    'mode': 'async', 'role': 'research',
    'title': 'Arithmetic162m: confirmed positive-curvature Fourier-restriction operative-proof discovery',
    'task': brief}
(o / 'private/submitted-prompt.json').write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(prep, indent=2))
