#!/usr/bin/env python3
"""Prepare one distinct Source076 family with every inherited exclusion."""
from pathlib import Path
import hashlib
import json
import re

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162k-parent'
old = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162k-brief.txt').read_text()
target = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162l-brief.txt'
root = b / 'fresh-arithmetic-discovery-r162l'
assert not target.exists() and not root.exists()
iso = json.loads((o / 'prospective-isolation-arithmetic162l.json').read_bytes())
assert iso['checked_before_new_root_brief']
for peer in iso['peer_original_initial_briefs']:
    assert hashlib.sha256((p / peer['brief']).read_bytes()).hexdigest() == peer['brief_sha256']
marker = '--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old.split(marker, 1)[1]
assert len(standing.encode()) == 5570
header = old.split('This is ONE NEW DISTINCT Source075 family', 1)[0]
header = header.replace('r162k', 'r162l').replace('confirmed L log L Fourier-convergence operative-proof discovery', 'confirmed real-Littlewood ultraflatness operative-proof discovery')
header += '''This is ONE NEW DISTINCT Source076 family,not a retry of the weighted Fourier endpoint or full4D maximal target. The ENTIRE root/brief/future parent namespace is covered by *arithmetic*r162* in EVERY currently recorded foreign task's ORIGINAL INITIAL brief BEFORE creation. Parent has not queried peer live status,body,findings or activity; recorded metadata is not fresh liveness. Exclude all peer/derivative namespaces. Own162l is excluded from broad history but usable by direct own I/O. Prompt chronology is not OS/perfect isolation or exhaustive clearance.

Arithmetic162k is PREFREEZE/no nominee. Its full weighted modular target retains every A1 weight,every complex LlogL(w)input,every threshold and the entire symmetric Fourier sequence,with requested factor A log(e+B). The compatible source/primary baseline pays A log²(e+B) and the refined bounded-block estimate; no weaker theorem was frozen. Compatible weighted live/Fisher charge and predictable-drift control,or stronger full-input endpoint summation removing one logarithm,remains unpaid. Do not retry,restrict,rename or regrade that target. Earlier full4D maximal target and its same-retained-mass state/velocity/normal-label/recovery/overlap gap remain unchanged. All wholePASS/TECHNICAL zero-count closures and prior frozen/PREFREEZE scopes stay immutable.

'''
isolation = 'Prospective isolation BEFORE FIRST filename traversal' + old.split('Prospective isolation BEFORE FIRST filename traversal', 1)[1].split('Catalogue access, if needed:', 1)[0]
isolation = isolation.replace('\n\nPrune these case-insensitive FULL-PATH substrings', ' *arithmetic*162l* *arithmetic*r162l*\n\nPrune these case-insensitive FULL-PATH substrings', 1)
closed = 'Arithmetic162h remains CLOSED WHOLE-SCOPE' + old.split('Arithmetic162h remains CLOSED WHOLE-SCOPE', 1)[1].split('Your ONE developed family is SOURCE075:', 1)[0]
body = '''Catalogue access,if needed: ONLY direct binary seek/read sources/CONTENTS.md[128445,130739),EXACT Source076 body. Parent decoded only the first two numeric-title strings in one bounded14000-byte window and ONLY076 body. Numeric labels need not be contiguous. Three confirmed folders have41descendants/35blobs plus their three roots. Actual wrappers are build/main.tex,not guessed compiled basenames. Parent read NO source proof body. No child title locator,catalogue scan,extra family,opening or whole-file decoding. Selector failure grants no broader access.

Read FOUR exact COMPLETED originals as narrow direct exceptions,relative to frontier/campaigns/2026-10-14/:
discovery-arithmetic-r162k-parent/assessment.md
fresh-arithmetic-discovery-r162k/packet/FINAL.md
fresh-arithmetic-discovery-r162k/packet/private/RESEARCH.md
fresh-arithmetic-discovery-r162k/packet/private/READING-ISOLATION.md
No containing namespace,linked body or peer status/activity access is admitted. Retain full weighted target,paid baseline,failed repairs and exact residual;do not offer a favorable subclass or renamed retry. All older obligations and dispositions remain unchanged.

'''
family = '''Your ONE developed family is SOURCE076: REAL ULTRAFLAT LITTLEWOOD POLYNOMIALS AND BINARY MERIT FACTORS. All three source manuscripts and EVERY operative upstream proof are stipulated TRUE,including their formerly conjectural conclusions. Do not audit or contradict upstream truth. Validate exact applicability and genuinely new deductions.

Authenticate ALL35 canonical blobs by complete-tree size/Git blob/SHA256,including all READMEs,compiled PDFs and every actual local object. Read the actual three READMEs/wrappers,FULL theorem interfaces,and COMPLETELY all actual operative proofs/ancestors/includes/required companions for the developed construction,plus strongest relevant actual primary proofs and eligible ORIGINAL-history mechanisms BEFORE extended deductions or author drafting. Follow actual nested include directives,not filename inferences. Canonical complete proof reading must not be deferred until verification. Preserve durable understanding and exact extents;recover clipped seams. Hashes,metadata,abstracts,theorem interfaces and another agent's summaries are not proof-body reading.

Confirmed folders/wrappers:
preprints/Ultraflat-real-Littlewood-polynomials-October-5-2026
preprints/Ultraflat-real-Littlewood-polynomials-October-5-2026/build/main.tex
bytes1948;Git blob7ea356ba43f13e66f69be8d46b070db9d20a8b7b.
preprints/Nearly-minimal-maxima-and-positive-minima-of-Littlewood-polynomials-October-5-2026
preprints/Nearly-minimal-maxima-and-positive-minima-of-Littlewood-polynomials-October-5-2026/build/main.tex
bytes1762;Git blobf6b7c151898095628f5e5df5f82ef1f5a8aa084e.
preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026
preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026/build/main.tex
bytes1902;Git blob796dc3a99ad1db31208bdcdc899705ed47c58bba.

The strongest catalogue conclusion is PAID: for EVERY epsilon in(0,1),EVERY sufficiently large integer lengthN admits N consecutive coefficients in{-1,1} with modulus between(1-epsilon)sqrtN and(1+epsilon)sqrtN on the ENTIRE unit circle,including both real endpoints. Signs may be chosen separately at each length. The lower-envelope companion and all-integer-length nearly-minimal maxima/merit-factor consequences are also paid. Binary merit factors tending to infinity and disproof of the stated bounded-factor/fixed-gap conjectures are not new findings. Lean navigation is not an extra theorem or authorization for downstream formal work.

Read exact coefficient,degree/length,normalization,parity,endpoint,error,exceptional-arc,parameter/constant and algorithmic quantifiers in all actual operative proofs. Distinguish independent per-length existence from one coherent infinite sign sequence;all sufficiently large lengths from a subsequence;uniform circle control from Lp/most-arc control;aperiodic from periodic correlations;real signs from arbitrary complex phases or zero coefficients;existence from a specified efficient construction;and asymptotic thresholds from effective uniform rates. Do not infer an explicit rate,simultaneous constraint,common sign choice,conditioning freedom or computational bound from an existential theorem unless the actual proof pays it.

Conversely credit ALL stronger operations supplied by the integrated three-manuscript construction and actual primary/history proofs,including any coefficient freedom,rounding,patching,balancing or quantitative/constructive interfaces genuinely proved there. Ordinary Parseval/Hölder/interpolation,autocorrelation identities,merit-factor conversion,parameter substitutions,finite products/concatenations and source/classical compositions already paid by that construction are not substantial nominees. A naive obstruction or failed shortcut does not rule out a stronger compatible classical operation. Do not audit source truth or use an imagined contradiction with a formerly open problem as research.

After full actual reading,choose and develop ONE DISTINCT fully specified full-scope operation with a CLOSED identifiable nonroutine bridge after the strongest integrated payment. Quantitative,relative,simultaneous,structural,prescribed-data,stability or hypothesis-removal directions are not categorically excluded,but an unproved hard target is not a finding. Carry sustained concrete mathematics through compatibility tests and preserve failed attempts/exact residuals. Do not add a favorable parity/subsequence/coefficient class,discard real endpoints or weaken a full old target as a replacement nominee. Freeze a viable EXACT theorem BEFORE author-proof development;then close every interface and quantifier. If nothing closes,honest PREFREEZE/no nominee with strongest integrated derivation and precise unpaid operation,no weaker substitute,self-grade,count,exhaustion/global-impossibility or priority claim.

Record source/primary/transitive/original-history extents,versions,access failures,late reads,truncation recovery,false admissions/coarse omissions honestly. All protected bodies AND named metadata remain private/local under original rights. Mathematics must dominate proportionate evidence work. Seal only YOUR new exact packet once,with fresh manifest,detached FINAL/MANIFEST/outside REPORT anchors,read-only explicit-anchor verifier and tiny COPIED own-text controls. No inherited manifest over a reduced selection. Artifact checks are not mathematical gates. No nested agents,shared writes,public actions or downstream formal/manuscript/release. Parent alone requests independent correctness and separate contribution reviews of a viable full author proof.

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
    'old_guards_and_standing5570bytes_preserved': True, 'source_label': '076',
    'catalogue_extent': [128445, 130739], 'canonical_folders': 3,
    'canonical_descendants': 41, 'canonical_blobs': 35,
    'parent_operative_proof_read': False, 'foreign_initial_guards_before_creation': True}
(o / 'brief-preparation.json').write_text(json.dumps(prep, indent=2) + '\n')
args = {'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162l-codex-astra-r1',
    'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
        'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
    'mode': 'async', 'role': 'research',
    'title': 'Arithmetic162l: confirmed real-Littlewood ultraflatness operative-proof discovery',
    'task': brief}
(o / 'private/submitted-prompt.json').write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(prep, indent=2))
