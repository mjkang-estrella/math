"""Single final root seal; writes only the three root envelopes, once."""
from pathlib import Path
from datetime import datetime,timezone
import json
from verify import inventory,digest,verify,ENVELOPES
ROOT=Path(__file__).resolve().parent
if any((ROOT/n).exists() for n in ENVELOPES): raise SystemExit('seal exists; refusing repair/reseal')
receipt=json.loads((ROOT/'freeze-receipt.json').read_text())
for name,key in [('H-SCOPE.md','scope_sha256'),('DERIVATION.md','prefreeze_derivation_sha256')]:
 if digest((ROOT/name).read_bytes())!=receipt[key]: raise SystemExit('frozen bytes changed')
report='''# r138 research handoff — author-proof nominee

The proposed proof in AUTHOR-PROOF.md addresses the unchanged full question H retained in I130/I133. For every 4/9<v<1 and 1<c<9v/4, it constructs one complete smooth metric on R3, Euclidean near the origin, with Ric>=0 and AVR=v, and a sequence of strictly increasing integer degrees k_i tending to infinity for which dim H_(k_i)>=c(k_i+1)^2. Each counted function is smooth, entire, real harmonic and has its own finite pointwise polynomial-growth constant at every point. One metric serves the whole sequence. H-SCOPE.md is the exact frozen statement; its bytes and the prefreeze derivation remain unchanged.

The strongest integrated reduction credits Source361's finite retained-double/avoidance operations, rank averaging, exact whole-ball maps, finite graph transforms, and signed scalar matching, together with I130's finite-band construction and I133's geometric scheduling. The proposed additional operation uses terminally nested low spaces at TWO fixed finite cutoffs for each band, matches their finite quotient, and lifts through a lower triangular block with a strictly smaller growth rate. Nonuniform contraction constructs those spaces before local estimates are used. A common product fixed point chooses all controls; finite stage and connector estimates control growth at every radius. No infinite angular matrix inverse, cutoff-uniform gap, normalized exhaustion, or countability slogan is substituted for these steps.

The author draft argues every implication at the frozen scope and is submitted as a full author-proof nominee. The critical interfaces for independent adversarial review are uniform local freezing over arbitrary admitted pasts, nested graph limits, preservation of the signed quotient coefficient, nonuniform stage scheduling/product continuity, and every-prefix growth. No independent correctness or contribution grade is assigned here. The graph transform, quotient algebra, fixed-point theorem and slow-link geometry themselves are classical or credited source operations; substantiality of the integrated operation remains a separate parent review. Parent alone integrates, reviews, and counts.

This is the only selected family. The required r137 Boltzmann originals remain PREFREEZE/no nominee, with their thermal, total-separation and global-class obligations unpaid. All accepted results, R041, old frozen scopes, and other active work remain untouched. This packet does not claim a Boltzmann result or an impossibility theorem for r136.

Authentication uses stipulated pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and the complete 13,223-entry tree SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. The September26 operative sections were read in full before freeze; primary and companion read extents, late readings, unread dependencies, and late-current-original snapshot limits are explicit in the ledgers and READING-LIMITS.md. The initial unpruned path navigation and two history-search false-admission sets are disclosed, not retrospectively cleared. Prospective arithmetic*r109 and t185r144-* additions apply alongside all earlier exclusions. No whole-history, whole-parent, OS-isolation, or worldwide-priority certificate is claimed.

Protected source, primary and history bodies remain private/local under their original rights. All writes were confined to this exclusive root. No git, nested agents, browser UI, publication, upload, contact, formalization, manuscript or release work was performed. Provenance is Codex / GPT-6 Astra / high / default service tier.

MANIFEST.json binds the exact payload and directories; this REPORT, FINAL.json and MANIFEST.json are separate root envelopes. Detached hashes for all three are supplied in the final handoff. verify.py requires those explicit anchors and is read-only. Eight copied integrity controls restored their fixture baseline and left the three copied originals unchanged; they are artifact checks, not mathematical gates or source truth audits.
'''
(ROOT/'REPORT.md').write_text(report)
files,dirs=inventory(ROOT)
manifest={'schema':1,'scope':'exact owned r138 payload; root envelopes excluded','files':files,'directories':dirs}
(ROOT/'MANIFEST.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
anchors={n:digest((ROOT/n).read_bytes()) for n in ['REPORT.md','MANIFEST.json']}
final={'schema':1,'sealed_at_utc':datetime.now(timezone.utc).isoformat(),'status':'full author-proof nominee; independent reviews pending','provenance':'Codex / GPT-6 Astra / high / default service tier','scope_sha256':receipt['scope_sha256'],'prefreeze_derivation_sha256':receipt['prefreeze_derivation_sha256'],'author_proof_sha256':digest((ROOT/'AUTHOR-PROOF.md').read_bytes()),'manifest_sha256':anchors['MANIFEST.json'],'report_sha256':anchors['REPORT.md'],'mathematical_gates_assigned':False,'parent_alone_integrates_reviews_counts':True}
(ROOT/'FINAL.json').write_text(json.dumps(final,sort_keys=True,indent=2)+'\n')
anchors['FINAL.json']=digest((ROOT/'FINAL.json').read_bytes())
print(json.dumps({'detached_anchors':anchors,'verification':verify(ROOT,anchors)},indent=2))
