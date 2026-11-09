"""Write flat-bindings.json: flat immutable external refs (no copies). Paths relative to lanes/.
Usage (from lane dir): python3 -I -B scripts/bind.py"""
import hashlib, json, os, datetime
LANES = os.path.abspath('..')
REFS = [
 ('intake_manifest', 'root-mathdb-curvature-review-intake-r617/manifest.json'),
 ('intake_receipt', 'root-mathdb-curvature-review-intake-r617/verification-receipt.json'),
 ('intake_assignment', 'root-mathdb-curvature-review-intake-r617/focused-assignment.json'),
 ('intake_decision', 'root-mathdb-curvature-review-intake-r617/DECISION.md'),
 ('intake_adjudications', 'root-mathdb-curvature-review-intake-r617/adjudications.json'),
 ('authority_manifest', 'root-mathdb-breadth-intake-r619/manifest.json'),
 ('authority_receipt', 'root-mathdb-breadth-intake-r619/verification-receipt.json'),
 ('authority_assignment', 'root-mathdb-breadth-intake-r619/focused-assignment.json'),
 ('authority_decision', 'root-mathdb-breadth-intake-r619/DECISION.md'),
 ('authority_adjudications', 'root-mathdb-breadth-intake-r619/adjudications.json'),
 ('candidate_proposals_frozen', 'root-mathdb-curvature-review-intake-r617/frozen/claude-mathdb-primary-qualified-breadth-r602/proposals.json'),
 ('candidate_proposals_original', 'claude-mathdb-primary-qualified-breadth-r602/proposals.json'),
 ('mathdb_record_frozen', 'root-mathdb-curvature-review-intake-r617/frozen/claude-mathdb-primary-qualified-breadth-r602/assigned-records.json'),
 ('candidate_cached_brt_pdf', 'claude-mathdb-primary-qualified-breadth-r602/fetched/arxiv-pdf/1802.01952v2.pdf'),
 ('candidate_cached_bly_pdf', 'claude-mathdb-primary-qualified-breadth-r602/fetched/arxiv-pdf/2103.00941v2.pdf'),
 ('exclusions_r304_manifest', 'root-mathdb-accepted-exclusions-r304/manifest.json'),
 ('exclusions_r304', 'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'),
 ('cayley_r363_manifest', 'root-mathdb-cayley-review-intake-r363/manifest.json'),
 ('cayley_r363_decision', 'root-mathdb-cayley-review-intake-r363/DECISION.md'),
 ('helper_guard', 'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),
 ('campaign_agents', '../AGENTS.md'),
 ('repo_agents', '../../../../../AGENTS.md'),
]
out = {'base': 'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes',
       'bound_utc': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
       'refs': []}
for role, p in REFS:
    b = open(os.path.join(LANES, p), 'rb').read()
    out['refs'].append({'role': role, 'path': p, 'size': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
json.dump(out, open('flat-bindings.json', 'w'), indent=1)
print(len(out['refs']))
