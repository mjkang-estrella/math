"""Reconcile frozen corpus IDs; no mathematical statements are evaluated."""
from pathlib import Path
from collections import Counter
import json

root = Path(__file__).resolve().parent
index = json.loads((root/'frozen/accepted-exclusions.json').read_text())
accepted = {}
for family in index['families']:
    for link in family.get('record_associations', []):
        accepted.setdefault(link['mathdb_id'], []).append({
            'family':family['number'], 'relation':link['relation'],
            'scope':family.get('scope','')})
seen = set()
duplicates = []
malformed = []
matches = []
chunks = []
completeness = Counter()
retrieval = Counter()
status = Counter()
empty = 0
rows = 0
for p in sorted((root/'frozen').glob('mathdb-normalized-chunk-*.jsonl')):
    chunk_rows = 0
    with p.open() as f:
        for line_no, line in enumerate(f, 1):
            rows += 1
            chunk_rows += 1
            try:
                r = json.loads(line)
                i = r['mathdb_id']
                assert type(i) is int and i > 0
            except (ValueError, KeyError, AssertionError, TypeError) as exc:
                malformed.append({'file':p.name,'line':line_no,'error':str(exc)})
                continue
            if i in seen:
                duplicates.append({'mathdb_id':i,'file':p.name,'line':line_no})
            seen.add(i)
            completeness[str(r.get('statement_completeness'))] += 1
            retrieval[str(r.get('retrieval_source'))] += 1
            status[str(r.get('status'))] += 1
            empty += not bool(str(r.get('statement') or '').strip())
            if i in accepted:
                matches.append({'mathdb_id':i,'url':r.get('canonical_url'),
                                'file':p.name,'line':line_no,
                                'accepted_associations':accepted[i],
                                'disposition':'requires literal scope comparison; '
                                              'not an automatic whole-record exclusion'})
    chunks.append({'file':p.name,'rows':chunk_rows})
result = dict(scope='Point-in-time copy of unfinished inventory output; '
                    'not a completed handback or verified full live corpus',
              rows=rows, distinct_ids=len(seen), duplicate_rows=len(duplicates),
              malformed_rows=len(malformed), empty_statements=empty,
              submitted_statement_completeness=dict(completeness),
              retrieval_sources=dict(retrieval), submitted_status=dict(status),
              accepted_associated_ids_found=sorted(accepted.keys() & seen),
              accepted_associated_ids_missing=sorted(accepted.keys() - seen),
              root_technical_statement_reviews=0,
              root_primary_body_reviews=0, credit_added=0, chunks=chunks)
for name, data in [('reconciliation.json',result),('duplicates.json',duplicates),
                   ('malformed.json',malformed),('accepted-id-matches.json',matches),
                   ('available-record-ids.json',sorted(seen))]:
    (root/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'chunks','submitted_status'}},indent=2))
