"""Offline dispatch checks, not mathematical or novelty adjudication.

Usage: python3 -B intake.py accepted-exclusions.json proposals.json
Input proposals is a list of hypothesis rows. Output is deterministic JSON.
Missing data stays missing; this never turns an open label into clearance.
"""
import json
import sys


def intake(index, rows):
    associations = {}
    for family in index['families']:
        for link in family.get('record_associations', []):
            associations.setdefault(str(link['mathdb_id']), []).append({
                'family': family['number'], 'scope': family.get('scope', ''),
                'relation': link['relation']})
    seen = set()
    result = []
    required = ('mathdb_id', 'source_url', 'literal_statement',
                'full_statement_evidence', 'source_scope_evidence',
                'mechanism', 'decisive_next_calculation',
                'certificate_size_estimate', 'formal_dependencies',
                'prior_screen', 'adaptation_objection')
    for row in rows:
        reasons = []
        missing = [key for key in required if not row.get(key)]
        if missing:
            reasons.append({'missing_fields': missing})
        statement = ' '.join(str(row.get('literal_statement', '')).split())
        key = (str(row.get('mathdb_id', '')), statement)
        if key in seen:
            reasons.append('duplicate ID and literal statement in this intake')
        seen.add(key)
        if row.get('statement_review') != 'full_statement':
            reasons.append('excerpt, metadata or unreviewed statement is insufficient')
        if row.get('source_review') != 'primary_body':
            reasons.append('primary source-body scope needs review before solving')
        hits = associations.get(key[0], [])
        if hits and not row.get('accepted_scope_comparison'):
            reasons.append('associated accepted family requires literal scope comparison')
        if row.get('disposition') in ('publicly_resolved', 'accepted_duplicate',
                                      'routine_adaptation', 'parked'):
            reasons.append('retired or parked by submitted disposition')
        result.append({'mathdb_id': row.get('mathdb_id'),
                       'hypothesis': statement,
                       'dispatch': 'needs_information_or_adjudication' if reasons
                                   else 'ready_for_orchestrator_selection',
                       'reasons': reasons, 'accepted_family_associations': hits})
    return {'schema_version': 1, 'proposal_rows': len(rows),
            'distinct_id_statement_pairs': len(seen),
            'accepted_credit_added': 0,
            'qualification': 'Dispatch metadata only. No mathematical, novelty, '
                             'substantive, formal or acceptance gate is certified.',
            'proposals': result}


if __name__ == '__main__':
    with open(sys.argv[1]) as handle:
        index = json.load(handle)
    with open(sys.argv[2]) as handle:
        rows = json.load(handle)
    print(json.dumps(intake(index, rows), indent=2, sort_keys=True))
