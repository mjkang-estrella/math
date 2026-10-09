#!/usr/bin/env python3
"""Verify frozen I38 artifacts and exact diagnostics without refreshing a seal.

Only generated output: I38 experiment directory/verification.json.
Shared mutable ledgers may drift; immutable dependencies may not.
This is an integrity/finite-algebra verifier, not an independent proof review.
"""
import datetime
import json
from pathlib import Path
import sys
from audit import ROOT, S, CORPUS, sha, audit_corpus
from diagnostics import exact_checks, floating_checks

E = Path(__file__).resolve().parent


def main():
    out = {'run_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Artifact integrity, full corpus search reconstruction and finite algebra; not an independent mathematical proof/significance review.','mutable_shared_ledger_drift':[],'immutable_dependency_errors':[]}
    try:
        seal = json.loads((S/'artifact-seal.json').read_text())
        for f in seal['files']:
            data = (ROOT/f['path']).read_bytes()
            assert len(data) == f['bytes'] and sha(data) == f['sha256'], 'Owned artifact drift: '+f['path']
        out['sealed_artifacts'] = len(seal['files'])
        for f in json.loads((S/'input-manifest.json').read_text()):
            frozen = ROOT/f['frozen']
            assert sha(frozen.read_bytes()) == f['sha256'], 'Frozen input drift: '+str(frozen)
            p = ROOT/f['path']
            different = not p.exists() or sha(p.read_bytes()) != f['sha256']
            if different and f['mutable']:
                out['mutable_shared_ledger_drift'].append(f['path'])
            elif different:
                raise AssertionError('Immutable live input drift: '+f['path'])
        for f in json.loads((S/'external-dependencies.json').read_text()):
            assert sha((ROOT/f['path']).read_bytes()) == f['sha256'], 'External immutable manifest drift: '+f['path']
        out['corpus'] = audit_corpus()
        for f in json.loads((S/'pinned-manifest.json').read_text()):
            assert sha((CORPUS/f['path']).read_bytes()) == f['sha256'], 'Selected proof dependency drift: '+f['path']
            assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+f['path'] in f['url']
        for f in json.loads((S/'read-passages.json').read_text()):
            data = (ROOT/f['path']).read_bytes()
            assert sha(data) == f['sha256'], 'Read source drift: '+f['path']
            lines = data.decode('utf-8').split('\n')
            for part in f['passages']:
                excerpt = '\n'.join(lines[part['first_line']-1:part['last_line']])
                assert sha(excerpt.encode()) == part['sha256'], 'Passage drift: '+f['path']
                assert excerpt.startswith(part['opening_anchor'])
        n, failures = 0, []
        for p in sorted((S/'literature').glob('*manifest.json')):
            for f in json.loads(p.read_text()):
                data = (S/'literature'/f['name']).read_bytes()
                assert sha(data) == f['sha256'] and len(data) == f['bytes'], 'Primary response drift: '+f['name']
                assert data.startswith(b'%PDF') == f['pdf'], 'Primary response format drift: '+f['name']
                assert 'request' in f and 'headers' in f and 'retrieved_utc' in f
                n += 1
                if f['status'] != 200:
                    failures.append({'name':f['name'],'status':f['status'],'used_as_proof_input':False})
        out['primary_responses_checked'] = n
        out['retained_primary_failures'] = failures
        recorded = json.loads((E/'diagnostics-record.json').read_text())
        current = exact_checks()
        assert current == recorded['exact_checks'], 'Exact diagnostic mismatch'
        out['exact_diagnostics_passed'] = len(current)
        floats = floating_checks()
        assert len(floats) == len(recorded['floating_activation'])
        for f, old in zip(floats,recorded['floating_activation']):
            assert f['extra_labels'] == old['extra_labels'] and f['tail_energy'] == old['tail_energy']
            assert abs(f['activation_over_energy_3_over_2']-old['activation_over_energy_3_over_2']) < 2e-9
        out['noncertified_quadrature_rows_reproduced'] = len(floats)
        out['status'] = 'PASS'
    except Exception as exc:
        out['status'] = 'FAIL'
        out['immutable_dependency_errors'].append(str(exc))
    (E/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
    return 0 if out['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
