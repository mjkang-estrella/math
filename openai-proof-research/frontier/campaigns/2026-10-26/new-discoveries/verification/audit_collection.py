#!/usr/bin/env python3
"""Read-only integrity/coverage audit of every accepted proof packet.

This does not certify novelty or repeat independent mathematical review.
It checks that the accepted evidence still exists and binds the current bytes.
"""
from pathlib import Path
import hashlib
import json
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    ledger = json.loads((ROOT/'ledger.json').read_text())
    results=[]
    assert len(ledger['accepted'])==ledger['discovery_count']
    assert [x['number'] for x in ledger['accepted']]==list(range(1,ledger['discovery_count']+1))
    assert sum(x['discovery_count_credit'] for x in ledger['accepted'])==ledger['discovery_count']
    assert ledger['historical_count_credit']==0
    for entry in ledger['accepted']:
        number=entry['number']; candidate=ROOT/entry['path'];slug=candidate.name
        failures=[];notes=[]
        packet=ROOT/entry['packet']
        if not packet.exists():failures.append('packet missing')
        if failures:
            results.append({'number':number,'status':'FAIL','failures':failures});continue
        if sha(packet.read_bytes())!=entry['packet_sha256']:failures.append('packet hash differs from ledger')
        with zipfile.ZipFile(packet) as archive:
            if archive.testzip() is not None:failures.append('archive CRC failure')
            members=archive.namelist()
            manifest_names=[n for n in members if Path(n).name in ['MANIFEST.json','MANIFEST.sha256']]
            assert len(manifest_names)==1
            manifest_name=manifest_names[0];prefix=manifest_name.rsplit('/',1)[0]+'/'
            if manifest_name.endswith('.json'):
                manifest=json.loads(archive.read(manifest_name))
            else:
                manifest={line[66:]:line[:64] for line in archive.read(manifest_name).decode().splitlines() if line}
            if set(members)!={prefix+n for n in manifest}|{manifest_name}:
                failures.append('archive members differ from payload manifest')
            for name,digest in manifest.items():
                if sha(archive.read(prefix+name))!=digest:failures.append('archive manifest hash: '+name)
                path=candidate/name
                if not path.exists() or sha(path.read_bytes())!=digest:
                    failures.append('current canonical file differs from archive: '+name)
            config=json.loads(archive.read(prefix+'candidate.json'))
            module_names=[x['module'] for x in config['modules']]
            for module in module_names:
                source=archive.read(prefix+'formal/'+module+'.lean').decode()
                if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source):
                    failures.append('forbidden proof token: '+module)
            audit_name=prefix+'verification/parent-audit.json'
            if audit_name not in members:audit_name=prefix+'verification/audit.json'
            independent_name=prefix+'verification/independent-audit.json'
            audit_bytes=archive.read(audit_name);audit=json.loads(audit_bytes)
            independent_bytes=archive.read(independent_name)
            independent=json.loads(independent_bytes)
            differences=[key for key in sorted(set(audit)|set(independent))
                         if audit.get(key)!=independent.get(key)]
            # Early independent reviewers recorded a dependency-build path and
            # different prose, and listed fewer headline endpoints. Their full
            # compiled declaration inventory and source hashes must still agree.
            if set(differences)-{'qualification','dependency_build','main_theorems'}:
                failures.append('parent/independent proof evidence mismatch')
            for key in ['status','compiler','modules','declarations','inventory','axioms']:
                if audit.get(key)!=independent.get(key):
                    failures.append('parent/independent core receipt mismatch: '+key)
            if not set(independent['main_theorems'])<=set(independent['inventory']):
                failures.append('independent headline endpoint absent from checked inventory')
            if differences:notes.append('Historical independent receipt metadata differs: '+', '.join(differences)+
                '; all compiled source hashes, types/axiom inventory, compiler and counts agree.')
            if audit['status']!='PASS' or audit['declarations']!=entry['formal_declarations']:
                failures.append('receipt result/count mismatch')
            if set(audit['axioms'])-ALLOWED:failures.append('nonstandard proof dependencies')
            if [Path(x['path']).stem for x in audit['modules']]!=module_names:
                failures.append('receipt modules mismatch')
            for module in audit['modules']:
                if sha(archive.read(prefix+module['path']))!=module['sha256']:
                    failures.append('receipt/formal source hash mismatch: '+module['path'])
            if not set(config['main_theorems'])<=set(audit['inventory']):
                failures.append('endpoint missing from inspected receipt inventory')
            reviews=[n for n in manifest if n.startswith('reviews/') and n.endswith('.md')
                     and ('independent' in n or 'final' in n)]
            if not reviews:failures.append('independent/final review evidence missing')
            if not archive.read(prefix+'paper.pdf').startswith(b'%PDF-'):
                failures.append('paper PDF invalid signature')
            if 'sources/' not in '\n'.join(manifest):failures.append('no retained source evidence')
            receipt_sha=sha(audit_bytes)
            # Select a retained extracted run only when its receipt and complete
            # payload match this exact accepted archive, not a superseded run.
            replay_matches=[]
            for extraction in (ROOT/'build').glob(slug+'-packet-audit*'):
                for actual in extraction.glob('*/build/verified/audit.json'):
                    if actual.read_bytes()!=audit_bytes:continue
                    extracted=actual.parents[2]
                    if not all((extracted/n).exists() and sha((extracted/n).read_bytes())==h
                               for n,h in manifest.items()):continue
                    checks=actual.parent/'Checks.log'
                    if not checks.exists():continue
                    content=checks.read_text()
                    reports=re.findall(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",content,re.S)
                    if sorted(n for n,_ in reports)!=sorted(audit['inventory']):continue
                    if any(not (actual.parent/(m+'.log')).exists() or
                           (actual.parent/(m+'.log')).stat().st_size for m in module_names):continue
                    replay_matches.append(str(actual.relative_to(ROOT)))
            if not replay_matches:failures.append('no matching complete extracted replay retained')
            results.append({'number':number,'title':entry['title'],
                'status':'PASS' if not failures else 'FAIL','failures':failures,
                'packet':entry['packet'],'packet_sha256':sha(packet.read_bytes()),
                'payload_files':len(manifest),'formal_declarations':audit['declarations'],
                'formal_modules':len(module_names),'main_theorems':config['main_theorems'],
                'receipt_sha256':receipt_sha,'matching_extracted_replays':replay_matches,
                'independent_receipt_sha256':sha(independent_bytes),
                'receipt_metadata_notes':notes,
                'independent_review_files':reviews,'paper_sha256':sha(archive.read(prefix+'paper.pdf')),
                'novelty_and_scope_limits':entry.get('novelty_limit',entry.get('scope',''))})
    report={'status':'PASS' if all(x['status']=='PASS' for x in results) else 'FAIL',
            'accepted_count':ledger['discovery_count'],'target':ledger['target'],
            'scope':'Artifact integrity and retained proof/review/replay coverage only; independent mathematical and bounded novelty decisions remain attached to each outcome. This audit is not a new Lean compilation or worldwide-priority certificate.',
            'ledger_sha256':sha((ROOT/'ledger.json').read_bytes()),'outcomes':results}
    destination=ROOT/'verification/collection-integrity-audit.json'
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'accepted_count':report['accepted_count'],
                      'failures':[{k:x[k] for k in ['number','failures']} for x in results if x['failures']]},indent=2))

if __name__=='__main__':main()
