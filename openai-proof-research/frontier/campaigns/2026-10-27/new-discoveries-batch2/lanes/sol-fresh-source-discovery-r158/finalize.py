from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def J(n,v):(L/n).write_text(json.dumps(v,indent=2)+'\n')
if sys.argv[1]=='context':
    out={}
    for n in ['ledger.json','prior-campaign-context.json']:
        b=(L/('context-'+n)).read_bytes();j=json.loads(b)
        out[n]=dict(sha256=H(b),top_level_keys=list(j),list_counts={k:len(v) for k,v in j.items() if isinstance(v,list)},matched_records=[])
        import re
        for k,v in j.items():
            if isinstance(v,list):
                for row in v:
                    if re.search('Macdonald|Haglund|Liang|Sagan|Shankar|34772|02782|12467',json.dumps(row),re.I):out[n]['matched_records'].append(dict(section=k,record=row))
    J('context-read.json',out)
    head=json.loads((L/'sources/openai-head.json').read_bytes())
    J('current-source-scope.json',dict(utc=now(),openai_head=head['sha'],commit_date=head['commit']['committer']['date'],current_and_fixed_chromatic_pdf_equal=(L/'sources/openai-current.pdf').read_bytes()==(L/'sources/openai-fixed.pdf').read_bytes(),source='2610.34772v1, submitted2026-10-26; no journal reference on live abs page',companion='2407.06965v2, published IMRN2025 rnaf144; publisher403, latest arXiv body read; no typeset identity claim',not_global_clearance=True))
    r=json.loads((L/'checks.json').read_bytes());print('checks',len(r['records']),'negative',sum(len(x['negative']) for x in r['records']))
    print('current OpenAI',head['sha']);print('context matches',out)
elif sys.argv[1]=='freeze':
    http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
    inputs=[]
    for rel in ['sol-fresh-source-discovery-r150/history-receipt.json','sol-fresh-source-discovery-r153/history-delta.json','sol-fresh-source-discovery-r155/history-delta.json','sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
        p=L.parent/rel;inputs.append(dict(path=str(p),sha256=H(p.read_bytes())))
    J('baseline-provenance.json',inputs)
    J('provenance.json',dict(utc=now(),result='UNRESOLVED, zero eligible discoveries',credit=0,counts_observed=dict(additional=9,total=39,next=40),http=http,baseline_inputs=inputs,guard='unchanged helper_guard.py; AS512MiB/group sampledRSS512MiB CPU210s wall230s nominal40ms; environment BLAS1/OMP1/PYTHONDONTWRITEBYTECODE1; unsampled transients not excluded',history='Complete retained original report bodies, no size cutoff. r150 qualified baseline plus r153/r155 deltas; newly changed originals refreshed. Generated echoes excluded by role. r111-r113 original scientific reports retained. Not worldwide semantic clearance.',registry='Fixed Omega490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c/OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a and source-facing current chromatic PDF actual statement. Two capped300 compares remain incomplete; lexical absence is not clearance.',limits=['No independent eligibility clearance','No full mathematical solution','No audit of all chromatic proof dependencies','Published alpha body403','Initial context output truncated','Initial shell path inventory outside guard; native bounded reads subsequently and all other command work guarded','Known-case full proof bodies read after initial experiment launch; scope and target statements read first'],external_actions=False))
    omit={'finalmanifest.json','scientific-freeze.json','manifest-verification.json','freeze.log','verify.log'}
    files={str(p.relative_to(L)):H(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in omit}
    science={p:h for p,h in files.items() if not p.startswith('context-') and not p.endswith('.log')}
    J('scientific-freeze.json',dict(utc=now(),files=science))
    files['scientific-freeze.json']=H((L/'scientific-freeze.json').read_bytes())
    J('finalmanifest.json',dict(utc=now(),files=files,excluded=sorted(omit-{'scientific-freeze.json'}),self_hash_excluded=True))
elif sys.argv[1]=='verify':
    result={}
    for n in ['scientific-freeze.json','finalmanifest.json']:
        j=json.loads((L/n).read_bytes());bad=[p for p,h in j['files'].items() if not (L/p).is_file() or H((L/p).read_bytes())!=h]
        assert not bad,(n,bad)
        result[n]=dict(entries=len(j['files']),mismatches=bad)
    for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()):
        if 'sha256' in r:assert H((L/'sources'/r['name']).read_bytes())==r['sha256']
    J('manifest-verification.json',dict(utc=now(),pass_=True,checks=result));print(result)
