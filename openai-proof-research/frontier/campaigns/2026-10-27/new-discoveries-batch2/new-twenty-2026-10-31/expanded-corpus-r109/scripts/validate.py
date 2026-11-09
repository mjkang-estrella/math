# Validate provenance: chunk hashes against the corpus manifest, raw line bytes, statement hashes, line numbers.
import json, hashlib, pathlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parents[1]
man=json.loads((B/'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text())
s=json.dumps(man)
ex=json.loads((D/'extracted.json').read_text()); res=json.loads((D/'results.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest(); out={}
for i,o in ex.items():
    p=o['provenance']; chunk=pathlib.Path(p['chunk']).read_bytes(); lines=chunk.splitlines(keepends=True)
    raw=(D/'raw'/f'{i}.jsonl').read_bytes()
    out[i]=dict(chunk_sha_matches_file=sha(chunk)==p['chunk_sha256'], chunk_sha_in_manifest=p['chunk_sha256'] in s,
        raw_line_matches=lines[p['line_1based']-1]==raw, raw_sha=sha(raw)==p['raw_sha256'], raw_ends_newline=raw.endswith(b'\n'),
        statement_sha=sha(json.loads(raw)['statement'].encode())==p['statement_utf8_sha256'], results_statement_equal=res[i]['statement']==o['statement'])
ok=all(all(v.values()) for v in out.values())
(D/'outputs/provenance-validation.json').write_text(json.dumps({'all_ok':ok,'entries':out,'results_count':len(res)},indent=1)+'\n')
print('all_ok',ok,len(res))
