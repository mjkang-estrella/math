import pathlib,json,hashlib,resource,time,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'reservation.json').read_bytes()); expected=(L/'reservation.sha256').read_text().strip()
assert H((L/'reservation.json').read_bytes())==expected
(L/'raw').mkdir(exist_ok=True)
out={}; start=time.monotonic()
for p in sorted((L.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
    assert time.monotonic()-start<130
    digest=hashlib.sha256()
    found=[]
    with p.open('rb') as f:
        for n,line in enumerate(f,1):
            digest.update(line)
            a=json.loads(line)
            if a['mathdb_id'] in r['ids']:
                i=str(a['mathdb_id']); (L/'raw'/f'{i}.jsonl').write_bytes(line)
                out[i]={'record':a,'provenance':{'chunk':str(p),'one_based_line':n,'raw_sha256':H(line),'statement_sha256':H(a['statement'].encode()),'raw_path':f'raw/{i}.jsonl','newline_preserved':line.endswith(b'\n')}};found.append(i)
    for i in found:out[i]['provenance']['chunk_sha256']=digest.hexdigest()
assert set(out)==set(map(str,r['ids']))
(L/'records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
(L/'literal-statements.txt').write_text('\n\n'.join(i+' '+out[str(i)]['record']['title']+'\n'+out[str(i)]['record']['statement'] for i in []) if False else '\n\n'.join(str(i)+' '+out[str(i)]['record']['title']+'\n'+out[str(i)]['record']['statement'] for i in r['ids']))
(L/'extraction-log.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'script':str(pathlib.Path(__file__).resolve()),'elapsed':time.monotonic()-start,'cpu':resource.getrusage(resource.RUSAGE_SELF).ru_utime,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'reservation_before':expected,'reservation_after':H((L/'reservation.json').read_bytes()),'records':len(out)},indent=2)+'\n')
