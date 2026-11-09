import os,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
start=datetime.datetime.now(datetime.timezone.utc).isoformat();reads=[]
def rd(p):
 b=p.read_bytes();reads.append(dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss));return b
manifest=json.loads(rd(P/'artifact-manifest.json'))
for rel,h in manifest['sha256'].items():assert hashlib.sha256(rd(P/rel)).hexdigest()==h,rel
r=rd(P/'reservation.json');assert hashlib.sha256(r).hexdigest()=='9159598d2019e4d0f760c4fa6d272da068f157a36635e9863746008d5e8b78a2'
ids=json.loads(r)['ids'];f=json.loads(rd(P/'raw-provenance.json'));results=json.loads(rd(P/'results.json'));assert set(map(str,ids))==set(f)==set(results) and len(f)==20
chunks={}
for i,v in f.items():
 p=pathlib.Path(v['chunk_path'])
 if str(p) not in chunks:chunks[str(p)]=rd(p)
 b=chunks[str(p)];assert hashlib.sha256(b).hexdigest()==v['chunk_sha256'];raw=b.splitlines(keepends=True)[v['line']-1];assert raw.decode()==v['raw'];assert hashlib.sha256(raw).hexdigest()==v['raw_sha256'];assert json.loads(raw)==v['parsed'];assert v['parsed']['mathdb_id']==int(i);assert hashlib.sha256(v['parsed']['statement'].encode()).hexdigest()==v['statement_sha256']==results[i]['statement_sha256']
receipt=dict(start=start,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),reservation_after=hashlib.sha256(r).hexdigest(),exact_records_verified=20,artifact_hashes_verified=len(manifest['sha256']),reads=reads,affinity=sorted(os.sched_getaffinity(0)),CPU=resource.getrlimit(resource.RLIMIT_CPU),AS=resource.getrlimit(resource.RLIMIT_AS),peak_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,descendants=[],verification='PASS',exit_note='Assertions all passed; actual process exit reported by invoking tool, not self-predicted telemetry',manifest_exclusions=manifest['excluded'])
# Mandated verifier receipt exception; own lane resolved only.
target=(P/'verification.json').resolve();assert target.is_relative_to(P);target.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['reservation_after','exact_records_verified','artifact_hashes_verified','verification']}))
