import pathlib,json,hashlib,re
P=pathlib.Path(__file__).resolve().parent
out=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 b=(P/e['derivative']['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['derivative']['sha256'];assert len(b)==e['derivative']['size']
 lines=b.decode().splitlines();mid=e['mathdb_id'];patterns={340088:r'Conjecture|nested matching|4k|4 k',343652:r'Conjecture|strong product|strong immersion|Theorem 1',353818:r'Conjecture|neighbou|Theorem 1|Theorem 2',345174:r'counterexample|Conjecture|purely-prime|purely-maximal'}
 hits=[i for i,s in enumerate(lines) if re.search(patterns[mid],s,re.I)]
 for i in hits[:16]:
  lo=max(0,i-3);hi=min(len(lines),i+7);text='\n'.join(lines[lo:hi]);out.append({'mathdb_id':mid,'line_start':lo+1,'line_end':hi,'text':text});print(mid,lo+1,hi,text,'\n')
(P/'selected-passages.json').write_text(json.dumps(out,indent=2)+'\n')
