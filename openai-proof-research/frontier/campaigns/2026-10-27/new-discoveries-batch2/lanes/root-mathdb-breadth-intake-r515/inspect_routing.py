import pathlib,json
P=pathlib.Path(__file__).resolve().parent;L=P.parent
r=json.loads(next((P/'frozen/root-mathdb-breadth-intake-r415/routing-queue.jsonl').open()))
print('routing keys',list(r));print('routing metadata',{k:v for k,v in r.items() if k not in {'statement','title','technical_assessment'}})
c=json.loads(next((L/'pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0001.jsonl').open()))
print('corpus keys',list(c));print('metadata',{k:c[k] for k in ['status','record_kind','retrieval_status','solution_count','priority_score','importance'] if k in c})
