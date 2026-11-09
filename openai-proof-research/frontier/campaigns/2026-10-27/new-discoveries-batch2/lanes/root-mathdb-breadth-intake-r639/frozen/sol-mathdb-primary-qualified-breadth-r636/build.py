from pathlib import Path
import json,hashlib,itertools
O=Path(__file__).resolve().parent;B=O.parent.parent;I=O.parent/'root-mathdb-breadth-intake-r635'
def save(n,x): (O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
records=json.loads((O/'literal-records.json').read_text());notes={int(l.split('|')[0]):l.split('|')[1:] for l in (O/'review-notes.tsv').read_text().splitlines()}
passages=[]
def excerpt(p,a,b,ids,url):
 lines=Path(p).read_text().splitlines();text='\n'.join(lines[a-1:b]);passages.append(dict(path=str(Path(p).resolve()),start_line=a,end_line=b,mathdb_ids=ids,url=url,text=text,text_sha256=sha(text.encode()),scope='selected primary passage only'))
L=O.parent;f=L/'sol-mathdb-primary-qualified-breadth-r418/primary/farb.txt';u='https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf'
for a,b,ids in [(1324,1347,[390059]),(1730,1778,[390076]),(2010,2055,[390088,390091]),(14188,14224,[390300]),(9337,9375,[390216]),(11218,11262,[390243]),(16306,16345,[390348])]:excerpt(f,a,b,ids,u)
p=L/'sol-mathdb-primary-qualified-breadth-r582/owr711.txt';u='https://ems.press/journals/owr/articles/711'
for a,b,ids in [(2085,2165,[392636]),(2400,2514,[392638]),(2910,2998,[392640]),(4455,4503,[392652])]:excerpt(p,a,b,ids,u)
for n,a,b,ids in [(722,1530,1584,[392730]),(723,584,625,[392734]),(723,1170,1280,[392739]),(723,1316,1488,[392742])]:excerpt(O/f'ems{n}.txt',a,b,ids,f'https://ems.press/journals/owr/articles/{n}')
save('selected-passages.json',passages)
d=[]
for x in records:
 r=x['record'];i=r['mathdb_id'];dis,scope,note=notes[i];d.append(dict(mathdb_id=i,canonical_url=r['canonical_url'],source_url=r['source_url'],source_name=r['source_name'],source_version='only as documented in source-provenance.json',corpus_chunk=x['chunk'],corpus_line=x['line'],canonical_record_sha256=x['canonical_record_sha256'],statement=r['statement'],statement_utf8_sha256=sha(r['statement'].encode()),record_completeness=r['statement_completeness'],literal_review_complete=True,technical_scope=scope,definition_and_mechanism_assessment=note,disposition=dis,primary_passages=[k for k,p in enumerate(passages) if i in p['mathdb_ids']],evidence=dict(statement='exact literal corpus record read',primary='selected passages only' if any(i in p['mathdb_ids'] for p in passages) else 'not inspected beyond literal record',whole_primary_body=False,local_source_proof=i==392640,full_dependency_audit=False,closest_successor_body=False,registry='HOLD unavailable; no absence inference'),proposal=False,accepted_credit=0))
assert len(d)==50;save('dispositions.json',d);save('proposals.json',[])
roots=[]
for a,b in itertools.combinations(range(4),2):
 for sa,sb in itertools.product([-1,1],repeat=2):
  v=[0]*4;v[a]=sa;v[b]=sb;roots.append(v)
assert len(roots)==24 and len(set(map(tuple,roots)))==24
mind=min(sum((x-y)**2 for x,y in zip(v,w)) for v,w in itertools.combinations(roots,2));assert mind==2
save('bounded-checks.json',dict(executed=[dict(id=390300,check='GL(1,Z)={-1,1}; trivial subgroup index2; trivial epimorphism, n=3 gives1<2',result='excluded wording endpoint'),dict(id=390277,check='Euler characteristic (2-4)*(2-4)',value=16,result='necessary condition only'),dict(id=392652,check='enumerate D4 roots: two coordinates +/-1',root_count=24,squared_norms=sorted(set(sum(a*a for a in v) for v in roots)),minimum_squared_distance=mind,result='known kissing lower bound24 only')],not_executed=['no character search','no NUT sweep','no automaton sweep'],no_new_full_scope_proof=True))
save('source-coverage.json',dict(literal_records=50,selected_primary_record_count=sum(bool(x['primary_passages']) for x in d),selected_passage_count=len(passages),whole_volume_reads=0,full_dependency_audits=0,closest_successor_bodies=0,local_source_proof_read=[392640],primary_answer_reports=[392636,392638,392640],proposals=0,current_registry='HOLD',routing_rows_are_not_reviews=True))
save('source-provenance.json',dict(new_downloads=json.loads((O/'fetch-provenance.json').read_text()),cached_references=[dict(path=str(f),url='https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf',version='cached author-hosted combined volume, not standalone arXiv chapter',provenance_path=str(L/'sol-mathdb-primary-qualified-breadth-r418/provenance.json')),dict(path=str(p),url='https://ems.press/journals/owr/articles/711',version='Oberwolfach Report1/2004',provenance_path=str(L/'sol-mathdb-primary-qualified-breadth-r582/source-provenance.json'))],hashes='flat-bindings.json; fetch-provenance.json; derivative-bindings.json',coverage='selected-passages.json exact ranges; no full body/registry clearance'))
save('failures.json',dict(helper_failures=[dict(stage='first report builder',exit=1,error='SyntaxError unterminated string literal from nested triple quotes; no writes executed; corrected')],access_failures_new=[],inherited_stops=['MathDB429 zero requests','proof registry unavailable HOLD','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS parked','ProjectEuclid challenge parked','ResearchGate403 parked','OEIS A274199/internal403 parked','DOI10.1093/imrn/rnz305 OUP403 challenge parked'],stopped_routes=['rank1 character source Theorem2','all-ones NUT source Theorem6','GL1 excluded wording endpoint','D4 known lower bound only'],deviations=['Filename-only recursive inventory located cached snapshots; no tree copying or historical content expansion.','PDF skill read after first read-only extraction; byte/derivative bindings preceded content inspection.'],limits=['No whole-volume, full dependency, closest-successor-body or live registry clearance.','Historical non-finite-generation assertion for K_g not adopted as current theorem.','Hovey landing derivative keyword inspection yielded no relevant passage; no body coverage claimed.']))
