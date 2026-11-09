import pathlib,json,hashlib,datetime
O=pathlib.Path(__file__).resolve().parent; B=O.parent.parent; old=B/'lanes/sol-mathdb-primary-qualified-breadth-r390'; r=json.loads((O/'reservation.json').read_text()); H=lambda x:hashlib.sha256(x).hexdigest(); receipts=[]
for group in ['prior_report_hashes','input_hashes']:
 for p,h in r[group].items():
  a=H(pathlib.Path(p).read_bytes());receipts.append(dict(path=p,expected=h,actual=a,match=a==h,group=group));assert a==h,(p,a,h)
d={str(x['mathdb_id']):x for x in json.loads((old/'dispositions.json').read_text())}; bindings=json.loads((old/'corpus-bindings.json').read_text());refs={x['path']:x for x in bindings['refs']};out={}
(O/'raw').mkdir(exist_ok=True)
for i in r['ids']:
 x=d[str(i)];p=pathlib.Path(x['corpus_chunk']);data=p.read_bytes();h=H(data);assert h==refs[str(p)]['sha256'];found=[]
 for n,line in enumerate(data.splitlines(keepends=True),1):
  z=json.loads(line)
  if str(z.get('id',z.get('mathdb_id')))==str(i):found.append((n,line,z))
 assert len(found)==1,(i,len(found));n,line,z=found[0];(O/'raw'/f'{i}.jsonl').write_bytes(line);assert H(x['statement'].encode())==x['statement_sha256']
 out[str(i)]={'old':x,'inherited_coverage':r['prior_coverage'][str(i)],'raw':{'path':str(p),'chunk_sha256':h,'one_based_line':n,'line_sha256':H(line),'line_bytes':len(line),'retained':f'raw/{i}.jsonl'},'literal_quantifiers':x['statement'],'raw_record':z}
(O/'inherited.json').write_text(json.dumps(out,indent=2)+'\n');(O/'binding-verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':receipts,'raw_records':40,'raw_chunks':list(set(x['raw']['path'] for x in out.values()))},indent=2)+'\n')
print('Verified prior immutable/input hashes, 40 literal statements and raw lines; preserved trailing newlines.')
