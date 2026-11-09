import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1];O=L/'resumed-20261105';pat=re.compile(r'1203[.]1780|1210[.]2705|1411[.]2082|1512[.]01335|1806[.]11208|2203[.]07335|2206[.]08106|2208[.]03573|2209[.]12239|2306[.]04088|2310[.]04265|2311[.]07995|2403[.]09423|2409[.]19165|2410[.]04782|2410[.]16521|2512[.]05480|2603[.]11662|2603[.]14668|2606[.]20256|Chapoton|Horton|starter|involution|crossing|sudoku|eppa|Hitchin|irredundance|hyperenergetic|Lemoine|tournament|twin.width',re.I);out=[]
for log in ['registry-scopes.log','github-search.log']:
 for line in (O/log).read_text().splitlines():
  r=json.loads(line);entry={'receipt_url':r['url'],'status':r['status'],'sha256':r.get('sha256')}
  if r['status']==200:
   p=L/'receipts'/r['body_file'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];d=json.loads(p.read_text());entry['truncated']=d.get('truncated');entry['total_count']=d.get('total_count');entry['hits']=[x for x in d.get('tree',[]) if pat.search(x['path'])] if 'tree' in d else [(x['full_name'],x.get('description')) for x in d.get('items',[])];entry['scope']='path_or_metadata_only_no_proof_clearance'
  out.append(entry)
(O/'registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:5000])
