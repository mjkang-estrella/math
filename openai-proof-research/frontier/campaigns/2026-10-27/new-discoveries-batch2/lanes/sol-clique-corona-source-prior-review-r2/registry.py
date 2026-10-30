import pathlib,json,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parent
p=L.parent/'sol-steiner-gp-source-prior-review-r2/retrieved/omega-fixed-delta.json';b=p.read_bytes()
q=L/'retrieved/omega-fixed-delta.json';q.write_bytes(b)
o=json.loads(b)
print('keys',list(o));print({k:v for k,v in o.items() if k not in ['files','commits']})
rows=[]
for f in o.get('files',[]):
 text=f.get('patch','');hit=bool(re.search(r'corona|unimodal|independence.polynomial|Levit|Mandrescu|3383|2015.09.021',f['filename']+'\n'+text,re.I))
 rows.append({'path':f['filename'],'status':f.get('status'),'patch_present':'patch' in f,'patch_bytes':len(text.encode()),'literal_alias_hit':hit})
 if hit:print('HIT',f['filename'],text)
print('FILES',json.dumps(rows,indent=2))
(L/'registry-coverage.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':str(p),'copy':str(q),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'files':rows,'base':'d36a58e865e46580f127ef7a09d64ccbc2370296','head':'2b143c68ca72fcaccfe71d6233cb2c6db4c8c059','note':'Saved fixed comparison; not a current HEAD or historical merge certificate.'},indent=2)+'\n')
