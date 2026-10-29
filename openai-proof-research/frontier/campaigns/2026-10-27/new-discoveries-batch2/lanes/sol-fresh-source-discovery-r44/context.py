import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':[]}
for f in [B/'ledger.json',B/'prior-campaign-context.json']+sorted(B.glob('lanes/sol-fresh-*/SUMMARY.md')):
 if f.parent==P:continue
 data=f.read_bytes()
 out['files'].append({'path':str(f),'sha256':hashlib.sha256(data).hexdigest(),'first_paragraphs':data.decode().split('\n\n')[:3]})
for f in [B/'ledger.json',B/'prior-campaign-context.json']:
 d=json.loads(f.read_text());print(f.name,'keys',list(d))
 if 'accepted' in d:print('accepted',[(x.get('number'),x.get('title')) for x in d['accepted']])
(P/'context-screen.json').write_text(json.dumps(out,indent=2))
d=json.loads((P/'sources/delta.json').read_text());print('delta',d.get('status'),d.get('total_commits'),'files',len(d.get('files',[])),[(x['filename'],x['status']) for x in d.get('files',[])])
