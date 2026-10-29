from pathlib import Path
import json,urllib.request,datetime,hashlib,re
P=Path(__file__).resolve().parent;root=P.parent/'root-edge-irregulator-final-freeze-r1'
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':'Filename search is not semantic clearance; no git operations. Exact relevant bodies read separately.'}
for n in ['openai','omega']:
 f=root/(n+'-tree.txt');data=f.read_bytes();lines=data.decode().splitlines();hits=[x for x in lines if re.search('Zagreb|HansenV|Sarkhel|Isoclin|CommutingGraph|CommutativityPreserv',x,re.I)]
 j=json.loads((P/'sources'/(n+'-head.json')).read_text());old=json.loads((root/'CURRENT-REGISTRIES.json').read_text())[n]['head']
 report[n]={'old_head':old,'head':j['sha'],'cached_tree_sha256':hashlib.sha256(data).hexdigest(),'entries':len(lines),'matches':hits}
 if j['sha']!=old:
  url='https://api.github.com/repos/the-omega-institute/trureturing/compare/'+old+'...'+j['sha']
  row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=25) as r:b=r.read(16000000);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest());P.joinpath('sources/omega-compare.json').write_bytes(b)
   z=json.loads(b);report[n]['delta']={'status':z.get('status'),'total_commits':z.get('total_commits'),'files':[x['filename'] for x in z.get('files',[])],'truncation_limit':300}
  except Exception as e:row['error']=str(e)
  h=json.loads(P.joinpath('http.json').read_text());h.append(row);P.joinpath('http.json').write_text(json.dumps(h,indent=2))
P.joinpath('registry-screen.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
