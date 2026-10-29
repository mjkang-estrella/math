import pathlib,json,re,urllib.request,datetime,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent
pat=re.compile(r'Aivazidis|Loukaki|transversal|dissociat|subset.{0,25}product|factorial|pigeonhole|阶乘|子集|!\s*/|t\^t|sum.distinct',re.I)
out=[]
def body(repo,ref,p):
 url='https://raw.githubusercontent.com/'+repo+'/'+ref+'/'+p
 r={'url':url,'ref':ref,'path':p,'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as q:
   b=q.read(2500000);r.update(status=q.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  t=b.decode(errors='replace');r['opening']=t[:1700];r['excerpts']=[t[max(0,m.start()-180):m.end()+450] for m in list(pat.finditer(t))[:8]]
  r['git_blob']=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 except Exception as e:r['error']=str(e)
 r['utc_end']=datetime.datetime.now(datetime.timezone.utc).isoformat();out.append(r)
 print(p,r.get('status',r.get('error')),len(r.get('excerpts',[])))
leads=json.loads((L/'sol-factorial-product-preliminary-review-r1/registry-path-leads.json').read_text())
for x in leads:
 if x['repo']=='omega' and x['path'].endswith('.md') and re.search('PigeonholeFiber|LatinHTransversals|QTransversalRepresentability|InvolutionTransversal|TransversalFixedPoint|ProductCoordinateTransversality',x['path']):body('the-omega-institute/trureturing','1b999d9fda71df7537b62327147496d64a6f66ef',x['path'])
later=json.loads((L/'sol-supertoken-preliminary-review-r1/omega-new-delta.json').read_text())
for f in later['files']:
 if f['filename'].endswith('.md') and re.search('ProductClosure|CDSO_GROWING|CDSO_CAPACITY|AURIC_COMPATIBLE',f['filename']):body('the-omega-institute/trureturing','7f200dc4fad796eec490994c705245530200fd78',f['filename'])
j=json.loads((O/'fresh-delta.json').read_text());rows=[]
for f in j.get('files',[]):
 p=f['filename'];t=f.get('patch','');ms=list(pat.finditer(t));rows.append({'path':p,'status':f['status'],'blob':f['sha'],'patch':bool(t),'patch_sha256':hashlib.sha256(t.encode()).hexdigest(),'excerpts':[t[max(0,m.start()-150):m.end()+350] for m in ms[:5]]})
 if (not t and f['status']!='removed') or (ms and (p.endswith('.md') or '/context/' in p)):body('the-omega-institute/trureturing','0d4df45e499f5e2d97471c506c555c18fd44920c',p)
(O/'follow-body-reads.json').write_text(json.dumps(out,indent=2));(O/'fresh-screen.json').write_text(json.dumps({'commits':j.get('total_commits'),'files':rows},indent=2));print('fresh',j.get('total_commits'),len(rows),'missing',sum(not x['patch'] for x in rows),'hits',sum(bool(x['excerpts']) for x in rows))
