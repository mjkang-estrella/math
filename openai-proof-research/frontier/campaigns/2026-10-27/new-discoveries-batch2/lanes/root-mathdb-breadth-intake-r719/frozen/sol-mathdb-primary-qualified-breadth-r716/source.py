exec(open(__file__.replace('source.py','bind.py')).read().split('refs={}')[0])
import urllib.request,datetime,re,subprocess
prov=[]
for a in ['2504.07978','2501.00047','2505.00413','2510.09219']:
 item={'arxiv':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'coverage':'not read'};prov.append(item)
 try:
  url='https://arxiv.org/abs/'+a
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=30) as f:b=f.read();item['abs_final_url']=f.url
  p=P/(a+'-abs.html');p.write_bytes(b);item['abs_binding']=entry(p)
  # Bound HTML before version parsing.
  text=p.read_text();versions=re.findall(r'\b'+re.escape(a)+r'v(\d+)\b',text);v=max(map(int,versions)) if versions else 1
  item['version']=v;url='https://arxiv.org/pdf/'+a+'v'+str(v);item['pdf_url']=url
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=40) as f:b=f.read();item['pdf_final_url']=f.url
  assert b.startswith(b'%PDF');p=P/(a+'v'+str(v)+'.pdf');p.write_bytes(b);item['pdf_binding']=entry(p)
  t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);item['text_binding']=entry(t);item['coverage']='bound text derivative; not yet read'
 except Exception as e:item['failure']=str(e);item['stop']='no retry or alternate route'
 write('source-provenance.json',prov)
print(json.dumps(prov,indent=2))
