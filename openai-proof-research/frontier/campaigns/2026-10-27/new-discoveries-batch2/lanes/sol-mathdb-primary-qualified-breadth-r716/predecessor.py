exec(open(__file__.replace('predecessor.py','bind.py')).read().split('refs={}')[0])
import urllib.request,subprocess,datetime
prov=j(P/'source-provenance.json');d={'arxiv':'2510.09219','version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pdf_url':'https://arxiv.org/pdf/2510.09219v1'}
try:
 with urllib.request.urlopen(urllib.request.Request(d['pdf_url'],headers={'User-Agent':'Python-urllib/3'}),timeout=40) as f:b=f.read();d['pdf_final_url']=f.url
 assert b.startswith(b'%PDF');p=P/'2510.09219v1.pdf';p.write_bytes(b);d['pdf_binding']=entry(p)
 t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);d['text_binding']=entry(t);d['coverage']='bound derivative; not yet read'
except Exception as e:d['failure']=str(e);d['stop']='no retry'
prov.append(d);write('source-provenance.json',prov);print(d)
