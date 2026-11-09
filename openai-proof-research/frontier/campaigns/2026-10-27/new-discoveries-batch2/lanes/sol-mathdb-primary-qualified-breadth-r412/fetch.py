from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,subprocess,sys
R=Path(__file__).resolve().parent; E=R/'evidence';E.mkdir(exist_ok=True)
targets=[('soap','http://torus.math.uiuc.edu/jms/Papers/foams/soap-prob.pdf'),('statistical','https://www.jstage.jst.go.jp/article/iis/4/2/4_2_125/_pdf/-char/en'),('kapovich','https://www.math.ucdavis.edu/~kapovich/EPR/problems.pdf'),('donaldson','https://wwwf.imperial.ac.uk/~skdona/NONLINEARITYPROBLEMS.PDF'),('dynamics','https://arxiv.org/pdf/1304.2590'),('aperiodic','https://arxiv.org/pdf/1604.06280'),('gromov','https://www.ihes.fr/~gromov/wp-content/uploads/2018/08/101-problemsOct1-2017.pdf'),('pansu','https://www.imo.universite-paris-saclay.fr/~pansu/problems_MTDG.tex'),('strata','https://livrepository.liverpool.ac.uk/3022838/1/stratum.pdf'),('ghomi','https://people.math.gatech.edu/~ghomi/Papers/op.pdf'),('montalban','https://math.berkeley.edu/~antonio/papers/questionsRM.pdf'),('simpson','https://sgslogic.net/t20/talks/cta/problems/'),('shelah','https://shelah.logic.at/files/224419/E103.pdf')]
targets += [('simpson-banach','https://sgslogic.net/t20/talks/cta/problems/node3.html'),('simpson-szemeredi','https://sgslogic.net/t20/talks/cta/problems/node6.html'),('simpson-wqo','https://sgslogic.net/t20/talks/cta/problems/node8.html'),('degrees','https://mathoverflow.net/questions/227083/what-are-some-important-but-still-unsolved-problems-in-mathematical-logic')]
class SafeRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  host=urllib.parse.urlparse(newurl).hostname or ''
  assert not any(x in host.lower() for x in ['mathdb','google','github','sciencedirect']),newurl
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(SafeRedirect)
for name,url in targets:
 if len(sys.argv)>1 and name not in sys.argv[1:]:continue
 meta={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'live bytes; document version requires body check'}
 try:
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0 (public academic reading)'}),timeout=12) as f:
   b=f.read(12*1024*1024+1);assert len(b)<=12*1024*1024
   meta.update(final_url=f.url,status=f.status,headers=dict(f.headers),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  suffix='.pdf' if b.startswith(b'%PDF') else '.txt';p=E/(name+suffix);p.write_bytes(b)
  meta['path']=str(p.relative_to(R));(E/(name+'.provenance.json')).write_text(json.dumps(meta,indent=2)+'\n')
  # URL/time/hash persisted before any content extraction.
  if suffix=='.pdf':
   q=subprocess.run(['pdftotext','-layout',str(p),str(E/(name+'.txt'))],capture_output=True,text=True,timeout=18)
   meta['extraction_exit']=q.returncode;meta['extraction_stderr']=q.stderr
  else:meta['extraction_exit']='not_pdf'
 except Exception as e:meta['failure']=repr(e);meta['action']='STOP; no retry or bypass'
 (E/(name+'.provenance.json')).write_text(json.dumps(meta,indent=2)+'\n');print(name,meta.get('status'),meta.get('size'),meta.get('failure',''))
