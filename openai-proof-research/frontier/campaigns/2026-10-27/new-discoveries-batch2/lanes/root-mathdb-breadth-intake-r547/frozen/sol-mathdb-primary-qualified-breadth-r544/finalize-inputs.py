import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent
out=json.loads((D/'flat-bindings.json').read_text());by={e['path']:e for e in out}
def stamp(p):
 h=hashlib.sha256();size=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);size+=len(b)
 return {'path':str(p),'sha256':h.hexdigest(),'size':size}
flat=L/'sol-mathdb-primary-qualified-breadth-r540/flat-bindings.json'
for e in json.loads(flat.read_text()):
 p=pathlib.Path(e['path']);s=stamp(p);assert s['sha256']==e['sha256'] and s['size']==e.get('size',e.get('bytes')),str(p)
 if str(p) in by:assert s==by[str(p)]
 by[str(p)]=s
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parent.parent.parent.parent/'AGENTS.md']:
 if p.exists():by[str(p)]=stamp(p)
(D/'flat-bindings.json').write_text(json.dumps(list(by.values()),indent=2)+'\n');print('flat originals',len(by))
provenance={'reuse':'Original immutable snapshot references only, no corpus/PDF/tree copies. PDF and derivative checked against each producer manifest before selected text reading. No fresh PDF extraction or visual work.','sources':[]}
for lane,stem,url,version,span in [('r428','4080','https://ems.press/content/serial-article-files/46238','OWR37/2009, Benzi, pp2064-2065','lines1875-1929'),('r436','12861','https://ems.press/content/serial-article-files/46491','OWR01/2014, Heinig, pp57-60','lines2371-2490'),('r442','owr2017-20','https://ems.press/content/serial-article-files/46684','OWR20/2017, Yoshida-Zhang-Zhang, pp1245-1246','lines1650-1748')]:
 P=L/('sol-mathdb-primary-qualified-breadth-'+lane)
 provenance['sources'].append({'primary_pdf_url':url,'version':version,'passage_coverage':span,'pdf_binding':by[str(P/('sources/'+stem+'.pdf'))],'text_binding':by[str(P/('sources/'+stem+'.txt'))],'producer_manifest_binding':by[str(P/'manifest.json')],'retrieval_utc_evidence':'See bound original source-provenance.json / pdf-provenance.json / body-downloads.json in this producer lane; not represented as a fresh byte retrieval.','whole_body_read':False,'successor_body_read':False,'full_dependency_audit':False})
(D/'source-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
