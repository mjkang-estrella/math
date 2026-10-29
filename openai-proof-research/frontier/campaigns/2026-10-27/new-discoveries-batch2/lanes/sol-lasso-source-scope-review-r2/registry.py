import pathlib,json,re,hashlib,datetime,urllib.request,urllib.error
out=pathlib.Path(__file__).resolve().parent
root=out.parent/'root-edge-irregulator-final-freeze-r1'
def sha(b):return hashlib.sha256(b).hexdigest()
meta=json.loads((root/'CURRENT-REGISTRIES.json').read_text())
report={'inventory_utc':meta['utc'],'review_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Dated bounded path screen and selected actual bodies, not semantic absence.'}
rx=re.compile(r'2303[._-]?16843|stallrich|(?:^|[/_-])lasso(?:[/_.-]|$)|sign.?recover|irrepresent|supersatur|(?:screening|orthogonal).*(?:design|select|recover)|(?:gaussian|sparse).*regress',re.I)
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 b=(root/(key+'-tree.txt')).read_bytes();assert sha(b)==meta[key]['tree_sha256']
 lines=b.decode().splitlines(); hits=[]
 for line in lines:
  p=line.split('\t',1)[-1]
  if rx.search(p):hits.append(p)
 delta=(root/(key+'-delta.txt')).read_text().splitlines()
 d_hits=[x for x in delta if rx.search(x.split('\t')[-1])]
 report[key]={**meta[key],'inventory_file_sha256':sha(b),'regex':rx.pattern,'hits':hits,'delta_hits':d_hits}
 (out/(key+'-matches.txt')).write_text('\n'.join(hits)+'\n')
 print(key,len(lines),'entries',len(hits),'hits',len(d_hits),'delta hits')
 print('\n'.join(hits[:70]))
(out/'registry-screen.json').write_text(json.dumps(report,indent=2))
