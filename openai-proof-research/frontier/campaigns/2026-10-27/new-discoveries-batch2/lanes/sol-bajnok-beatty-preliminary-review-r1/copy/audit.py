import pathlib,json,hashlib,re,datetime,urllib.request
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent;R=B.parents[3]
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'context':{},'registry':{}}
for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',B/'lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json']:
 b=p.read_bytes();entry={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
 if p.name in ['ledger.json','prior-campaign-context.json']:
  j=json.loads(b);entry['accepted']=[{'number':x.get('number'),'title':x.get('title'),'scope':x.get('scope')} for x in j.get('accepted',[])]
 out['context'][str(p)]=entry
for name in ['omega','openai']:
 j=json.loads((P/f'sources/{name}-head.json').read_text());out['registry'][name]={'head':j['sha'],'commit_date':j['commit']['committer']['date']}
j=json.loads((P/'sources/omega-compare.json').read_text());files=j.get('files',[])
out['registry']['omega'].update(compare_files=len(files),total_commits=j.get('total_commits'),matches=[f for f in files if re.search('bajnok|beatty|noncyclic|bow.variet|gyenge|collatz|rahavandrainy',f['filename']+' '+f.get('patch',''),re.I)],coverage='bounded compare API; not complete body inventory; no global novelty clearance')
(P/'audit.json').write_text(json.dumps(out,indent=2))
# Read exact potentially adjacent current registry body; unrelated author name is not automatic subsumption.
head=out['registry']['omega']['head'];u=f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/Blueprint/D5/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis.md'
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u}
try:
 with urllib.request.urlopen(u,timeout=25) as f:b=f.read(2_000_000);r['status']=f.status
 (P/'sources/bajnok-comparator.md').write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest()
except Exception as e:r['error']=str(e)
(P/'comparator-http.json').write_text(json.dumps(r,indent=2))
print(json.dumps(out['registry'],indent=2))
