from pathlib import Path
import json,hashlib,datetime,re,subprocess
P=Path(__file__).resolve().parent; B=P.parent.parent; R=B.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
context=[]
for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']:
 if p.exists():context.append({'path':str(p),'sha256':sha(p),'bytes':len(p.read_bytes())})
summaries=sorted(R.glob('frontier/campaigns/**/SUMMARY.md'))
patterns={'silicosis':r'silicosis|1901[.]10670|0956792519000329|da Costa.{0,30}Drmota','geometry':r'447678|Convex functions in convex sets|Pasteczka'}
screen={k:[{'path':str(p),'hits':[s for s in p.read_text(errors='replace').splitlines() if re.search(v,s,re.I)]} for p in summaries if re.search(v,p.read_text(errors='replace'),re.I)] for k,v in patterns.items()}
(P/'context-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files_scanned':len(summaries),'context':context,'older_summary_matches':screen,'r57_r74_read':list(range(57,75))},indent=2)+'\n')
G=B/'lanes/root-edge-irregulator-current-prior-r1'; reg=json.loads((G/'CURRENT-REGISTRIES.json').read_text());res={}
for repo in ['omega','openai']:
 p=G/(repo+'-tree.txt'); data=p.read_text(); lines=data.splitlines()
 exact=[s for s in lines if re.search(r'Silicosis|Grinfeld|1901[.-]10670|Drmota|HermiteHadamard',s,re.I)]
 related=[s for s in lines if re.search(r'ExponentialSum/DescartesRule|ThresholdPublicGoodDualEquilibria',s)]
 res[repo]={'head':reg[repo]['head'],'entries':len(lines),'sha256':sha(p),'sha_matches':sha(p)==reg[repo]['tree_sha256'],'exact_lexical_matches':exact,'related_lexical_matches':related}
(P/'registry-screen.json').write_text(json.dumps({'screen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'registry_observed_utc':reg['utc'],'freshness':'Dated complete inventories supplied by root; no new HEAD request; later head movement unknown','results':res,'limit':'Paths are not semantic clearance; selected actual Lean read, not Blueprint. No git or API calls.'},indent=2)+'\n')
for stem in ['source-v1','followup-v1','descartes-v1']:
 p=P/'evidence'/(stem+'.pdf')
 if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
subprocess.run(['pdftoppm','-f','18','-l','18','-scale-to','1500','-singlefile','-png',str(P/'evidence/silicosis.pdf'),str(P/'evidence/source-conjecture')],check=True)
print('context, complete-tree screens, PDF extraction/render PASS')
