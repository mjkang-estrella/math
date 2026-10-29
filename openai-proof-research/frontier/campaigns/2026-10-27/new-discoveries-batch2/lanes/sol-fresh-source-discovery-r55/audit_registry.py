import pathlib,json,hashlib,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent
old=json.loads((B/'lanes/sol-fresh-source-discovery-r53/registry-screen.json').read_text())
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'coverage':'Complete named cached scopes only, plus incremental comparisons. No whole-dev coverage claim.','registries':{}}
for k,v in old['registries'].items():
 h=json.loads((P/'sources'/f'{k}-head.json').read_text()); scopes=[]
 for s in v['scopes']:
  p=pathlib.Path(s['path']);d=json.loads(p.read_text());sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==s['sha256']
  scopes.append({'path':str(p),'sha256':sha,'entries':len(d['tree']),'truncated':d.get('truncated'),'hits':[a['path'] for a in d['tree'] if any(w in a['path'].lower() for w in ['nuttall','wronsk','cumulant','charlier','coefficientvanish'])]})
 r['registries'][k]={'head':h['sha'],'commit_utc':h['commit']['committer']['date'],'baseline':v['head'],'unchanged':h['sha']==v['head'],'scopes':scopes}
 if h['sha']!=v['head']:
  repo={'omega':'the-omega-institute/trureturing','omega-main':'the-omega-institute/trureturing','openai':'openai/math','aim':'MColbrook/AIM','count':'suvrit/count-ex-machina'}[k]
  subprocess.run(['python3',str(P/'fetch.py'),k+'-delta.json',f'https://api.github.com/repos/{repo}/compare/{v["head"]}...{h["sha"]}'],check=True)
  d=json.loads((P/'sources'/f'{k}-delta.json').read_text());r['registries'][k]['delta']={'total_commits':d.get('total_commits'),'returned_commits':len(d.get('commits',[])),'files':[x['filename'] for x in d.get('files',[])],'file_list_may_cap_at_300':len(d.get('files',[]))>=300}
(P/'registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
