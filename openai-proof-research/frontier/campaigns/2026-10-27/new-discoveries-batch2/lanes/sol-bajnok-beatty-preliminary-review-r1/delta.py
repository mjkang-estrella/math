import pathlib,json,re
D=pathlib.Path(__file__).resolve().parent;results=[]
for path in [D/'copy/sources/omega-compare.json',D/'research/baseline-to-r89.json',D/'research/omega-new-compare.json']:
 j=json.loads(path.read_text());files=j.get('files',[]); matches=[]
 for f in files:
  if re.search(r'bajnok|cayley|lee.?sphere|noncyclic|2406\.04045|2s.?2',f['filename']+'\n'+f.get('patch',''),re.I):matches.append({'filename':f['filename'],'patch':f.get('patch','')})
 results.append({'file':str(path.relative_to(D)),'total_commits':j.get('total_commits'),'commits_returned':len(j.get('commits',[])),'files_returned':len(files),'file_cap_possible':len(files)>=300,'matched_changes':matches,'all_changed_paths':[f['filename'] for f in files]})
(D/'research/delta-audit.json').write_text(json.dumps(results,indent=2));print(json.dumps([{k:v for k,v in r.items() if k not in ['all_changed_paths','matched_changes']}|{'matches':len(r['matched_changes'])} for r in results],indent=2))
