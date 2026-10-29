from research import *
o=json.loads((H/'sources/omega-head.json').read_text());a=json.loads((H/'sources/openai-head.json').read_text());d=json.loads((H/'sources/omega-delta.json').read_text())
r={'omega':o['sha'],'openai':a['sha'],'base':'9a026fe5527cacf8d3aed5f9291f08bc520ea90b','status':d.get('status'),'ahead_by':d.get('ahead_by'),'total_commits':d.get('total_commits'),'returned_commits':len(d.get('commits',[])),'files':len(d.get('files',[])),'files_cap_possible':len(d.get('files',[]))>=300,'commit_cap_possible':len(d.get('commits',[]))<d.get('total_commits',0),'matches':[]}
for f in d.get('files',[]):
 s=f['filename']+'\n'+f.get('patch','')
 if re.search('domino|cavey|saturat|2410.11194|2501.17765',s,re.I):r['matches'].append({'path':f['filename'],'patch':f.get('patch')})
# Complete body of closest actual public theorem remains separate from patch screening.
save('registry-receipt.json',r);print(json.dumps(r,indent=2)[:9000])
