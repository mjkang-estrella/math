from research import *
j=json.loads((HERE/'omega-delta.json').read_text());r={'utc':utc(),'status':j.get('status'),'base':j.get('merge_base_commit',{}).get('sha'),'total_commits':j.get('total_commits'),'returned_commits':len(j.get('commits',[])),'paths':len(j.get('files',[])),'files_cap_risk':len(j.get('files',[]))>=300,'target_hits':[],'coverage':'Only fixed a776→9a026 interval; path and patch screen, not all historical semantic clearance.'}
rx=re.compile(r'visibility|04144|01280|admissib|local.?ramsey|ramsey.{0,20}local|subdivision',re.I)
for f in j.get('files',[]):
 if rx.search(f['filename']+' '+f.get('patch','')):r['target_hits'].append({'path':f['filename'],'patch':f.get('patch','')[:3000]})
save('registry-refresh.json',r);print(json.dumps(r,indent=2));print('changed paths',*[f['filename'] for f in j.get('files',[])],sep='\n')
