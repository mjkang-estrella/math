import pathlib,json,subprocess,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
rows=json.loads((L/'reservation.json').read_text())['rows']; out={}
for r in rows:
 i=str(r['mathdb_id']);a=r['source_url'].rsplit('/',1)[1]
 cmd=['rg','-l','-i','-e',i,'-e',a,'-e',r['title'],'--glob','SUMMARY.md','--glob','CANDIDATE*','--glob','results.json','--glob','*ledger.json',str(L.parent)]
 p=subprocess.run(cmd,capture_output=True,text=True)
 paths=[s for s in p.stdout.splitlines() if str(L)+'/' not in s]
 out[i]={'patterns':[i,a,r['title']],'hits':paths,'scope':'campaign sibling SUMMARY/CANDIDATE/results/ledgers; administrative ID mentions are not mathematical review'}
 print(i,len(paths),paths[:3])
(L/'outputs/history.json').write_text(json.dumps(out,indent=2))
