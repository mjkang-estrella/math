import pathlib,json,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((D/'extracted.json').read_text())
terms=[str(i) for i in rows]+[o['source_url'].split('/')[-1] for o in rows.values()]+['simplicial','Perarnau','Heawood','Rivezzi','monomial','Vlasev','Bressoud','Kanade','Orlik','Kirgizov','Dougherty','Lewis','Liouville','Krattenthaler','Muhle','Mühle','antidiagonal','assembly','aperiodic','W-algebra','reduced word','Catalan']
out={}
for reg in ['pool','omega']:
 j=json.loads((D/f'sources/{reg}-tree.json').read_text());paths=[o['path'] for o in j['tree']];hits={t:[p for p in paths if t.casefold() in p.casefold()] for t in terms};hits={t:h for t,h in hits.items() if h}
 out[reg]={'sha':j['sha'],'truncated':j['truncated'],'path_hits':hits,'path_count':len(paths)}
 print(reg,'truncated',j['truncated'],'count',len(paths),json.dumps(hits,ensure_ascii=False)[:7000])
 if reg=='pool':
  wanted=[p for p in paths if p.endswith('projects.yml') or p.startswith('candidates/') and p.endswith(('.md','.yml','.yaml','.json'))]
  print('candidate/project files',wanted)
  for p in wanted:
   subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),'pool-'+p.replace('/','_'),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+j['sha']+'/'+p])
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
