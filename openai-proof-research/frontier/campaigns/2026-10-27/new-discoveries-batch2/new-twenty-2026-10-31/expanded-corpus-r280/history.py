import pathlib,json,subprocess,resource,hashlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
r=pathlib.Path(__file__).resolve().parent; root=r.parents[5]; rows=json.loads((r/'reservation.json').read_text())['rows']
terms=[str(x['mathdb_id']) for x in rows]+[x['source_url'].split('/')[-1] for x in rows]+['strip occupancy','set-homogeneous','self-avoiding walk','stable-set domination','Grid Representations','cubic containers','regular trees','distance-2 matchings','Cuts in matchings','translation ovals','scattered quadrinomials','colorability of bi','Transversals in generalized','Snarks with special','Strong conciseness','Minimum degree and the graph removal','Presentations for Vertex','Sum-Product Configurations','immersion-closed']
p=subprocess.run(['rg','-l','-i','-F',*[z for t in terms for z in ['-e',t]],str(root),'--glob','!expanded-corpus-r280/**','--glob','!*.jsonl','--glob','!*.pdf','--glob','!*.html'],capture_output=True,text=True,timeout=110)
files=[x for x in p.stdout.splitlines() if 'expanded-corpus-r280/' not in x]
(r/'historical-matches.txt').write_text('\n'.join(files)+'\n')
print('ROOT',root,'MATCHES',len(files)); print('\n'.join(files[:100]))
