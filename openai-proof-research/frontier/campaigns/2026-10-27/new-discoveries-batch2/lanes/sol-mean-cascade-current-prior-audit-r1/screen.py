exec((__import__('pathlib').Path(__file__).parent/'audit.py').read_text().split("if sys.argv[1] in")[0])
terms=['2405.13618','2004.07893','aadm240618001m','bej1299','mihok','raïss','raiss','cénac','cenac','pouyanne','paccaut','arctan','stolarsky','cascade','variablelength','variable-length','contexttree','context-tree','stabiliz','mean']
results={}
for n in ['omega-D5-tree.json','omega-Problems-tree.json','openai-preprints-tree.json','count-full-tree.json']:
 j=json.loads((b/'sources'/n).read_text());assert j['truncated']==False
 hits={t:[e['path'] for e in j['tree'] if t in e['path'].lower()] for t in terms}
 results[n]={'entries':len(j['tree']),'matches':{t:v for t,v in hits.items() if v}}
(b/'path-screen.json').write_text(json.dumps(results,indent=2))
for n,j in results.items():print(n,json.dumps(j['matches'],ensure_ascii=False)[:10000])
print('ROOTS')
for n in ['openai','count']:print(n,[e['path'] for e in json.loads((b/'sources'/(n+'-root.json')).read_text())['tree']])
