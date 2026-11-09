import pathlib,re,json,hashlib
D=pathlib.Path('.');x=json.loads((D/'extracted.json').read_text());o={}
for i,v in x.items():
 a=v['source_url'].split('/')[-1];p=D/'sources'/f'{a}.txt'
 if not p.exists():continue
 ls=p.read_text().splitlines();hits=[]
 for j,l in enumerate(ls):
  if re.search(r'Conjecture|Lemma [\d]|Theorem [\d]|Definition [\d]|verified|computational',l):
   hits.append({'line':j+1,'text':'\n'.join(ls[max(0,j-2):min(len(ls),j+17)])})
 o[i]=hits
(D/'outputs/source-passages.json').write_text(json.dumps(o,indent=2))
for n in ['openai','omega']:
 z=json.load(open('sources/'+n+'-head.json'));print(n,z['sha'],[(v['filename'],v['status']) for v in z.get('files',[]) if re.search('367773|367985|368463|368622|369623|370576|371615|371911|372231|362002|362028|362167|363220|364527|364967|365061|365961|357466|357982|358422|tournament|dihedral|golay',v['filename'],re.I)])
