from fetch import get,D
import json,concurrent.futures,re,hashlib
out={};todo=[]
for name,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 t=json.loads((D/f'sources/{name}-root.json' if name=='omega' else D/f'sources/{name}-tree.json').read_text());out[name]={'head':json.loads((D/f'sources/{name}-head.json').read_text())['sha'],'root_truncated':t.get('truncated')}
 if name=='omega':
  for scope in ['D5','Problems']:
   a=next(x for x in t['tree'] if x['path']==scope);todo.append((f'omega-{scope}-tree.json',a['url']+'?recursive=1'))
 else:
  p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';b=p.read_bytes();out[name]['cached_preprints']={'path':str(p),'sha256':hashlib.sha256(b).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
terms=r'fox.*nenadov|berczi|chandrasekaran|tangent.*conic|reverse.*strategy|fractional.*isometric|fractional.*general.position|lexicode|johnson.*cover|2.jet|overcubic|cohen.*potent|5.potent|xor.magic|residue.class.*bias|hook.*bias|descendent|triangular.partition|grothendieck|codegree.*density|super.exponential|bidirectional.*polygon|sumset.*uniform'
for p in [D/'sources/omega-D5-tree.json',D/'sources/omega-Problems-tree.json',D/'sources/openai-tree.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 o=json.loads(p.read_text()); hits=[v for v in o['tree'] if re.search(terms,v['path'],re.I)];out[p.name]={'truncated':o.get('truncated'),'entries':len(o['tree']),'hits':hits};print(p.name,len(hits))
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
