import pathlib,json,hashlib,re,collections
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i106_positive_characteristic_imm';D=json.loads((R/'frontier/sources/i103_algebraic_complexity_discovery/search-domain.json').read_text());reads=[]
def add(p,a=1,z=None,conv='LF',source=None):
 b=(R/p).read_bytes();ls=b.decode().split('\n') if conv=='LF' else b.decode().splitlines();z=z or (len(ls)-int(ls[-1]=='') if conv=='LF' else len(ls));assert 1<=a<=z<=len(ls)
 rec={'path':str(p),'first':a,'last':z,'line_convention':conv+'; 1-based inclusive; join with LF and append one LF','source_sha256':hashlib.sha256(b).hexdigest(),'passage_sha256':hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()}
 if source:rec.update({'upstream_path':source,'url':'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+source})
 reads.append(rec)
for d in D:
 p=d['path']
 full=('Homogeneous-depth-five-lower-bounds' in p and ('/sections/' in p or p.endswith('references.bib'))) or ('Matrix-Multiplication-Nine-Fourths' in p and p.endswith('paper.tex')) or ('Polynomial-Hitting-Lists' in p and any(p.endswith('/'+x+'.tex') for x in ['encoding','expansion','division','generator'])) or ('Uniform-Matrix-Hitting-Points' in p and any(p.endswith('/'+x+'.tex') for x in ['words','construction']))
 if full:add(d['local'],source=p)
 if 'Below-2.258' in p and p.endswith('08-comparison.tex'):add(d['local'],308,source=p)
old='frontier/sources/i103_algebraic_complexity_discovery/external/'
for file,a,z in [('hw',195,285),('gk',370,560),('gk',945,1016)]:add(old+file+'.txt',a,z)
for file,ranges in {'forbes':[(220,390),(420,510),(510,620)],'agkst':[(1750,1965)],'lst':[(195,240)],'abt':[(300,365),(1670,1725)],'bera':[(94,123),(695,835)]}.items():
 for a,z in ranges:add(str(S.relative_to(R)/'external'/ (file+'.txt')),a,z)
for f in ['frontier/iterations/i103-algebraic-complexity-discovery.md','frontier/experiments/i103_algebraic_complexity_discovery/verify.py']:add(f)
(S/'read-manifest.json').write_text(json.dumps(reads,indent=2)+'\n')
expr=r'(?i)\bIMM\b|iterated.matrix.multiplication|depth.five|depth.5';hits=[]
for l in (S/'lexical-hits.jsonl').read_text().splitlines():
 x=json.loads(l)
 if x['query']=='imm' and re.search(expr,x['text']):hits.append(x)
(S/'refined-screen.json').write_text(json.dumps({'expression':expr,'operation':'Filter imm occurrence records by search on full line; duplicate occurrences retained','occurrences':hits,'families':dict(collections.Counter(x['path'].split('/')[1] for x in hits))},indent=2)+'\n')
e=json.loads((S/'preparation-events.json').read_text());e += [{'event':'Initial M field-transfer search in tex/conclusion.tex and then tex/*.tex returned no matches; exact build-wide search found rectangular/08-comparison.tex. First chained read stopped before later sed commands; repeated separately.'},{'event':'pdftotext returned exit 0 with Bad annotation destination warnings for lst and abt; warnings retained in external-requests.json.'}];(S/'preparation-events.json').write_text(json.dumps(e,indent=2)+'\n')
print('reads',len(reads),'refined',len(hits))
