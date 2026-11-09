import pathlib,re,json,hashlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent
patterns={'321501':r'Conjecture.*regular|are regular','321554':r'Conjecture 1','321621':r'Conjecture 4','321728':r'Conjecture 1','321938':r'Conjecture 1.6','322014':r'Conjecture (13.9|12.9)|strongly stratified\.$','322024':r'Conjecture.*|Minimal non-faces','322081':r'Conjecture 1','322155':r'Moreover, we falsify|counterexample to','322271':r'Conjecture 8','322351':r'Conjecture 1.4','322389':r'Conjecture 1.2','322520':r'Conjecture.*Let u and v|principal coefficients. Then','322711':r'Conjecture (9|15)','322716':r'Conjecture 5.1','324363':r'Conjecture 5.24','324369':r'Theorem 2.2','325182':r'Conjecture 5.1','340762':r'Conjecture 2','352341':r'Conjecture 1'}
parts=[];inventory=[]
for f in sorted((p/'sources').glob('*.txt')):
 ident=f.name[:6]
 if ident not in patterns:continue
 lines=f.read_text().splitlines();hits=[i for i,l in enumerate(lines) if re.search(patterns[ident],l)]
 if ident=='322024':hits=[i for i in hits if '9.6' in lines[i] or 'cardinality k' in ' '.join(lines[i:i+3])][:1]
 hits=hits[:1]
 inventory.append({'file':str(f.relative_to(p)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'passage_lines_1based':[[max(0,i-1)+1,min(len(lines),i+10)] for i in hits], 'depth':'selected target passage only; no whole-body claim'})
 for i in hits:parts.append('\nFILE '+f.name+' L'+str(i+1)+'\n'+'\n'.join(lines[max(0,i-1):i+10]))
(p/'version-passages.txt').write_text('\n'.join(parts));(p/'passage-inventory.json').write_text(json.dumps(inventory,indent=2))
print('\n'.join(parts))
