import pathlib,json,re,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
patterns={'316625':'Conjecture 5.2','317293':'Conjecture 6.1','317860':'Conjecture 3','317862':'Theorem 1.4','318385':'Conjecture 1 If','319218':'Conjecture 1','319306':'Conjecture 2','320189':'Proposition 3.5','320200':'Conjecture 1.4','320373':'Conjecture 2','320954':'McCuaig','321211':'c > 1','321317':'Conjecture 1.','321378':'Conjecture.','376550':'Conjecture 4.2','377492':'Conjecture 2','377729':'Conjecture 5.8','378274':'As Conjecture 1 was true','378319':'conjecture 2','379698':'Conjecture 1.7'}
out=[]
for i,pat in patterns.items():
 for p in sorted((L/'http').glob(i+'-*.txt')):
  s=p.read_text();m=re.search(re.escape(pat),s,re.I)
  out.append('\n### '+p.name+'\n'+(s[max(0,m.start()-60):m.start()+1000] if m else 'TARGET LOCATOR NOT FOUND; version not semantically checked.'))
(L/'version-passages.txt').write_text('\n'.join(out))
