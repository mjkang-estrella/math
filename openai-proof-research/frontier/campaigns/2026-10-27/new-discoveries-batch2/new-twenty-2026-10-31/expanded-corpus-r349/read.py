inventory=[]
for f in sorted((P/'texts').glob('*.txt')):
 s=f.read_text(); windows=[]
 for pat in ['Conjecture','conjecture','dominating matching','weakly even','greedy','Noetherian']:
  for m in list(re.finditer(re.escape(pat),s))[:6]:
   a=max(0,m.start()-180);b=min(len(s),m.end()+1200)
   if not any(a>=v[0] and b<=v[1] for v in windows):windows.append((a,b))
 windows=sorted(windows);out='\n'.join(f'[{a}:{b}] '+s[a:b] for a,b in windows);write('passages/'+f.name,out);inventory.append({'path':str(f.relative_to(P)),'sha256':h(f.read_bytes()),'read_windows':windows,'depth':'targeted passages, not entire proof'})
 print('FILE',f.name,'LENGTH',len(s));print(out[:14000])
jwrite('read-inventory-initial.json',inventory)
