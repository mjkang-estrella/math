import runpy
D=runpy.run_path(__file__.replace('passages.py','research.py'));globals().update({k:v for k,v in D.items() if not k.startswith('__')})
for aid in sys.argv[1:]:
 s=read(L/'sources'/str(aid+'.txt')).decode();lines=s.splitlines();indices=set()
 for n,line in enumerate(lines):
  if any(w in line.lower() for w in ['conjecture','suffix language','z-equival','bridge-column','theorem 1','theorem 2','involution']):indices.update(range(max(0,n-6),min(len(lines),n+22)))
 print('SOURCE',aid,'LINES',len(lines))
 for n in sorted(indices):print(f'{n+1}: {lines[n]}')
write('passages-'+ '-'.join(sys.argv[1:])+'.json',receipts)
print('TRUE_EXIT',0,'PID',os.getpid(),'RUSAGE',list(resource.getrusage(resource.RUSAGE_SELF)))
