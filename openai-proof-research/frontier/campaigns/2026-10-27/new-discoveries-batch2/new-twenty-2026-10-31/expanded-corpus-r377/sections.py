import runpy
D=runpy.run_path(__file__.replace('sections.py','research.py'));globals().update({k:v for k,v in D.items() if not k.startswith('__')})
for arg in sys.argv[1:]:
 aid,lo,hi=arg.split(':');lines=read(L/'sources'/str(aid+'.txt')).decode().splitlines();print('SOURCE',aid,lo,hi)
 for n in range(int(lo)-1,min(int(hi),len(lines))):print(str(n+1)+': '+lines[n])
write('sections-'+str(os.getpid())+'.json',receipts);print('TRUE_EXIT',0,'PID',os.getpid(),'RUSAGE',list(resource.getrusage(resource.RUSAGE_SELF)))
