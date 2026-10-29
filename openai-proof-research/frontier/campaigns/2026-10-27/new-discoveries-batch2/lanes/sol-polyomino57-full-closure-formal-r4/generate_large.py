from pathlib import Path
import resource,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent
for n in [9,10,11]:
 with (L/'bench/formal'/('Layer%d.lean'%n)).open('w') as f:
  f.write('import LocalAssembly\nset_option autoImplicit false\nnamespace Polyomino57\ndef layer%d : Array (List GridPoint) := #['%n)
  for i,line in enumerate((L/'data'/('layer%d.jsonl'%n)).open()):
   P=json.loads(line)
   if i:f.write(',')
   f.write('['+','.join('(%d,%d)'%tuple(p) for p in P)+']')
  f.write(']\nend Polyomino57\n')
