from pathlib import Path
import sys,json,hashlib,re,datetime
R=Path(__file__).parent
names={'22':'Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-in-Dimension-Twenty-Two-October-5-2026','sharp':'Sharpness-of-the-Cyclic-Integral-Floer-Bound-Below-the-Stable-Morse-Number-October-5-2026','orig':'Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-October-5-2026','nondeg':'A-nondegenerate-counterexample-to-the-Morse-number-Arnold-bound-September-23-2026','deg':'A-degenerate-counterexample-to-the-critical-number-Arnold-bound-September-23-2026'}
for item in sys.argv[2:]:
 bits=item.split(':');f=bits[0];p='preprints/'+names[sys.argv[1]]+'/build/'+f
 b=(R/'private/upstream'/p).read_bytes();ls=b.splitlines(keepends=True);offsets=[0]
 for l in ls:offsets.append(offsets[-1]+len(l))
 lo=int(bits[1]) if len(bits)>1 else 1;hi=int(bits[2]) if len(bits)>2 else len(ls)
 assert 1<=lo<=hi<=len(ls)
 selected=b[offsets[lo-1]:offsets[hi]];assert selected==b''.join(ls[lo-1:hi])
 print('\nEXACT',p,'lines',lo,'through',hi,'bytes',f'[{offsets[lo-1]},{offsets[hi]})','SHA256',hashlib.sha256(selected).hexdigest())
 print(selected.decode())
 with (R/'private/semantic-reads.jsonl').open('a') as out:out.write(json.dumps({'path':p,'start':offsets[lo-1],'end':offsets[hi],'first_line':lo,'last_line':hi,'sha256':hashlib.sha256(selected).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'parser':'bytes.splitlines(keepends=True)'})+'\n')
