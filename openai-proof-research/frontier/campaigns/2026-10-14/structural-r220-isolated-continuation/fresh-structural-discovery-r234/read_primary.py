from pathlib import Path
import sys,json,hashlib,re
R=Path(__file__).parent;name=sys.argv[1];start=int(sys.argv[2]);end=int(sys.argv[3]);p=R/'private/primary'/(name+'.txt');b=p.read_bytes();ls=b.splitlines(keepends=True);assert 1<=start<end<=len(ls)+1
# Explicit mathematical selections; same byte parser used for boundary classification and display.
lo=sum(map(len,ls[:start-1]));hi=sum(map(len,ls[:end-1]));om=[];off=lo;out=[]
for n,l in enumerate(ls[start-1:end-1],start):
 s=l.decode().strip()
 isheader=(not s or bool(re.fullmatch(r'\d+',s)) or bool(re.search(r'^(?:\d+\s+)?(?:M\. Kapovich,?\s*B\.? (?:Leeb|Loeb)|MANIFOLDS WITHOUT CONJUGATE POINTS|S\.? IVANOV AND V\.? KAPOVITCH|Actions of discrete groups)',s,re.I)))
 editorial=bool(re.search(r'acknow|acknowleg|thank|grateful|private communicat|supported by|copyright|licen[cs]|download|e.mail|e-maih',s,re.I))
 if isheader or editorial:om.append({'start':off,'end':off+len(l),'reason':'editorial' if editorial else 'header/blank'})
 else:out.append(l)
 off+=len(l)
print('EXACT SELECTION',name,'lines',start,end,'bytes',lo,hi,'stopping boundary already classified');print(b''.join(out).decode())
with (R/'private/semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'file':p.relative_to(R).as_posix(),'start':lo,'end':hi,'line_start':start,'line_end_exclusive':end,'parser':'bytes.splitlines(keepends=True)','omissions':om,'sha256':hashlib.sha256(b).hexdigest()})+'\n')
