from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parent
for arg in sys.argv[1:]:
 parts=arg.split('@');p=R/parts[0];b=p.read_bytes();start,end=(map(int,parts[1].split(':')) if len(parts)>1 and not parts[1].startswith('L') else (0,len(b)))
 
 if len(parts)>1 and parts[1].startswith('L'):
  lo,hi=map(int,parts[1][1:].split(':'));lines=b.splitlines(keepends=True);start=sum(map(len,lines[:lo-1]));end=sum(map(len,lines[:hi]));
 text=b[start:end].decode();print('\nFILE',parts[0],'BYTES',start,end,'OF',len(b));print(text)
 with (R/'private/r2-read-log.jsonl').open('a') as f:f.write(json.dumps({'path':parts[0],'start':start,'end':end,'sha256':hashlib.sha256(b[start:end]).hexdigest(),'kind':'tool display; semantic coverage subject to truncation disclosure'})+'\n')
