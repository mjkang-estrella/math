from pathlib import Path
import json,sys
p=Path(__file__).parent/'packet/private'
m=json.loads((p/'map.json').read_text())
for arg in sys.argv[1:]:
 parts=arg.split(':');k=parts[0];b=Path(m[k]).read_bytes();s=int(parts[1]) if len(parts)>1 else 0;e=int(parts[2]) if len(parts)>2 else len(b);part=b[s:e];print('\n'+k+' bytes['+str(s)+','+str(e)+')\n'+part.decode())
 with (p/'reads.jsonl').open('a') as f:f.write(json.dumps({'key':k,'start':s,'end':e})+'\n')
