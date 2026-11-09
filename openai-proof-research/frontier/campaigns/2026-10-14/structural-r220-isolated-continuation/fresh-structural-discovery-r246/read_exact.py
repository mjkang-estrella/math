from pathlib import Path
import sys,json,re,hashlib,datetime
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r246')
P=R/'private'
mode=sys.argv[1]
for arg in sys.argv[2:]:
 name,_,spec=arg.partition(':')
 path=P/name
 assert path.is_relative_to(P) and '..' not in path.parts
 b=path.read_bytes(); ls=b.splitlines(keepends=True); offsets=[0]
 for l in ls: offsets.append(offsets[-1]+len(l))
 if mode=='map':
  print('\nBOUNDARIES',name,'LINES',len(ls),'BYTES',len(b))
  for n,line in enumerate(ls,1):
   t=line.decode('utf-8')
   if re.search(r'acknow|ackow|thank|licen[cs]e|private communication|copyright|funded|grant|personal communication',t,re.I):
    print(n,offsets[n-1],'[EDITORIAL CANDIDATE MASKED]')
   elif re.search(r'\\(?:section|subsection|subsubsection|paragraph|input|include|begin\{(?:theorem|lemma|proposition|corollary|definition|remark|proof|figure)|end\{(?:theorem|lemma|proposition|corollary|definition|remark|proof|figure))|^#+ ',t):
    print(n,offsets[n-1],t.strip())
  print('END',len(ls)+1,len(b))
 elif mode=='read':
  for s in spec.split(','):
   a,z=map(int,s.split('-')); assert 1<=a<=z<=len(ls)
   selected=b[offsets[a-1]:offsets[z]]
   assert selected==b''.join(ls[a-1:z])
   print('\nREAD',name,'LINES',a,z,'BYTES',offsets[a-1],offsets[z])
   for n in range(a,z+1): print(f'{n}: '+ls[n-1].decode('utf-8').rstrip())
   with (P/'reading.jsonl').open('a') as f: f.write(json.dumps({'file':name,'start_line':a,'end_line_inclusive':z,'byte_start':offsets[a-1],'byte_stop':offsets[z],'sha256':hashlib.sha256(selected).hexdigest(),'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'parser':'bytes.splitlines(keepends=True)'})+'\n')
