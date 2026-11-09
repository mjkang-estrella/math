from pathlib import Path
import sys,json,re,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r238');D=R/'private/primary'
k,lo,hi=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]);b=(D/(k+'.txt')).read_bytes();a=b.splitlines(keepends=True);o=[0]
for l in a:o.append(o[-1]+len(l))
assert 1<=lo<=hi<=len(a)
headers={
'DL1991':r'^(?:[0-9]+\s+R\s*\.|Global Solutions of Boltzmann|R\s*\.\s*J\s*\.\s*DIPERNA)',
'LM2010':r'^(?:[0-9]+\s+(?:C\. D\.|C\. David)|From the Boltzmann equation|C\. D\. Levermore and N\. Masmoudi)',
'GPV2009':r'^(?:[0-9]+\s+I\. M\. GAMBA|MAXWELLIAN BOUNDS FOR THE BOLTZMANN EQUATION)',
'DHWY2017':r'^(?:[0-9]+\s+RENJUN|THE BOLTZMANN EQUATION WITH LARGE AMPLITUDE INITIAL DATA)',
'GLPS1988':r'^(?:[0-9]+\s+GOLSE|REGULARITY\s*OF\s*A\s*TRANSPORT\s*EQUATION)',
'BGL-near':r'^(?:[0-9]+\s+CLAUDE BARDOS|BOLTZMANN EQUATION NEAR GLOBAL MAWELLIANS)',
'MW1999':r'^(?:[0-9]+\s+S\. MISCHLER|ON THE SPATIALLY HOMOGENEOUS BOLTZMANN EQUATION|Annales de|Vol\.)'}
mask=[];out=[]
for n in range(lo,hi+1):
 s=a[n-1].decode()
 if re.search(headers.get(k,r'(?!)'),s.strip(),re.I):mask.append(n);continue
 # A matched editorial line stops extraction instead of consuming a continuation.
 if re.search(r'acknow|aknow|licen[cs]e|copyright|all rights|download|communicated by|private communication|personal communication|thank|supported by|e-mail|email:|©',s,re.I):raise RuntimeError(f'editorial boundary at {n}; select separately')
 out.append(s)
rec={'id':k,'source_sha256':hashlib.sha256(b).hexdigest(),'line_start':lo,'line_end_inclusive':hi,'byte_start':o[lo-1],'byte_end_exclusive':o[hi],'masked_running_headers':mask,'parser':'bytes.splitlines(keepends=True)','scope':'selected mathematical body only; not whole-paper coverage'}
with (D/'reads.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(json.dumps(rec));print(''.join(out))
