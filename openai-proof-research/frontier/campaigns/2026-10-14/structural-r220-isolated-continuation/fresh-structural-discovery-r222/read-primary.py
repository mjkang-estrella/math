from pathlib import Path
import sys,json,hashlib,datetime,re
R=Path(__file__).resolve().parent;d=R/'private/primary'
for arg in sys.argv[1:]:
 k,lo,hi=arg.split(':');b=(d/(k+'.txt')).read_bytes();ls=b.splitlines(keepends=True);a=int(lo)-1;z=int(hi);assert 0<=a<z<=len(ls)
 start=sum(map(len,ls[:a]));stop=start+sum(map(len,ls[a:z]));part=b[start:stop]
 print('\nPRIMARY '+k+f' lines {a+1}..{z}; bytes [{start},{stop}) SHA256 '+hashlib.sha256(part).hexdigest())
 # Confirmed running author/title headers only; page-number-only lines are harmlessly preserved.
 omitted=[]
 for i,l in enumerate(ls[a:z],a+1):
  t=l.decode().strip().replace('\f','')
  if (k.startswith('DMSV') and ('DE LELLIS' in t and 'VALTORTA' in t or 'RECTIFIABILITY OF THE SINGULAR SET' in t or 'HARMONIC Q-VALUED MAPS' in t)) or (k=='NV' and ('AARON NABER AND DANIELE VALTORTA' in t or 'THE SINGULAR STRUCTURE AND REGULARITY' in t)) or (k=='HS' and ('JONAS HIRSCH AND LUCA SPOLAOR' in t or 'DIMENSION OF THE SINGULAR SET FOR' in t or 'J. HIRSCH AND L. SPOLAOR' in t or 'STATIONARY 2-VALUED GRAPHS' in t)) or (k=='Allard1987' and (re.fullmatch(r'[0-9 ]*W(?:ILLIAM|\.)? ?K\.? ?ALLARD[0-9 ]*',t) or 'NOTES ON THE THEORY OF VARIFOLDS' in t)) or (k=='BDLF' and ('RECTIFIABILITY OF STATIONARY VARIFOLDS' in t or 'BRENA' in t and 'LELLIS' in t and 'FRANCESCHINI' in t)) or (k=='BDD' and (bool(re.fullmatch(r'STATIONARY VARIFOLDS[ 0-9]*',t)) or 'BRENA' in t and 'DECIO' in t and 'LELLIS' in t)):
   omitted.append(i);continue
  print(l.decode(),end='')
 with (d/'semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':k,'line_start':a+1,'line_end':z,'byte_start':start,'byte_end':stop,'sha256':hashlib.sha256(part).hexdigest(),'masked_running_headers':omitted,'parser':'bytes.splitlines(keepends=True)','limit':'Text extraction; no unclaimed visual formula coverage. Truncation if any must be recovered.'})+'\n')
