"""Independent root audit of final extracted replay logs and source integrity."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parent
F=R/'extracted/formal'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=json.loads((F/'replay-modules.json').read_text())
audits=json.loads((F/'audit-modules.json').read_text())
assert len(mods)==437 and len(audits)==22
selected=[]
for m in audits:
 s=(F/(m+'.lean')).read_text()
 imports=re.findall(r'^import (.+)$',s,re.M)
 assert set(mods)<=set(imports)
 p=re.search(r'if (\[.*?\])\.contains env.header.moduleNames',s)
 assert p
 selected.extend(json.loads(p.group(1)))
 assert 'env.constants.toList.filterMap' in s and 'env.getModuleIdxFor?' in s
 assert 'info.isUnsafe' in s and 'repr d.safety' in s
 assert '#check' in s and '#print axioms' in s
assert len(selected)==len(set(selected))==437 and set(selected)==set(mods)
names={};endpoints={};axiom_union=set()
def examine(block):
 if not block:return
 header=block[0].split('|')
 assert len(header)==6 and header[0]=='DECL' and header[2]=='ORIGIN' and header[4:] == ['UNSAFE','false']
 n,origin=header[1],header[3]
 assert n not in names and origin in mods
 names[n]=origin
 assert any(t in block for t in ['SAFETY|'+n+'|Lean.DefinitionSafety.safe','SAFETY|'+n+'|nondefinition'])
 pattern=re.compile(r'^@?'+re.escape(n)+r'(?:\.\{[^}]*\})?(?:\s|$)')
 typ=[t for t in block if pattern.match(t)]
 assert len(typ)==1,(n,'actual type missing',typ)
 text='\n'.join(block)
 assert '⋯' not in text
 marker="'"+n+"'"
 al=[i for i,t in enumerate(block) if t.startswith(marker) and ('depends on axioms:' in t or 'does not depend on any axioms' in t)]
 assert len(al)==1
 a=' '.join(block[al[0]:])
 if 'does not depend on any axioms' in a:vals=set()
 else:
  v=a.split('depends on axioms:',1)[1]
  assert '[' in v and ']' in v
  v=re.sub(r'\.\{[^}]*\}','',v[v.index('[')+1:v.index(']')])
  vals={t.strip() for t in v.split(',') if t.strip()}
 assert vals<={'propext','Classical.choice','Quot.sound'},(n,vals)
 axiom_union.update(vals)
 if n in ['Assembly.literal_endpoint','Assembly.sorted_clamped_bound','Assembly.n22671','Assembly.query_of_neg_bound']:
  endpoints[n]=typ[0]
for m in audits:
 block=[]
 with (F/'logs'/(m+'.log')).open() as f:
  for raw in f:
   s=raw.strip()
   if s.startswith('DECL|'):
    examine(block);block=[s]
   elif block:block.append(s)
 examine(block)
assert len(names)==35654 and len(set(names.values()))==436
assert set(names.values())==set(mods)-{'Dag168'}
assert endpoints['Assembly.literal_endpoint']=='Assembly.literal_endpoint : FloorSums.LiteralEndpoint'
assert endpoints['Assembly.sorted_clamped_bound']=='Assembly.sorted_clamped_bound : FloorSums.SortedClampedBound'
assert hashlib.sha256('\n'.join(sorted(names)).encode()).hexdigest()=='7abfdce5f2b7e1d6ba7df2fc0de7ee9a96faa975f113e04b512bfd42008a668b'
receipts=[]
for m in mods+audits:
 j=json.loads((F/'logs'/(m+'.guard.json')).read_text())
 assert j['exit_code']==0 and j['reason'] is None
 assert j['sampled_peak_group_rss']<=2800*1024**2 and j['wall_seconds']<=230
 receipts.append(j)
manifest=json.loads((R/'extracted/SOURCE-MANIFEST.json').read_text())
assert len(manifest)==550
for n,h in manifest.items():assert digest(R/'extracted'/n)==h,n
for row in json.loads((R/'bindings.json').read_text()):
 for k in ['original','copy']:assert digest(Path(row[k]))==row['sha256']
out={'status':'PASS','actual_declarations':len(names),'actual_origins':len(set(names.values())),'math_modules':len(mods),'audit_modules':len(audits),'serial_invocations':len(receipts),'endpoints':endpoints,'transitive_axioms':sorted(axiom_union),'unchanged_packet_payloads':len(manifest),'source_bindings_reverified':3,'scope':'Root independently parsed actual fresh kernel outputs and exhaustive origin selection; not priority or campaign acceptance.'}
(R/'root-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
