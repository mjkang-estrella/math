from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
import sys
raw=json.loads((L/(sys.argv[1] if len(sys.argv)>1 else 'development3')/'closure-raw.json').read_text())
O=L/'original';S=L/'source'
def span(data,r):
 lines=data.decode().splitlines(keepends=True)
 a=sum(map(len,lines[:r['startLine']-1]))+r['startColumn']
 b=sum(map(len,lines[:r['endLine']-1]))+r['endColumn']
 return data.decode()[a:b].encode()
evidence=[]
for row in raw['closure']:
 f=row['module']+'.lean'
 assert (O/f).is_file(),f
 old=(O/f).read_bytes();new=(S/f).read_bytes()
 # Closure modules are completely unchanged, so their compiler ranges apply to both.
 assert old==new,f
 assert row['range'] is not None,row
 a=span(old,row['range']);b=span(new,row['range']);assert a==b
 evidence.append(dict(row,old_sha256=sha(a),new_sha256=sha(b),bytes=len(a),identical=True))
closure={r['name'] for r in raw['closure']}
changedmods={'NormalForm','TraceAction','AutomatonSemantics','MachineInvariant'}
splitmods={p.stem for p in S.glob('Spectral*.lean') if p.stem!='SpectralDefinitions'} | changedmods
moved=[r for r in raw['packetDeclarations'] if r['module'] in splitmods]
assert all(r['name'] not in closure for r in moved)
# Code-generation-only changes have no altered logical declaration bodies.
for m in changedmods:
 old=(O/(m+'.lean')).read_text();new=(S/(m+'.lean')).read_text()
 restored=new.replace('noncomputable section\n','')
 restored=re.sub(r'(?m)^noncomputable def (Movable|Clean|pluck|frontState|Accept|run)( | :)',r'def \1\2',restored)
 assert restored==old,m
baseline=json.loads((L/'logs/early/closure-raw.json').read_text())
original_changed=[r for r in baseline['packetDeclarations'] if r['module'] in changedmods]
assert all(r['name'] not in closure for r in original_changed)
files=[]
for p in sorted(O.glob('*.lean')):
 n=S/p.name
 same=p.read_bytes()==n.read_bytes()
 assert same or p.name in {'SpectralWitness.lean','NormalForm.lean','TraceAction.lean','AutomatonSemantics.lean','MachineInvariant.lean'}
 files.append({'file':p.name,'original_sha256':sha(p.read_bytes()),'new_sha256':sha(n.read_bytes()),'identical':same})
# Original matrix/data/topology declaration command blocks map to the new sources.
text=(O/'SpectralWitness.lean').read_text()
pattern=r'(?m)^(?:noncomputable )?(?:def|theorem) (\w+)'
starts=list(re.finditer(pattern,text));original=[]
for i,m in enumerate(starts):
 stop=starts[i+1].start() if i+1<len(starts) else text.index('end ActualSpectra330264',m.start())
 block=text[m.start():stop]
 # Ignore trailing #print commands/comments; Lean metadata still lists every generated declaration.
 name='ActualSpectra330264.'+m[1]
 assert name not in closure
 target=next(r['module'] for r in moved if r['name']==name)
 newtext=(S/(target+'.lean')).read_text()
 newstart=re.search(r'(?m)^(?:noncomputable )?(?:def|theorem) '+re.escape(m[1])+r'\b',newtext).start()
 header=lambda b:re.split(r'\s*(?::=|\bwhere\b)',b,maxsplit=1)[0]
 oldheader=header(block);newheader=header(newtext[newstart:])
 assert oldheader==newheader,name
 original.append({'name':name,'outside_closure':True,'original_block_sha256':sha(block.encode()),
   'original_header_sha256':sha(oldheader.encode()),'new_header_sha256':sha(newheader.encode()),'header_identical':True,
   'new_modules':sorted({r['module'] for r in moved if r['name']==name})})
out={'definition':'Endpoint plus packet constants in its type, transitively through their types and values; endpoint proof is not a seed.',
'computed_on':'restructured compiled Endpoint; original module exceeded wall cap',
'endpoint_name':'MathDB330264.conjecture_false','closure':evidence,
'all_closure_modules_byte_identical':True,'moved_or_new_packet_declarations':moved,
'original_changed_module_declarations':original_changed,
'original_spectral_declarations':original,'file_comparison':files}
(L/'statement-closure.json').write_text(json.dumps(out,indent=2)+'\n')
report=['# File preservation report','', 'GroupSemantics and Endpoint contain the complete statement closure and remain entirely byte-identical. Three generated matrix proof helpers inherit the source span of their unchanged parent matrix declaration.','', '| File | Preservation |','|---|---|']
for r in files:report.append('| '+r['file']+' | '+('Byte-identical' if r['identical'] else ('Added noncomputable section and explicit noncomputable modifiers as needed; logical bodies unchanged; outside closure' if r['file'][:-5] in changedmods else 'Split; nine proofs assembled from row certificates; all declarations outside statement closure'))+' |')
for p in sorted(S.glob('*.lean')):
 if not (O/p.name).exists():report.append('| '+p.name+' | New helper or relocated declarations; no closure member |')
report+=['','The JSON records compiler-reported source spans, extracted byte counts and both hashes for every closure member. Every original SpectralWitness declaration and every compiler-recorded moved/generated declaration is checked outside the closure.']
(L/'PRESERVATION.md').write_text('\n'.join(report)+'\n')
print('closure',len(evidence),'moved/new declarations',len(moved),'original spectral declarations',len(original))
