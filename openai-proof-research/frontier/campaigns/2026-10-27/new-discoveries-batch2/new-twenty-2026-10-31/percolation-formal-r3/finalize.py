from pathlib import Path
import json,re,hashlib,zipfile,sys
r=Path(__file__).resolve().parent
if sys.argv[1]=='early':
 res=json.loads((r/'results.json').read_text());res['solver']={k:json.loads((r/'logs'/('solve-'+k+'.receipt.json')).read_text()) for k in ['input','normalized']};res['trimming']={k:json.loads((r/(k+'-trim-results.json')).read_text()) for k in ['input','normalized']}
 res['replay_pilot']={}
 for n in [500,2000]:
  row={'additions':n}
  for phase in ['build','check']:
   p=r/'logs'/f'{phase}-Pilot{n}.receipt.json'
   if p.exists():
    a=json.loads(p.read_text());log=(r/'logs'/f'{phase}-Pilot{n}.log').read_text();m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)
    if m:
     secs=0
     for part in m[1].split(':'):secs=60*secs+float(part)
     a['wall_seconds']=secs;a['additions_per_second']=n/secs
    row[phase]=a
  res['replay_pilot'][str(n)]=row
 (r/'results.json').write_text(json.dumps(res,indent=2))
elif sys.argv[1]=='endpoint':
 data=json.loads((r/'input-trimmed.json').read_text());rows=data['steps'][:2000]
 cs='['+','.join(f'P2000.cl_{i}' for i,_,_ in rows)+']'
 proof='(by intro d hd; cases hd)'
 for i,_,_ in reversed(rows):proof=f'(hints_cons _ _ _ (P2000.der_{i} v h) {proof})'
 text=f'''import Pilot2000
namespace Percolation.Replay
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- The exact first 2000 additions, in certificate order. Last LRAT id {rows[-1][0]}.
def prefix2000 : List CNF.NClause := {cs}
theorem prefix2000_sound (v : SatVar → Bool)
    (h : ∀ c ∈ inputCNF5, CNF.Holds v c) :
    ∀ c ∈ prefix2000, CNF.Holds (v ∘ decodeVar) c :=
  {proof}
-- This explicit frontier refutation remains UNPROVED. No formal replay of the suffix is claimed.
def ReplayFrontierUnsat5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ inputCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefix2000, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_after2000 (hs : ReplayFrontierUnsat5) : ¬ Conjecture20 := by
  apply not_conjecture20_generated
  rintro ⟨v, h⟩
  exact hs ⟨v, h, prefix2000_sound v h⟩
#print axioms not_conjecture20_after2000
end Percolation.Replay
'''
 (r/'packet/src/ReplayEndpoint.lean').write_text(text)
elif sys.argv[1]=='compare':
 log=(r/'logs/export-probe2.log').read_text();a=log.split('BEGIN_DIMACS\n')[1].split('END_DIMACS')[0]
 b=(r/'input.cnf').read_text();assert a==b
 z=zipfile.ZipFile(r.parent/'percolation-formal-r2/source-only.zip');checked=[]
 for n in z.namelist():
  if n.startswith('src/'):
   assert z.read(n)==(r/'packet'/n).read_bytes(),n;checked.append(n)
 (r/'provenance.json').write_text(json.dumps({'export_byte_identical':True,'cnf_sha256':hashlib.sha256(b.encode()).hexdigest(),'inherited_byte_identical':checked},indent=2))
elif sys.argv[1]=='package':
 mods=(r/'packet/module-order.txt').read_text().splitlines();src=r/'packet/src'
 # Archive only source modules and a resumable replay driver, no compiled files.
 with zipfile.ZipFile(r/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
  for m in mods:z.write(src/(m+'.lean'),'src/'+m+'.lean')
  for n in ['module-order.txt','replay.sh','guard.sh']:z.write(r/'packet'/n,n)
 (r/'source-only.sha256').write_text(hashlib.sha256((r/'source-only.zip').read_bytes()).hexdigest()+'\n')
 dst=r/'fresh-extracted';assert not dst.exists();dst.mkdir()
 with zipfile.ZipFile(r/'source-only.zip') as z:
  for n in z.namelist():
   p=Path(n);assert not p.is_absolute() and '..' not in p.parts
   out=dst/p;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(z.read(n))
