import pathlib,json,hashlib,zipfile
r=pathlib.Path(__file__).resolve().parent;p=r/'packet'
mods=(p/'module-order.txt').read_text().splitlines(); pilots=[x for x in mods if x.startswith('MaskPilot')];mods=['MaskRUP']+pilots+[x for x in mods if x not in pilots and x!='MaskRUP']
audit='''import EndpointR6
import Control4
import Control5
import NormalizedExport
'''+''.join('import '+x+'\n' for x in pilots)+'''import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let localModules : Array String := #['''+','.join(json.dumps(x) for x in mods+['AuditR6'])+''']
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "AuditR6"
    if localModules.contains owner then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden local metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local assumption: {n}"
      | _ => pure ()
  logInfo m!"Metadata audit passed: {count} declarations"
'''
(p/'src/AuditR6.lean').write_text(audit);mods+=['AuditR6'];(p/'module-order.txt').write_text('\n'.join(mods)+'\n')
(p/'source-manifest.sha256').write_text(''.join(hashlib.sha256((p/'src'/f'{m}.lean').read_bytes()).hexdigest()+f'  src/{m}.lean\n' for m in mods))
with zipfile.ZipFile(r/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in ['guard.sh','replay.sh','module-order.txt','source-manifest.sha256']+[f'src/{m}.lean' for m in mods]:z.write(p/f,f)
with zipfile.ZipFile(r/'source-only.zip') as z:
 for n in z.namelist():
  a=pathlib.PurePosixPath(n);assert not a.is_absolute() and '..' not in a.parts
 z.extractall(r/'fresh-extracted')
 for n in z.namelist():assert (r/'fresh-extracted'/n).read_bytes()==z.read(n)
print(len(mods))
