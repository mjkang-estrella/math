from pathlib import Path
import json
r=Path(__file__).resolve().parents[1];rows=json.loads((r/'reconciliation.json').read_text())['per_support']
lines=['import NutInterface','import CheckedGraphIso','namespace Nut8','def orderedTreeCheck (code : Nat) (order parents : List Nat) : Bool :=', '  decide (order.Perm (List.range 8)) && decide (parents.length = 8) &&', '    (List.range 8).all (fun i => if i = 0 then true else', '      decide (parents[i]?.getD 8 < i) &&', '      graphBit 8 code (order[parents[i]?.getD 8]?.getD 8) (order[i]?.getD 8))','end Nut8']
# OrderedTreeCheck.lean is maintained by hand, including its soundness proof.
mods=['OrderedTreeCheck']
for start in range(0,len(rows),10):
 name=f'CatalogueTrees{start//10:03d}';mods.append(name)
 lines=['import OrderedTreeCheck',f'namespace Nut8.{name}','def records : List (Nat × List Nat × List Nat) := [']
 lines += [f"({x['code']}, {x['bfs_order']}, {x['parents']})"+(',' if k+1<min(start+10,len(rows)) else '') for k,x in enumerate(rows[start:start+10],start)]
 lines += [']','theorem checked : records.all (fun r => orderedTreeCheck r.1 r.2.1 r.2.2) = true := by','  decide +kernel',f'end Nut8.{name}']
 (r/'formal'/(name+'.lean')).write_text('\n'.join(lines)+'\n')
name='CatalogueTrees';lines=['import '+m for m in mods[1:]]+['namespace Nut8','def catalogueTreeRecords : List (Nat × List Nat × List Nat) :=']
lines+=['  '+' ++ '.join(m+'.records' for m in mods[1:]),'theorem catalogueTreeCodes : catalogueTreeRecords.map Prod.fst = GraphClosure7_000.targets := by','  decide +kernel','theorem catalogueTrees_checked : catalogueTreeRecords.all (fun r => orderedTreeCheck r.1 r.2.1 r.2.2) = true := by','  simp only [catalogueTreeRecords, List.all_append]']
lines+=['  simp only ['+', '.join(m+'.checked' for m in mods[1:])+', Bool.and_self]','end Nut8']
old=(r/'formal/CatalogueTrees.lean').read_text() if (r/'formal/CatalogueTrees.lean').exists() else ''
marker='namespace Nut8\n\ntheorem catalogue_ordered_tree'
extra=marker+old.split(marker,1)[1] if marker in old else ''
(r/'formal/CatalogueTrees.lean').write_text('\n'.join(lines)+'\n'+extra);mods.append('CatalogueTrees')
(r/'tree-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
