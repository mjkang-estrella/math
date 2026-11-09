from pathlib import Path
r=Path(__file__).resolve().parent
old='''    liftCoreM <| addDecl (.defnDecl { name, levelParams := [],
      type := mkConst ``MaskRUP.Mask, value := maskE p n,
      hints := .abbrev, safety := .safe })'''
new='''    liftCoreM <| addDecl (.defnDecl { name := name, levelParams := [], type := mkConst ``MaskRUP.Mask, value := maskE p n, hints := .abbrev, safety := .safe })'''
for f in [r/'optimize-r8.py',r/'packet/src/MaskChainBuildR8.lean',r/'optimized-extracted/src/MaskChainBuildR8.lean']:
 t=f.read_text();assert old in t;f.write_text(t.replace(old,new))
