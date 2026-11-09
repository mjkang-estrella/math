import pathlib,json,re,zipfile,hashlib
D=pathlib.Path(__file__).resolve().parents[1];names=[]
for p in sorted((D/'lean').glob('*.lean')):
 if p.name=='Audit.lean':continue
 names += ['Separation.'+m.group(1) for m in re.finditer(r'^(?:def|abbrev|lemma|theorem)\s+(\w+)',p.read_text(),re.M)]
(D/'lean/Audit.lean').write_text('import Certificate\n'+''.join('#print axioms '+n+'\n' for n in names))
(D/'lean/README.md').write_text('''# Literal submodular-separation packet

Separator.lean gives the general mathematical separation assertion for every d and r <= d. Points are sets of subset-indexed coordinates, allowed when all labels have cardinality <= r. phi is the set of labels contained in the input subset; it includes the empty coordinate. Separator requires submodularity on the entire Boolean lattice of allowed coordinates, strict negativity on the monomial image, and nonnegativity off it. Coordinates outside the allowed set have no role and can be assigned arbitrary values. This is the source Boolean-coordinate model with labels, rather than an arbitrary ordering of coordinates.

Certificate.lean proves no_separator_5_2 and the general negation source_existence_refuted. It uses genuine coordinate permutations and group averaging; the normalization equalities are kernel decide proofs on finite sets. It does not treat numerical LP output as an axiom. The polynomial-time evaluation requirement is unnecessary: the theorem disproves existence of any integer-valued function with the required properties, so also excludes an efficiently evaluable one. No bounded-obstruction theorem is substituted for the general negation.

Use scripts/replay.py under scripts/limited.py. Lean 4.34.1, -M3500 -j2 -DwarningAsError=true; mathlib read-only cache d13f23b723b8a846827a245b89c10fc7d3f11612. Upstream cache is trusted; no complete upstream rebuild claimed. Review still required for source fidelity, novelty and credit. SIAM version of record body was denied.
''')
with zipfile.ZipFile(D/'lean-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted((D/'lean').glob('*')):
  if p.suffix in ['.lean','.md']:
   zi=zipfile.ZipInfo('lean/'+p.name,(2026,11,5,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;z.writestr(zi,p.read_bytes())
(D/'outputs/lean-packet-manifest.json').write_text(json.dumps({'archive_sha256':hashlib.sha256((D/'lean-packet.zip').read_bytes()).hexdigest(),'declarations':names},indent=2))
