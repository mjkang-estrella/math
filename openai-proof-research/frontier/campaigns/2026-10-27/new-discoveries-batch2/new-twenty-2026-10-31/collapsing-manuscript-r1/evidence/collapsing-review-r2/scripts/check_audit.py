import pathlib,json,re,hashlib,collections
R=pathlib.Path(__file__).resolve().parents[1]
a=(R/'logs/ReviewAudit.log').read_text()
rows=re.findall(r'DECL (\S+) ORIGIN some \(MathDB378395\) KIND (\S+) UNSAFE (\S+) PARTIAL (\S+) BODY (\S+)',a)
axs=re.findall(r'TRANSITIVE_AXIOMS (\S+) \[(.*?)\]',a)
assert len(rows)==134 and len(set(x[0] for x in rows))==134 and len(axs)==134
assert a.count('FULL_TYPE ')==134
for n,k,u,p,b in rows:
 assert u==p=='false'
 assert k in ['def','theorem','inductive','ctor','recursor']
 assert b=='true' or k in ['inductive','ctor','recursor']
for n,v in axs:assert set(filter(None,map(str.strip,v.split(','))))<={'propext','Classical.choice','Quot.sound'}
pins=json.loads((R/'fresh/pins.json').read_text());B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
for n in ['lean','leanchecker']:assert hashlib.sha256((B/n).read_bytes()).hexdigest()==pins['binaries'][n]
manifest=json.loads((R/'fresh/source-manifest.json').read_text())
for n,h in manifest.items():assert hashlib.sha256((R/'fresh'/n).read_bytes()).hexdigest()==h
s=(R/'fresh/proof/MathDB378395.lean').read_text()
# Search executable source after removing comments; comments are not declarations.
s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool)\b',s)
for label,needle in [('Wrong','type mismatch'),('Sorry','sorry'),('Axiom','forbidden cheat'),('Perturbed','decide'),('BadOlean-correct-path','header')]:
 t=(R/f'logs/{label}.log').read_text();assert needle.lower() in t.lower(),(label,t[:600])
assert not (R/'logs/strict-build.log').read_text().strip()
out=dict(declarations=134,kinds=dict(collections.Counter(x[1] for x in rows)),allowed_axioms=['propext','Classical.choice','Quot.sound'],source_hash=manifest['proof/MathDB378395.lean'],binary_hashes=pins['binaries'],manifest_verified=True,negative_logs_matched=True)
(R/'outputs/audit.json').write_text(json.dumps(out,indent=2));print(out)
