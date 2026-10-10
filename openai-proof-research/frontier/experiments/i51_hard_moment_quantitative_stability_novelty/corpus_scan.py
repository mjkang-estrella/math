import sys
sys.dont_write_bytecode=True
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i51_hard_moment_quantitative_stability_novelty';C='frontier/sources/i14_spectral_width_novelty_r3/corpus'
patterns=[r'quantitative.{0,80}logarithmic.{0,40}(Brunn|Minkowski)|logarithmic.{0,80}stability|stability.{0,80}logarithmic',r'finite.defect.{0,50}moment|moment.{0,50}product.{0,50}stability|radial.{0,30}BV|transverse.{0,30}averag',r'Brunn.{0,50}Minkowski|cone.volume|moment measure']
rows=[]
for i,p in enumerate(patterns):
 z=subprocess.run(['rg','--no-ignore','-n','-i',p,C],cwd=R,capture_output=True);file=f'corpus-search-{i}.txt';(S/file).write_bytes(z.stdout)
 rows.append({'pattern':p,'output':file,'returncode':z.returncode,'lines':len(z.stdout.splitlines()),'replay':'sorted line multiset, preserving duplicates'})
(S/'corpus-search.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
# Preserve exact author replay source, changing only nondeterministic comparison in memory.
p=R/'frontier/experiments/i49_hard_moment_quantitative_stability/verify.py';src=p.read_text();old="assert run.stdout==(S/r['output']).read_bytes()";new="assert sorted(run.stdout.splitlines())==sorted((S/r['output']).read_bytes().splitlines())"
assert src.count(old)==1
z=subprocess.run([sys.executable,'-B','-c',"__file__="+repr(str(p))+"\n"+src.replace(old,new)],cwd=R,capture_output=True)
rec={'kind':'order-normalized in-memory I49 replay; NOT unmodified verifier','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'original':old,'replacement':new,'disk_files_modified':False,'returncode':z.returncode,'stdout':z.stdout.decode(),'stderr':z.stderr.decode()}
(S/'i49-normalized-replay.json').write_text(json.dumps(rec,indent=2)+'\n');print(z.stdout.decode());print(z.stderr.decode());assert z.returncode==0
