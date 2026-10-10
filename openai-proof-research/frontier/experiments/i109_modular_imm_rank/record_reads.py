"""Preparation of explicitly completed reading records; not the verifier."""
from pathlib import Path
import json,hashlib,collections
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i109_modular_imm_rank'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
rows=[]
def rec(rel,first=1,last=None,scope='Read actual passage'):
 p=R/rel;raw=p.read_bytes();ls=raw.decode().split('\n');last=len(ls) if last is None else last
 assert 1<=first<=last<=len(ls)
 item={'path':rel,'first':first,'last':last,'line_convention':'LF; UTF-8 split on newline; one-based inclusive; one appended LF in passage hash; formfeeds remain inside lines','source_sha256':hashlib.sha256(raw).hexdigest(),'passage_sha256':hashlib.sha256(('\n'.join(ls[first-1:last])+'\n').encode()).hexdigest(),'scope':scope}
 if '/corpus/' in rel:
  item['upstream_path']=rel.split('/corpus/')[1];item['url']='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+item['upstream_path']
 rows.append(item)
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026/build/sections/'
for name in ['01-introduction.tex','02-rank.tex','03-circuits.tex','04-moments.tex','05-paths.tex','06-completion.tex']:rec(base+name,scope='Complete section read through ending; pinned premise accepted, not upstream truth audit')
rec('AGENTS.md')
rec('frontier/iterations/i106-positive-characteristic-imm.md',scope='Complete frozen original supplied verbatim in task; actual bytes compared; audit of new original claims only')
for name,ranges in {'forbes':[(220,390),(420,510),(510,620)],'agkst':[(1750,1965)],'lst':[(195,240)],'abt':[(300,365),(1670,1725)],'bera':[(94,123),(695,835)]}.items():
 for a,z in ranges:rec('frontier/sources/i106_positive_characteristic_imm/external/'+name+'.txt',a,z,scope='Retained primary comparison passage; only Forbes Lemma 5/Theorem 10 are proof-operation dependencies')
rec('frontier/sources/i109_modular_imm_rank/external/chains.txt',scope='Entire primary paper read through all theorem/proof endings and references')
rec('frontier/sources/i109_modular_imm_rank/complete-additional-instructions.txt',scope='Complete required parent directions read before work')
(S/'read-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
h=[json.loads(x) for x in (S/'lexical-hits.jsonl').read_text().splitlines()]
(S/'lexical-family-summary.json').write_text(json.dumps(dict(collections.Counter(x['path'].split('/')[1] for x in h)),indent=2)+'\n')
print({'read_passages':len(rows)})
