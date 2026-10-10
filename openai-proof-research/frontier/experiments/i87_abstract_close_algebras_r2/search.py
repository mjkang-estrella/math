#!/usr/bin/env python3
"""Full-domain content search. Pure function when imported; CLI prints counts only."""
from pathlib import Path
import re,json,hashlib,collections
ROOT=Path(__file__).resolve().parents[3]
DOMAIN='frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'
PATTERNS={
 'trace_representation':r'Powers|trace.{0,35}(GNS|scal|uniqu)|GNS.{0,45}(trace|unitar)|essential.{0,20}ideal|densely.{0,20}finite|quasi.equival',
 'amplification_limits':r'(commutant|tensor.norm).{0,55}(amplif|continu|invar)|amplif.{0,55}(commutant|tensor.norm)|simultaneous.{0,25}(limit|norm)|normal.{0,20}extension|standard.form',
 'actual_construction':r'Pytlik|Szwarc|nonisomorph.{0,50}(close|separab)|close.{0,50}nonisomorph|finite.rank.{0,40}(perturb|deform)|relative.{0,25}weak.{0,15}inject'
}
def collect():
 domain=json.loads((ROOT/DOMAIN).read_text());rx={n:re.compile(p,re.I) for n,p in PATTERNS.items()};hits={n:[] for n in rx}
 for x in domain:
  b=(ROOT/x['local']).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256']
  for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
   for n,r in rx.items():
    if r.search(line):hits[n].append(dict(path=x['path'],local=x['local'],line=i,text=line))
 return hits
if __name__=='__main__':print(json.dumps({n:len(h) for n,h in collect().items()},sort_keys=True))
