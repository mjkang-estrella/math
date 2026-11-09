from pathlib import Path
import json,hashlib,re,subprocess,sys,os,zipfile
L=Path(__file__).resolve().parent
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def revision(p):
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  r=h[5:];f=g/r
  h=f.read_text().strip() if f.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+r))
 return h
def checkpins():
 manifest=json.loads((L/'administrative/lake-manifest.json').read_text())
 assert len(manifest['packages'])==9
 pins=[]
 for p in manifest['packages']:
  path=P/'.lake/packages'/p['name'];actual=revision(path);assert actual==p['rev'],p
  pins.append(dict(name=p['name'],revision=actual,path=str(path)))
 assert next(p['revision'] for p in pins if p['name']=='mathlib')=='d13f23b723b8a846827a245b89c10fc7d3f11612'
 assert sha(P/'lake-manifest.json')==sha(L/'administrative/lake-manifest.json')
 return pins
