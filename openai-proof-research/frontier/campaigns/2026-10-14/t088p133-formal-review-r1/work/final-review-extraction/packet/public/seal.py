#!/usr/bin/env python3
"""Seal this original review packet; no inputs outside review mutated. MIT, 2026 Myeongjin Kang."""
import hashlib,json,stat
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
def record(p):
 s=p.lstat();assert not p.is_symlink()
 r={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'kind':'dir' if p.is_dir() else 'file'}
 if p.is_file():r.update(bytes=s.st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 return r
def main():
 entries={str(p.relative_to(ROOT)):record(p) for p in [ROOT/'packet',*sorted((ROOT/'packet').rglob('*'))] if p!=ROOT/'packet/MANIFEST.json'}
 m={'format':1,'candidate':'T088P133','stage':'independent scoped formal review','round':1,'entries':entries,'exclusions':['work/'],'private_bodies_included':False,'compiled_dependencies_included':False}
 mp=ROOT/'packet/MANIFEST.json';mp.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
 h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 f={'candidate':'T088P133','stage':'FIRST_INDEPENDENT_SCOPED_FORMAL_REVIEW','round':1,'verdict':'PASS_SCOPED_SUPPORT','required_repairs':[],'full_theorem_formalized':False,'runner':'Codex / GPT-6.1-Sol / high / default service tier','manifest_sha256':h(mp),'outside_report_sha256':h(ROOT/'REPORT.md'),'support_declarations':21,'control_declarations':20,'review_declarations':15,'axioms':['propext','Classical.choice','Quot.sound'],'publication':'STOPPED','limits':'Formal deterministic support only; no correctness/contribution/acceptance/count/release verdict.'}
 fp=ROOT/'FINAL.json';fp.write_text(json.dumps(f,indent=2)+'\n')
 print(json.dumps({'FINAL.json':h(fp),'packet/MANIFEST.json':h(mp),'REPORT.md':h(ROOT/'REPORT.md'),'entries':len(entries)},indent=2))
if __name__=='__main__':main()
