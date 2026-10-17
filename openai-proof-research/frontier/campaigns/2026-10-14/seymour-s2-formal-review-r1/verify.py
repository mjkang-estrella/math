#!/usr/bin/env python3
"""Read-only review identity check. Myeongjin Kang, MIT. No truth certification."""
from pathlib import Path
import argparse,hashlib,json
from audit import authenticate
H=Path(__file__).resolve().parent
IGNORED={'run','verified-run','.replays'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);args=ap.parse_args()
 m=H/'output-manifest.json';assert hashlib.sha256(m.read_bytes()).hexdigest()==args.anchor,'Wrong external review anchor'
 rows=json.loads(m.read_text())['files'];listed={x['path'] for x in rows};assert len(listed)==len(rows)
 actual=set()
 for p in H.rglob('*'):
  rel=p.relative_to(H)
  if rel.parts[0] in IGNORED:continue
  assert not p.is_symlink(),rel
  if p.is_file() and rel.as_posix()!='output-manifest.json':actual.add(rel.as_posix())
 assert actual==listed,(actual-listed,listed-actual)
 for row in rows:
  p=H/row['path'];assert p.resolve().is_relative_to(H)
  b=p.read_bytes();assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256'],row['path']
 auth=authenticate()
 print(json.dumps({'status':'PASS identity only','review_payloads':len(rows),'author_payloads':auth['exact_payload_members'],'full_graph_theorem_formalized':False}))
if __name__=='__main__':main()
