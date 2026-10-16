#!/usr/bin/env python3
"""Explicitly freeze this review's output inventory. MIT, Myeongjin Kang 2026."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
rows=[]
for p in sorted(HERE.rglob('*')):
 if p.is_file() and p!=HERE/'output-manifest.json':
  data=p.read_bytes(); rows.append({'path':p.relative_to(HERE).as_posix(),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
manifest={'author':'Myeongjin Kang','affiliation':None,'scoped_verdict':'PASS','full_staircase_formalization':False,'acceptance_awarded':False,'count_action':False,'license':'Original review prose CC BY 4.0; original code MIT; copied author/third-party rights preserved','self_excluded':True,'files':rows}
(HERE/'output-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Frozen {len(rows)} output records plus self-excluded manifest')
