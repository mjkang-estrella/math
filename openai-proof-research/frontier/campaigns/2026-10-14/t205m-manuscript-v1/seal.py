#!/usr/bin/env python3
"""Create exact inventory. Does not assert a proof/review verdict. SPDX-License-Identifier: MIT."""
import hashlib,json,os
from pathlib import Path
from verify import scan,ancestry
root=Path(os.path.abspath(__file__)).parent
ancestry(root);files,dirs=scan(root);files.pop('manifest.json',None)
data={'packet':'t205m-manuscript-v1','status':'AUTHOR_MANUSCRIPT_READY_FOR_INDEPENDENT_REVIEW','scope':'Full unchanged T205M: every m>=2, all nonrow noncolumn labels, sharp m-1 floor; stipulated pinned source contracts.','files':files,'directories':dirs}
p=root/'manifest.json';p.write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
print(hashlib.sha256(p.read_bytes()).hexdigest())
