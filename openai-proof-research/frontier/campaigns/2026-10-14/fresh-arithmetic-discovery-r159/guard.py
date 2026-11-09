from pathlib import Path
import json,fnmatch,os
ROOT=Path("frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r159")
POLICY=json.loads((ROOT/"packet/private/guard-policy.json").read_text())
def excluded(path):
 p=Path(path).as_posix().casefold()
 return p.startswith(POLICY["own_root"].casefold()) or any(s in p for s in POLICY["substrings"]) or any(fnmatch.fnmatchcase(p,w) for w in POLICY["wildcards"]+POLICY["additional_wildcards"])
def eligible_files(start):
 if excluded(start): return
 for base,dirs,files in os.walk(start):
  dirs[:]=sorted(d for d in dirs if not excluded(Path(base)/d) and not (Path(base)/d).is_symlink())
  for name in sorted(files):
   p=Path(base)/name
   if not excluded(p) and not p.is_symlink(): yield p
