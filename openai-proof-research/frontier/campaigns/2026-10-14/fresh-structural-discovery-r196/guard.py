import fnmatch,json
from pathlib import Path
ROOT=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r196")
POLICY=json.loads((ROOT/"private/isolation-policy.json").read_text())
def excluded(path):
    s=Path(path).as_posix().casefold()
    return any(x.casefold() in s for x in POLICY["full_path_substrings"]) or any(fnmatch.fnmatchcase(s,p.casefold()) for k in ("literal_wildcards","no_r_twins","additional_patterns") for p in POLICY[k])
