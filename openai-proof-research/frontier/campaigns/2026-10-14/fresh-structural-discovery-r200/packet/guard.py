import fnmatch,json
from pathlib import Path
CFG=json.loads(Path(__file__).with_name("guard.json").read_text())
def denied(rel):
 s=Path(rel).as_posix().casefold()
 return s.startswith(CFG["own_root"].casefold()) or any(x in s for x in CFG["substrings"]) or any(fnmatch.fnmatchcase(s,p) for p in CFG["literals"]+CFG["twins"]+CFG["extra_patterns"])
