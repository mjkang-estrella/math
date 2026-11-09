from pathlib import Path
import json
L=Path(__file__).resolve().parent
with (L/'failures.jsonl').open('a') as f:f.write(json.dumps(dict(action='first final verification',error='AssertionError at plantri58.tar.gz original: extracted C source incorrectly required to hash identically to its archive',correction='Verifier now distinguishes frozen identical copies from archive/PDF derivations; derivation origins remain separately manifest-hash verified',scientific_effect='none; exact graph/sign checks already passed'))+'\n')
