from pathlib import Path
import hashlib
r=Path(__file__).resolve().parent
b=(r/'results.json').read_bytes();(r/'optimized-scaling-measurements.json').write_bytes(b);assert hashlib.sha256(b).digest()==hashlib.sha256((r/'optimized-scaling-measurements.json').read_bytes()).digest()
