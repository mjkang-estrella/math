"""Write dossier/pins.json from the pinned toolchain and the frozen expanded-corpus-r96/lean. python3 -I make_pins.py"""
import hashlib, json, subprocess
from pathlib import Path
L = Path(__file__).resolve().parents[1]
R = L.parent / 'expanded-corpus-r96' / 'lean'
B = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
P = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins = {
    'lean_version': 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)',
    'lean_commit': '5045d0056413266e57c625dcd7c365b10e377c52',
    'lean_bin_reference_path': str(B), 'lean_packages_reference_path': str(P),
    'lean_sha256': sha(B / 'lean'), 'leanchecker_sha256': sha(B / 'leanchecker'),
    'mathlib_rev': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
    'lake_manifest_sha256': sha(P.parent.parent / 'lake-manifest.json'),
    'lean_module_sha256': {f.name: sha(f) for f in sorted(R.glob('*.lean'))},
    'lean_modules_source': 'expanded-corpus-r96/lean (frozen input)',
    'perm_order_txt_sha256': sha(R / 'perm-order.txt'),
}
(L / 'dossier' / 'pins.json').write_text(json.dumps(pins, indent=1) + '\n')
print(len(pins['lean_module_sha256']), pins['lean_sha256'][:12], pins['leanchecker_sha256'][:12])
