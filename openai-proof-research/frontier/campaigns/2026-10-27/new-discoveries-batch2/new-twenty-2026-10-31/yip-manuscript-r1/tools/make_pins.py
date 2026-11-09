"""Record toolchain/dependency pins (no git commands; HEAD files read directly)."""
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
BIN = pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
FORMAL = pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
PACK = FORMAL / '.lake/packages'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ver = subprocess.run([str(BIN / 'lean'), '--version'], capture_output=True, text=True, timeout=60,
                     env={'PATH': str(BIN) + ':/usr/bin:/bin', 'HOME': str(pathlib.Path.home())}).stdout
heads = {}
for p in sorted(PACK.iterdir()):
    h = p / '.git' / 'HEAD'
    heads[p.name] = {'HEAD_file': h.read_text().strip() if h.exists() else None,
                     'build_lib_present': (p / '.lake/build/lib/lean').is_dir()}
pins = {
    'lean_version': ver,
    'lean_commit_expected': '5045d0056413266e57c625dcd7c365b10e377c52',
    'lean_bin_dir_example': str(BIN),
    'lean_packages_dir_example': str(PACK),
    'binaries': {'lean': sha(BIN / 'lean'), 'leanchecker': sha(BIN / 'leanchecker')},
    'mathlib_HEAD_read_directly_no_git_command': heads['mathlib']['HEAD_file'],
    'package_heads_read_directly': heads,
    'lake_manifest_sha256': sha(FORMAL / 'lake-manifest.json'),
    'lean_toolchain_file': (FORMAL / 'lean-toolchain').read_text().strip(),
    'dependency_manifest': json.loads((FORMAL / 'lake-manifest.json').read_text()),
    'toolchain_leanchecker_same_installation': True,
}
assert pins['lean_commit_expected'] in ver and 'version 4.34.1' in ver
assert pins['mathlib_HEAD_read_directly_no_git_command'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
(ROOT / 'pins.json').write_text(json.dumps(pins, indent=2))
print(ver.strip()); print(json.dumps({k: v['HEAD_file'] for k, v in heads.items()}, indent=0))
