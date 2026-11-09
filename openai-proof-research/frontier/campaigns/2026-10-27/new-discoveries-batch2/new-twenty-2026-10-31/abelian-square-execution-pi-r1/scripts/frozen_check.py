#!/usr/bin/env python3
"""Verify frozen r253 input hashes (before/after gate).

Usage: python3 -I -B frozen_check.py <frozen-inputs.json> <out.json> <label>
"""
import json, hashlib, os, sys, datetime


def main():
    manifest_path, out_path, label = sys.argv[1], sys.argv[2], sys.argv[3]
    man = json.load(open(manifest_path))
    ok, mismatch, missing = [], [], []
    for path, sha in man.items():
        if not os.path.exists(path):
            missing.append(path)
            continue
        h = hashlib.sha256(open(path, 'rb').read()).hexdigest()
        if h == sha:
            ok.append(path)
        else:
            mismatch.append({'path': path, 'expected': sha, 'actual': h})
    out = {
        'label': label,
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'n_total': len(man),
        'n_ok': len(ok),
        'n_mismatch': len(mismatch),
        'n_missing': len(missing),
        'mismatch': mismatch,
        'missing': missing,
        'ok_paths': ok,
    }
    json.dump(out, open(out_path, 'w'), indent=1)
    print(json.dumps({k: out[k] for k in
                      ['label', 'utc', 'n_total', 'n_ok', 'n_mismatch', 'n_missing']},
                     indent=1))
    return 0 if (not mismatch and not missing) else 1


if __name__ == '__main__':
    sys.exit(main())
