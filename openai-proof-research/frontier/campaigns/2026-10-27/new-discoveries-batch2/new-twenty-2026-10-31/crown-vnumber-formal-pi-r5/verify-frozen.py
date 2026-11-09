import json, hashlib, sys, os
d = json.load(open('frozen-inputs.json'))
bad = []
missing = []
for p, h in d.items():
    if not os.path.exists(p):
        missing.append(p); continue
    hh = hashlib.sha256(open(p,'rb').read()).hexdigest()
    if hh != h:
        bad.append((p,h,hh))
print(f"total={len(d)} ok={len(d)-len(bad)-len(missing)} mismatched={len(bad)} missing={len(missing)}")
for x in bad: print('MISMATCH', x)
for x in missing: print('MISSING', x)
