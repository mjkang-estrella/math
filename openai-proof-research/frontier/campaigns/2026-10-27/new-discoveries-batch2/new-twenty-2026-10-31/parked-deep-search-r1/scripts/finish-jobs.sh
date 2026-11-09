#!/bin/bash
D=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/parked-deep-search-r1
cd "$D" || exit 1
./scripts/run.sh python3 -I scripts/encode.py "$D" divine 4096 > logs/encode-divine-4096.log 2>&1
./scripts/run.sh /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical -t 85 outputs/divine-4096.cnf > logs/divine-4096.log 2>&1
./scripts/run.sh python3 -I scripts/check.py "$D" model divine-4096 > logs/verify-divine-4096.log 2>&1
./scripts/run.sh python3 -I scripts/registry-screen.py "$D" > logs/registry-screen.log 2>&1
mapfile -t urls < outputs/registry-urls.txt
./scripts/run.sh python3 -I scripts/fetch.py "$D" "${urls[@]}" > logs/registry-candidates.log 2>&1
./scripts/run.sh python3 -I scripts/registry-screen.py "$D" >> logs/registry-screen.log 2>&1
./scripts/run.sh python3 -I scripts/fetch.py "$D" 'https://api.github.com/search/repositories?q=%221810.01225%22' 'https://arxiv.org/abs/2609.07855' > logs/registry-second.log 2>&1
./scripts/run.sh python3 -I scripts/encode_complement.py "$D" cube 27 > logs/encode-cube-complement-27.log 2>&1
mv outputs/cube-27.cnf outputs/cube-complement-27.cnf
mv outputs/cube-27.json outputs/cube-complement-27.json
./scripts/run.sh /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical --lrat --no-binary -t 85 outputs/cube-complement-27.cnf outputs/cube-complement-27.lrat > logs/cube-complement-27.log 2>&1
