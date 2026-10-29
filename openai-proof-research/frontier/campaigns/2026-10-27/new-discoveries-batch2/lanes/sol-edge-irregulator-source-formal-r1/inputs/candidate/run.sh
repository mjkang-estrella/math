#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python context.py > context.log 2> context-guard.json
for shard in 0 1 2 3; do
 python capped_run.py python check.py "$shard" > "check-$shard.log" 2> "check-$shard-guard.json"
done
python capped_run.py python exchange.py > exchange.log 2> exchange-guard.json
python capped_run.py python independent.py > independent.log 2> independent-guard.json
python capped_run.py python finalize.py > finalize.log 2> finalize-guard.json
