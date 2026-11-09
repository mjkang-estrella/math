#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
if rg -n '\b(sorry|admit|native_decide|ofReduceBool|implemented_by)\b|^[[:space:]]*(axiom|unsafe)\b' lean --glob '*.lean'; then
  echo 'Rejected source token'; exit 1
fi
echo 'Source token scan passed'
