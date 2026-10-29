#!/bin/sh
set -eu
cd "$(dirname "$0")"
exec python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python check.py
