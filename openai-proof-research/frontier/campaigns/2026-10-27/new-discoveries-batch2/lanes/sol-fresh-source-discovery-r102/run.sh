#!/bin/sh
set -eu
cd "$(dirname "$0")"
exec python helper_guard.py python -u check.py
