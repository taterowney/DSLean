#!/usr/bin/env bash
set -euo pipefail

cd /workspace

echo "== Solver binaries =="
gappa --help >/dev/null
sage --version >/dev/null
M2 --version >/dev/null

echo "== Lean build =="
lake exe cache get
lake build DSLean.Demos

echo "== Demo check =="
lake env lean DSLean/Demos.lean

echo "Smoke checks passed"
