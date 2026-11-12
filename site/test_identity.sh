#!/bin/bash
# Faithfulness test of the reconstructed site generator.
#
#   site/test_identity.sh LEAN_REPO SITE_REPO
#
# LEAN_REPO is a clone of this repository, SITE_REPO a clone of the site repository
# (asving/asving.github.io). The test exports the site folder as the original generator last wrote
# it (site commit 8e741cd, 2026-10-17), runs `refresh.py --identity` on a copy with the Lean sources
# of tag v1.1.0, and compares the two folders byte for byte. Both states are read with
# `git archive`, so the working trees do not matter and nothing is written to either repository.
#
# The one expected difference is the added lean/README.md: the published sources index links to
# that file, and the published folder did not contain it.
set -euo pipefail
[ $# = 2 ] || { echo "usage: $0 LEAN_REPO SITE_REPO" >&2; exit 2; }
lean=$1
site=$2
here=$(cd "$(dirname "$0")" && pwd)
folder=claude/splitting-type-density
site_commit=8e741cd533b761872aa187ac64f06e459064e49a
lean_tag=v1.1.0

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/published" "$tmp/rebuilt"
git -C "$site" archive "$site_commit" "$folder" | tar -x -C "$tmp/published"
cp -R "$tmp/published/." "$tmp/rebuilt"
python3 -I "$here/refresh.py" "$lean" "$tmp/rebuilt/$folder" --rev "$lean_tag" --identity

files=$(find "$tmp/published/$folder" -type f | wc -l | tr -d ' ')
found=$(cd "$tmp" && diff -rq "published/$folder" "rebuilt/$folder" || true)
expected="Only in rebuilt/$folder/lean: README.md"
if [ "$found" = "$expected" ]; then
  echo "PASS: $files published files reproduced byte for byte (site ${site_commit:0:7}, Lean $lean_tag); the only difference is the added lean/README.md"
else
  echo "FAIL: differences between the published folder and the rebuilt one:"
  echo "$found"
  exit 1
fi
