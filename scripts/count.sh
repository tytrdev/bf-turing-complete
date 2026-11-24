#!/bin/sh
# Non-whitespace characters per proof version (tests excluded; Core is shared and not counted).
cd "$(dirname "$0")/../BfTuringComplete" || exit 1
for d in Reference Golf Exposition Elegant; do
  [ -d "$d" ] || continue
  n=$(find "$d" -name '*.lean' ! -name '*Test*.lean' -exec cat {} + | tr -d '[:space:]' | wc -c)
  printf '%-11s %8d\n' "$d" "$n"
done
