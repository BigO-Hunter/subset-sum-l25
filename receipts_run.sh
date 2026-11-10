#!/bin/bash
# O1-isolation landing receipts — adapted from pr52-3sum/run-build.sh pattern (SHARED.md §3).
# Three receipts: (1) full build exit 0, (2) named olean existence, (3) axiom banner
# (house triple, no sorryAx/native_decide) + sorry/native_decide grep.
# Run detached: setsid nohup ./receipts_run.sh — poll receipts/o1-<ts>/build.log.
set -u
LANE=/Volumes/Substrate-1/bigo/o1-lane
TS=$(date -u +%Y%m%dT%H%M%SZ)
REC="$LANE/receipts/o1-$TS"
mkdir -p "$REC"
exec 9>/Volumes/Substrate-1/bigo/.build.lock
flock -w 7200 9 || { echo "flock timeout" > "$REC/fatal.txt"; exit 42; }
trap "" TERM
cd "$LANE"

# Swap gate: sleep 300 loops until used <= 12GB, cap 12 loops (60 min).
for i in $(seq 1 12); do
  USED=$(sysctl vm.swapusage | sed -E 's/.*used = ([0-9.]+)M.*/\1/')
  INT=${USED%.*}
  echo "$(date -u +%H:%M:%SZ) swap_used=${INT}MB" >> "$REC/swap.log"
  [ "$INT" -le 12288 ] && break
  [ "$i" -eq 12 ] && { echo "swap gate not cleared in 60min" > "$REC/fatal.txt"; exit 43; }
  sleep 300
done

# Receipt 1: full build (exit 0 required).
lake build > "$REC/build.log" 2>&1
echo $? > "$REC/build.exit"

# Receipt 2: named oleans.
{
  stat -f "%N %z bytes %Sm" \
    .lake/build/lib/lean/SubsetSumL25/Statements/Isolation.olean \
    .lake/build/lib/lean/SubsetSumL25/Proofs/Isolation.olean 2>&1
} > "$REC/oleans.txt"

# Receipt 3: axiom banner on the two O1 theorems.
lake env lean o1_axiom_probe.lean > "$REC/axioms.txt" 2>&1
echo $? > "$REC/axioms.exit"

# Sweep: sorry / native_decide / axiom violations.
{
  echo "=== sorry/native_decide grep over SubsetSumL25/ (code lines only):"
  grep -rn "sorry\|native_decide" SubsetSumL25/ 2>/dev/null | grep -v "^\S*:[0-9]*:[0-9]*: *--" | grep -v "/-" | grep -v "^Binary" || echo "NONE"
  echo "=== axiom banner requirements:"
  grep -c "sorryAx" "$REC/axioms.txt" 2>/dev/null || true
} > "$REC/sweep.txt"

# Summary with source shas.
{
  echo "{"
  echo "  \"receipt\": \"o1-$TS\","
  echo "  \"lane\": \"o1-isolation\","
  echo "  \"branch\": \"$(git rev-parse --abbrev-ref HEAD)\","
  echo "  \"commit\": \"$(git rev-parse HEAD)\","
  echo "  \"toolchain\": \"$(cat lean-toolchain)\","
  echo "  \"mathlib_rev\": \"$(git -C .lake/packages/mathlib rev-parse HEAD)\","
  echo "  \"build_exit\": $(cat "$REC/build.exit"),"
  echo "  \"axioms_exit\": $(cat "$REC/axioms.exit"),"
  echo "  \"sha_Proofs_Isolation\": \"$(shasum -a 256 SubsetSumL25/Proofs/Isolation.lean | cut -d' ' -f1)\","
  echo "  \"sha_Statements_Isolation\": \"$(shasum -a 256 SubsetSumL25/Statements/Isolation.lean | cut -d' ' -f1)\""
  echo "}"
} > "$REC/summary.json"

echo "DONE o1-$TS" > "$REC/STATUS"
