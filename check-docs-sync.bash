#!/bin/bash
# check-docs-sync.bash — Verify that documented build-job counts match the real build
#
# Usage:
#   bash check-docs-sync.bash            # run lake build, compare against docs
#   bash check-docs-sync.bash --no-build # reuse the last `lake build` output (faster, CI)
#
# Runs a full `lake build`, extracts the real job count from Lake's own
# "Build completed successfully (N jobs)." line, then greps every doc file that is
# expected to carry that number for job-count-looking mentions ("NN jobs",
# "NN build jobs"). Prints every mismatch it finds. Does NOT edit the docs —
# prose sentences vary too much per file to rewrite safely; a human (or the AI
# following `actualiza doc` / `actualiza_documentacion` in AI-GUIDE.md) updates
# them by hand after reading this report.
#
# Wire this into: AI-GUIDE.md §"actualiza doc" step 1, and §"dame situación".

set -e

DOCS=(
    "README.md"
    "REFERENCE.md"
    "NEXT-STEPS.md"
    "CURRENT-STATUS-PROJECT.md"
)

if [ "$1" = "--no-build" ] && [ -f .last-build-output.txt ]; then
    BUILD_OUTPUT=$(cat .last-build-output.txt)
else
    echo "=== Running lake build ==="
    BUILD_OUTPUT=$(lake build 2>&1)
    echo "$BUILD_OUTPUT" > .last-build-output.txt
    echo "$BUILD_OUTPUT" | tail -5
fi

REAL_JOBS=$(echo "$BUILD_OUTPUT" | grep -oE 'Build completed successfully \([0-9]+ jobs\)' | grep -oE '[0-9]+' || true)

if [ -z "$REAL_JOBS" ]; then
    echo ""
    echo "❌ Could not determine real job count — build may have failed. See output above."
    exit 1
fi

echo ""
echo "=== Real build: $REAL_JOBS jobs ==="
echo ""
echo "=== Job counts declared in docs ==="

MISMATCH=0
for DOC in "${DOCS[@]}"; do
    [ ! -f "$DOC" ] && continue
    MATCHES=$(grep -noE '[0-9]+ (build )?jobs' "$DOC" || true)
    if [ -z "$MATCHES" ]; then
        echo "  $DOC: (no job-count mention found)"
        continue
    fi
    while IFS= read -r MATCH; do
        [ -z "$MATCH" ] && continue
        LINE="${MATCH%%:*}"
        CONTENT="${MATCH#*:}"
        NUM=$(echo "$CONTENT" | grep -oE '[0-9]+' | head -1)
        if [ "$NUM" != "$REAL_JOBS" ]; then
            echo "  ⚠️  $DOC:$LINE — declares '$NUM jobs', real build is $REAL_JOBS"
            MISMATCH=$((MISMATCH + 1))
        else
            echo "  ✅ $DOC:$LINE — $NUM jobs (matches)"
        fi
    done <<< "$MATCHES"
done

echo ""
if [ "$MISMATCH" -eq 0 ]; then
    echo "✅ All documented job counts match the real build ($REAL_JOBS jobs)."
else
    echo "⚠️  $MISMATCH mismatch(es) found. Update the flagged lines to '$REAL_JOBS jobs'."
    echo "    Note: CURRENT-STATUS-PROJECT.md may legitimately show a smaller *incremental*"
    echo "    rebuild count — only flag it if it is presented as the full-build total."
    exit 1
fi
