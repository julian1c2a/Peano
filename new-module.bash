#!/bin/bash
# new-module.bash — Create a new Lean 4 module from _template.lean
#
# Usage:
#   bash new-module.bash ModuleName
#   bash new-module.bash SubDir/ModuleName
#
# Creates:  Peano/ModuleName.lean  (from _template.lean)
# Updates:  Peano.lean                   (adds import line)
# Unlocks:  Peano.lean for editing (re-locks after update)

set -e

if [ $# -eq 0 ]; then
    echo "Usage: bash new-module.bash ModuleName"
    echo "       bash new-module.bash SubDir/ModuleName"
    exit 1
fi

MODULE_ARG="$1"

# Detect project name from lakefile.lean (lean_lib name)
PROJECT_NAME=$(grep -E 'lean_lib\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
if [ -z "$PROJECT_NAME" ]; then
    PROJECT_NAME=$(grep -E '^lean_lib\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
fi
if [ -z "$PROJECT_NAME" ]; then
    echo "Error: Could not detect project name from lakefile.lean"
    exit 1
fi

# Detect module directory from globs line
MODULE_DIR=$(grep -oE 'Glob\.submodules\s+`(\w+)' lakefile.lean 2>/dev/null | sed 's/.*`//' | head -1)
if [ -z "$MODULE_DIR" ]; then
    MODULE_DIR="${PROJECT_NAME}"
fi

# Convert path argument to file path and import name
MODULE_PATH="${MODULE_ARG//./\/}"
TARGET_FILE="${MODULE_DIR}/${MODULE_PATH}.lean"
IMPORT_NAME="${MODULE_DIR}.${MODULE_ARG//\//.}"
NAMESPACE_NAME="Peano.${MODULE_ARG//\//.}"

# Check if file already exists
if [ -f "$TARGET_FILE" ]; then
    echo "Error: '$TARGET_FILE' already exists."
    exit 1
fi

# Create parent directory if needed
mkdir -p "$(dirname "$TARGET_FILE")"

# Create from template, substituting names
TEMPLATE="${MODULE_DIR}/_template.lean"
if [ ! -f "$TEMPLATE" ]; then
    echo "Error: Template '$TEMPLATE' not found."
    exit 1
fi

# Get current year for copyright
YEAR=$(date +%Y)
AUTHOR=$(git config user.name 2>/dev/null || echo "Julián Calderón Almendros")

sed \
    -e "s/Copyright (c) 2026/Copyright (c) ${YEAR}/" \
    -e "s/Author: Julián Calderón Almendros/Author: ${AUTHOR}/" \
    -e "s/Peano\.ModuleName/${NAMESPACE_NAME}/g" \
    -e "s/import Peano\.PeanoNatLib/import ${MODULE_DIR}.PeanoNatLib/" \
    "$TEMPLATE" > "$TARGET_FILE"

echo "✅ Created: $TARGET_FILE"

# Add import to root module
ROOT_FILE="${PROJECT_NAME}.lean"
IMPORT_LINE="import ${IMPORT_NAME}"

if grep -Fqx "$IMPORT_LINE" "$ROOT_FILE" 2>/dev/null; then
    echo "   Import already in $ROOT_FILE (skipped)"
else
    # Unlock root file if locked
    WAS_LOCKED=false
    if grep -Fxq "$ROOT_FILE" locked_files.txt 2>/dev/null; then
        WAS_LOCKED=true
        bash git-lock.bash unlock "$ROOT_FILE"
    fi

    # Find the last import line and insert after it
    LAST_IMPORT=$(grep -n '^import ' "$ROOT_FILE" | tail -1 | cut -d: -f1)
    if [ -n "$LAST_IMPORT" ]; then
        sed -i "${LAST_IMPORT}a\\${IMPORT_LINE}" "$ROOT_FILE"
    else
        echo "$IMPORT_LINE" >> "$ROOT_FILE"
    fi
    echo "✅ Added import to $ROOT_FILE"

    # Re-lock if it was locked
    if [ "$WAS_LOCKED" = true ]; then
        bash git-lock.bash lock "$ROOT_FILE"
    fi
fi

echo ""
echo "Next steps:"
echo "  1. Edit '$TARGET_FILE'"
echo "  2. After completion, lock it: bash git-lock.bash lock $TARGET_FILE"
echo "  3. Project into REFERENCE.md (see AI-GUIDE.md §12)"
