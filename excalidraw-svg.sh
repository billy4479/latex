#/bin/sh

set -euxo pipefail

temp=$(mktemp)
grep -v -E '(defs)|(@font-face)|(</style>)|(<style)' "$1" | sed 's/Virgil, Segoe UI Emoji/Virgil 3 YOFF/g' > "$temp"

cat "$temp" > "$1"

