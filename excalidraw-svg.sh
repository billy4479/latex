#/bin/sh

set -euxo pipefail

temp=$(mktemp)
svgo --pretty "$1"
grep -v -E '(defs)|(@font-face)|(</style>)|(<style)' "$1" > "$temp" # TODO: this likely doesn't work

cat "$temp" > "$1"

