#!/usr/bin/env bash
#
# Regenerate the CpcBags package from the bag rules of a cvc5 checkout, with
# the semantics of install/defs extended by bags.
#
# Usage: install/defs/bags/install-bags.sh <cvc5 checkout>
#
# The checkout must have proofs/eo/cpc/expert/rules/Bags.eo; see
# CpcBags/README.md for the cvc5 branch that does.

set -euo pipefail

if [ $# -ne 1 ]; then
  sed -n '2,9p' "$0" | sed 's/^# \{0,1\}//'
  exit 1
fi

here="$(cd "$(dirname "$0")" && pwd)"
logos="$(cd "$here/../../.." && pwd)"
cvc5="$(cd "$1" && pwd)"
rules="$cvc5/proofs/eo/cpc/expert/rules/Bags.eo"
[ -f "$rules" ] || { echo "error: $rules not found" >&2; exit 1; }

tmp="$(mktemp -d)"

# The semantics: those of install/defs with the bag additions of the patches
# here. A patch that no longer applies means install/defs changed under it; it
# is then refreshed by hand.
for f in Cpc.eos smt.eos; do
  patch -s -o "$tmp/$f" "$logos/install/defs/$f" "$here/$f.patch"
done

# The signature: CPC with the bags theory and its rules.
cat > "$tmp/CpcBags.eo" <<EOS
(include "$cvc5/proofs/eo/cpc/Cpc.eo")
(include "$rules")
EOS

"$logos/install/install-sig.sh" "$tmp/CpcBags.eo" --package CpcBags \
  --semantics "$tmp/Cpc.eos" --smt-semantics "$tmp/smt.eos" \
  --rules bags_count_non_neg bags_count_def bags_make_split bags_ext

# The compiler also writes one obligation per rule, with sorry for a proof, and
# Proofs/RuleLemmas.lean, which collects them. Both build on the checker proofs
# of Cpc/Proofs, which do not cover bags yet, so they are dropped. The rules
# are proven sound in Proofs/BagRules.lean instead.
rm -f "${logos:?}/CpcBags/Proofs/RuleLemmas.lean"
rm -rf "${logos:?}/CpcBags/Proofs/Rules"
