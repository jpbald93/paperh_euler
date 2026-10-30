#!/bin/bash
# Gate for the EulerIneq Lean formalisation (Euler's theorem and the inequalities around it). Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="EulerIneq"
LIB="EulerIneq"
REQUIRED="EulerIneq.area EulerIneq.semiperimeter EulerIneq.euler EulerIneq.four_mul_area_mul_circumradius_sub EulerIneq.euler_inequality EulerIneq.eq_zero_of_pos_mul_sq EulerIneq.sum_three_eq_zero EulerIneq.euler_inequality_eq_iff EulerIneq.euler_excenter EulerIneq.hf_identity EulerIneq.hf_L_nonneg EulerIneq.hadwiger_finsler EulerIneq.hadwiger_finsler_eq_iff EulerIneq.weitzenboeck EulerIneq.weitzenboeck_eq_iff EulerIneq.core_identity EulerIneq.fundamental_quartic EulerIneq.gerretsen EulerIneq.dist_circumcenter_centroid_sq EulerIneq.dist_circumcenter_orthocenter_sq EulerIneq.dist_incenter_centroid_sq EulerIneq.gram EulerIneq.sideLen EulerIneq.sideLen_zero EulerIneq.sideLen_one EulerIneq.sideLen_two EulerIneq.side_pos EulerIneq.height_sq_mul EulerIneq.circumradius_sq_mul EulerIneq.two_mul_area_sq EulerIneq.area_nonneg EulerIneq.height_mul_sideLen EulerIneq.area_pos EulerIneq.four_mul_circumradius_mul_area EulerIneq.excenterWeightsUnnorm_eq EulerIneq.excenterWeights_eq EulerIneq.exradius_eq EulerIneq.incenter_weights EulerIneq.inradius_eq EulerIneq.sum_signed_sideLen_pos EulerIneq.dist_affineCombination_sq EulerIneq.dist_affineCombination_circumcenter_sq EulerIneq.dist_affineCombination_affineCombination_sq EulerIneq.centroid_eq_affineCombination EulerIneq.triangle_pos EulerIneq.inradius_mul EulerIneq.pedoe_identity EulerIneq.pedoe EulerIneq.pedoe_eq_iff EulerIneq.ptolemy_inequality EulerIneq.kooi_of_quartic EulerIneq.kooi EulerIneq.kooi_le_gerretsen EulerIneq.leibniz_relation EulerIneq.leibniz_min EulerIneq.leibniz_min_eq_iff EulerIneq.amgm_three EulerIneq.isoperimetric EulerIneq.isoperimetric_eq_iff EulerIneq.gerretsen_cross_check"
SOURCES="EulerIneq/*.lean EulerIneq.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
