# shellcheck shell=sh
# Inventory checks of the Rocq trees that ci/check_rocq.sh and
# ci/check_rocq_changed.sh share. Sourced, not run: it sets no shell option and
# defines the two lists of sources outside the project files and the functions
# that check a tree against them. The functions read $work, a scratch
# directory, and print to standard error.

# Sources outside the four project-listed directories. A make target of
# rocq/open compiles each source of the first list (check-schur-geometry the
# four Schur sources, extract ExtractQuaternion.v, check-plugins the two
# plugin fixtures), except the nullity certificate: check-schur-geometry
# scans it for admissions only, so the gate compiles it under that
# recipe's flags. Nothing the gate runs compiles a source of the second
# list: ExtractFP24Admit.v and ExtractR2VBDP4.v belong to the CertiRocq
# recipes extract-c and extract-r2vb-c, which need a rocq-certirocq switch,
# and no recipe names RustExtractSpike.v.
target_compiled='rocq/open/checkpoints/schur-geometry/CDTowerOperatorCorrespondence.v
rocq/open/checkpoints/schur-geometry/CDUnconditionalDoublingNullity.v
rocq/open/checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v
rocq/open/checkpoints/schur-geometry/SchurAccelerationObstruction.v
rocq/open/extraction/ExtractQuaternion.v
rocq/open/tests/MathCompMatrixCompatibility.v
rocq/open/tests/PluginCompatibility.v
rocq/open/tests/SchurAccelerationBoundaries.v'
held_uncompiled='rocq/open/extraction/ExtractFP24Admit.v
rocq/open/extraction/ExtractR2VBDP4.v
rocq/open/extraction/RustExtractSpike.v'

# Fails unless the sources of the list $1 that lie outside the four
# project-listed directories are exactly the two lists above, printing the
# difference.
outside_sources_match() {
  grep -v -E '^rocq/(open/(theories|verified)|quantum|delegation)/' "$1" | LC_ALL=C sort >"$work/outside.txt"
  printf '%s\n%s\n' "$target_compiled" "$held_uncompiled" | LC_ALL=C sort >"$work/outside-named.txt"
  diff "$work/outside-named.txt" "$work/outside.txt"
}

# Fails when a line of the newline-separated source list $2 is absent, as a
# whole line, from the project file $1, printing each absent one. An empty
# project file lists nothing, so every source is absent from it.
unlisted_sources() {
  status=0
  grep -F -x -v -f "$1" "$2" || status=$?
  case $status in
    0) return 1 ;;
    1) return 0 ;;
    *) return 2 ;;
  esac
}

# Fails unless the project file $1 carries the option lines of the warning
# set: -arg -w, then -arg all,+default.
warning_options_set() {
  awk 'previous == "-arg -w" && $0 == "-arg all,+default" { found = 1 } { previous = $0 } END { exit found ? 0 : 1 }' "$1"
}

# Succeeds when the source $1 holds as many Theorem lines as entries of
# its list stated, and at least one. The generator spells every other
# result of a rendered source Lemma.
stated_covers() {
  theorems=$(grep -c '^Theorem ' "$1" || true)
  entries=$(grep -c '^  *\[\{0,1\}exist Stated ' "$1" || true)
  [ "$theorems" -gt 0 ] && [ "$theorems" -eq "$entries" ]
}

# Checks the rendered sources of the directory $1 (rocq/delegation): three of
# them hold a list stated, each pairs every theorem with an entry of it, and
# the check rejects a copy with one more theorem. Prints the failure and
# returns 1.
check_delegation_stated() {
  rendered="$work/delegation-rendered.txt"
  (cd "$1" && grep -l '^Definition stated ' ./*.v) >"$rendered" || true
  [ "$(awk 'END { print NR }' "$rendered")" -eq 3 ] || {
    echo "rocq/delegation holds other than three sources with a list stated" >&2
    return 1
  }
  while IFS= read -r source; do
    stated_covers "$1/$source" || {
      echo "$source states a theorem that its list stated omits, or the reverse" >&2
      return 1
    }
    {
      cat "$1/$source"
      echo 'Theorem unlisted_calibration : True.'
    } >"$work/stated-calibration.v"
    if stated_covers "$work/stated-calibration.v"; then
      echo "the stated-list check accepted a source with an unlisted theorem" >&2
      return 1
    fi
  done <"$rendered"
}
