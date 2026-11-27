#!/bin/sh
# Usage: sh ci/check.sh [--quick | --build]
# The Lean half of the admission gate of gororoba-math. Without an option it
# is the full gate. With --quick it runs the checks that need no Lean
# toolchain and no build (step 1 and steps 8 and 9, in the order the script
# reaches them) and stops. With --build it runs every step but the kernel
# replay of step 7: Lake compares content hashes, so over a restored build
# tree the build of step 2 compiles the changed modules and the modules that
# import them. The quick workflow runs both modes on every pull request.
# From any directory of the checkout:
#   1. every tracked shell script passes the lint at severity error, every
#      tracked Python file passes ruff check and ruff format --check under
#      ruff.toml, every tracked workflow passes actionlint, and each line of
#      a tracked shell script that runs rm with a recursive option redirects
#      standard input from /dev/null; ci/check_signal_traps.sh requires
#      each trap command of a tracked shell script to read trap ACTION EXIT,
#      trap 'exit 130' INT or trap 'exit 143' TERM on one line, and
#      interrupts this script and four comparison scripts under stub tools
#      to confirm that each stops with the signal's status;
#   2. every tracked module under lean/GororobaMath/, taken from git's file
#      list, and the audit command build with warnings as errors;
#   3. the axiom audit accepts a generated file that imports the root
#      module and each of those modules, so the audit covers a module
#      whatever lean/GororobaMath.lean imports;
#   4. lean/GororobaMath.lean imports each of those modules, read from
#      Lean's own listing of the file's imports (lean --deps), and the same
#      check reports a module whose import sits inside a block comment;
#   5. the axiom audit rejects its known-bad inputs: lean/AuditFixture.lean,
#      naming sorryAx, the declared axiom, the native_decide axiom and
#      the unused private theorem closed by sorry, and a root that matches
#      no module (lean/audit/UnknownRoot.lean);
#   6. lean/lakefile.toml sets no srcDir, and no library source imports an
#      object of another library of this package, so the replay of step 7
#      assumes only the package's dependencies (Mathlib and what it
#      requires); each rule rejects a known-bad input;
#   7. ci/replay_modules.lean, which runs the replay function of
#      leanchecker: it reads the compiled objects in another process
#      and type-checks their theorems and definitions in the kernel again
#      (it skips unsafe and partial declarations; the kernel rejects a
#      theorem that uses one, measured under Lean 4.35.0), accepts each
#      tracked module, eight to a process, and rejects
#      lean/ReplayFixture.lean, whose declaration of type False was added
#      with the kernel switched off and which the build and the axiom
#      audit (lean/audit/ReplayFixture.lean) both accept. The root module
#      is left out of the replay and holds only `module` and its imports
#      of the library, which this step checks.
#   8. ci/check_headline_results.py calibrates itself on known-bad copies of
#      its inputs and then requires every row of ci/headline-results.tsv to
#      name a theorem of the library, the rows to equal the theorems the
#      "Lean library" table of README.md names, and each partner to be owed
#      with its tracking issue or to name a theorem of a project-listed Rocq
#      source.
#   9. ci/check_claims_ledger.py calibrates itself on known-bad copies of its
#      inputs and then requires every row of ci/claims/ledger.tsv to hold the
#      columns, enumerations and status rules of ci/claims/README.md and every
#      proof entry to name a declaration of the library or of a project-listed
#      Rocq source, and the ledger sources to equal those of
#      ci/claims/expected-sources.tsv.
# Needs git, shellcheck, ruff, actionlint, lake (elan, with the toolchain
# of lean/lean-toolchain; not needed with --quick) and Python 3 (PYTHON,
# default python3) on PATH. Exit status: 0 every check passed, 1 a check
# failed, 2 a tool is missing or the arguments are not understood. Writes
# only under a temporary directory it removes.
set -eu

quick=
build_only=
case $# in
0) ;;
1)
  case $1 in
  --quick) quick=1 ;;
  --build) build_only=1 ;;
  *)
    echo "usage: check.sh [--quick | --build]" >&2
    exit 2
    ;;
  esac
  ;;
*)
  echo "usage: check.sh [--quick | --build]" >&2
  exit 2
  ;;
esac

PYTHON=${PYTHON:-python3}
export PYTHON
build_tool=lake
[ -z "$quick" ] || build_tool=git
for tool in git "$build_tool" shellcheck ruff actionlint "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check: $tool is not on PATH (README.md, Toolchain)" >&2
    exit 2
  }
done

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
# A signal ends the script through the EXIT cleanup: a trap action that
# returns lets the shell run on with the work directory gone. The traps are
# set before the directory exists, and the cleanup keeps the status the
# script ended with when the removal itself fails.
work=
trap 'status=$?; [ -z "$work" ] || rm -r "$work" </dev/null || :; exit "$status"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
work=$(mktemp -d)

cd "$root"
git ls-files -- '*.sh' >"$work/scripts.txt"
[ -s "$work/scripts.txt" ] || {
  echo "check: git tracks no shell script; this script is one, so commit before the gate" >&2
  exit 1
}
while IFS= read -r script; do
  shellcheck -S error "$script"
done <"$work/scripts.txt"
echo "check: shellcheck passed on $(wc -l <"$work/scripts.txt") script(s)"

# A line of a tracked shell script that runs rm with a recursive option also
# holds the redirection </dev/null: under a terminal rm asks before it removes
# a write-protected file (a git object, mode 444), and a gate started from a
# terminal then waits for an answer. The rule is lexical and reads one line at
# a time: it knows the options -r, -R, a bundle that holds either, and
# --recursive, after any other option words, and it reports a removal whose
# redirection sits on another line. A removal built from a variable is
# outside it. The samples below
# calibrate both patterns; printf joins each sample so that the scan, which
# reads this script too, meets no sample as a line.
removal='(^|[^[:alnum:]_-])rm[[:space:]]+(-[^[:space:]]*[[:space:]]+)*(-[[:alnum:]]*[rR][[:alnum:]]*|--recursive)([[:space:]]|$)'
redirected='</dev/null'
reads_terminal() {
  # Prints the lines of standard input that remove recursively without the
  # redirection. Status 2 reports a read error of the first grep, the one
  # command here that reads a file; the later ones read its output.
  matches=$(grep -n -E "$removal") || { [ $? -eq 1 ] || return 2; }
  [ -z "$matches" ] || printf '%s\n' "$matches" |
    { grep -v -E '^[0-9]+:[[:space:]]*#' || [ $? -eq 1 ]; } |
    { grep -v -F "$redirected" || [ $? -eq 1 ]; }
}
for option in -r -R -fr -rf --recursive "-f -r" "-v --recursive"; do
  [ -n "$(printf 'rm %s scratch\n' "$option" | reads_terminal)" ] &&
    [ -n "$(printf 'rm %s scratch # <note>\n' "$option" | reads_terminal)" ] &&
    [ -z "$(printf 'rm %s scratch </dev/null\n' "$option" | reads_terminal)" ] || {
    echo "check: the recursive-removal rule failed its calibration on rm $option" >&2
    exit 1
  }
done
[ -z "$(printf 'rm scratch\nrm -f scratch\nperform -r scratch\n# rm %s scratch\n' -r | reads_terminal)" ] || {
  echo "check: the recursive-removal rule reported a line that removes nothing recursively" >&2
  exit 1
}
if reads_terminal <"$work" >/dev/null 2>&1; then
  echo "check: the recursive-removal rule accepted an input it cannot read (a directory)" >&2
  exit 1
fi
: >"$work/terminal-removals.txt"
while IFS= read -r script; do
  found=$(reads_terminal <"$script") || {
    echo "check: the recursive-removal rule could not read $script" >&2
    exit 1
  }
  [ -z "$found" ] || printf '%s\n' "$found" | sed "s|^|$script:|" >>"$work/terminal-removals.txt"
done <"$work/scripts.txt"
[ ! -s "$work/terminal-removals.txt" ] || {
  cat "$work/terminal-removals.txt" >&2
  echo "check: a recursive removal can read the terminal; put </dev/null on its line" >&2
  exit 1
}
echo "check: each recursive removal of $(wc -l <"$work/scripts.txt") script(s) reads /dev/null"
sh ci/check_signal_traps.sh

git ls-files -- '*.py' >"$work/python.txt"
if [ -s "$work/python.txt" ]; then
  while IFS= read -r source; do
    ruff check --quiet "$source"
    ruff format --quiet --check "$source"
  done <"$work/python.txt"
  echo "check: ruff passed on $(wc -l <"$work/python.txt") Python file(s)"
fi

"$PYTHON" -I ci/check_headline_results.py
"$PYTHON" -I ci/check_claims_ledger.py

git ls-files -- '.github/workflows/*.yml' >"$work/workflows.txt"
if [ -s "$work/workflows.txt" ]; then
  while IFS= read -r workflow; do
    actionlint "$workflow"
  done <"$work/workflows.txt"
  echo "check: actionlint passed on $(wc -l <"$work/workflows.txt") workflow(s)"
fi

[ -z "$quick" ] || {
  echo "check: the quick checks passed; the build, the audit and the replay did not run"
  exit 0
}

git ls-files -- ':(glob)lean/GororobaMath/**/*.lean' |
  sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g' | LC_ALL=C sort >"$work/modules.txt"
[ -s "$work/modules.txt" ] || {
  echo "check: git tracks no module under lean/GororobaMath" >&2
  exit 1
}

cd "$root/lean"
# shellcheck disable=SC2046 # one build target per module name
lake build --wfail $(cat "$work/modules.txt") GororobaMath AxiomAudit
echo "check: $(wc -l <"$work/modules.txt") tracked module(s) built with no warning"

{
  # The root module is audited with the modules below it, so a declaration
  # written in lean/GororobaMath.lean itself is covered.
  echo "import GororobaMath"
  sed 's/^/import /' "$work/modules.txt"
  echo "import AxiomAudit"
  echo "#audit_axioms GororobaMath"
} >"$work/AllModules.lean"
lake env lean "$work/AllModules.lean" >"$work/audit.out" 2>&1 || {
  cat "$work/audit.out" >&2
  exit 1
}
cat "$work/audit.out"
# The audit's own summary line is required, so a file that only exits 0
# (a command of the same name defined in the library, say) does not pass.
grep -q -E 'axiom audit: GororobaMath: [1-9][0-9]* declarations, 0 outside the allow list$' "$work/audit.out" || {
  echo "check: the axiom audit printed no summary line for GororobaMath" >&2
  exit 1
}

# Prints each module of the sorted list file $2 that the Lean file $1 does
# not import, and fails when it printed one. Lean reads the import header,
# so a commented import counts as absent.
missing_imports() {
  lake env lean --deps "$1" |
    sed -n -e 's|^.*/lib/lean/\(GororobaMath/.*\)\.olean$|\1|p' | sed 's|/|.|g' | LC_ALL=C sort -u >"$work/imports.txt"
  LC_ALL=C comm -23 "$2" "$work/imports.txt" >"$work/missing.txt"
  [ ! -s "$work/missing.txt" ] || {
    cat "$work/missing.txt"
    return 1
  }
}
missing_imports GororobaMath.lean "$work/modules.txt" >"$work/missing-root.txt" || {
  echo "check: lean/GororobaMath.lean does not import:" >&2
  cat "$work/missing-root.txt" >&2
  exit 1
}
first=$(sed -n 1p "$work/modules.txt")
{
  echo "/-"
  echo "import $first"
  echo "-/"
  sed -e 1d -e 's/^/import /' "$work/modules.txt"
} >"$work/CommentedImport.lean"
if missing_imports "$work/CommentedImport.lean" "$work/modules.txt" >"$work/missing-commented.txt"; then
  echo "check: the import check accepted an import inside a block comment" >&2
  exit 1
fi
[ "$(cat "$work/missing-commented.txt")" = "$first" ] || {
  cat "$work/missing-commented.txt" >&2
  echo "check: the import check misreported its commented import of $first" >&2
  exit 1
}
echo "check: root file imports all tracked modules; a commented import is reported"

lake build AuditFixture >"$work/fixture-build.log" 2>&1 || {
  cat "$work/fixture-build.log" >&2
  echo "check: the audit fixture failed to build" >&2
  exit 1
}
if lake env lean audit/Fixture.lean >"$work/fixture.out" 2>&1; then
  cat "$work/fixture.out" >&2
  echo "check: the axiom audit accepted its known-bad fixture" >&2
  exit 1
fi
for axiom in sorryAx AuditFixture.declaredAxiom native_decide AuditFixture.privateSorry; do
  grep -q -F "$axiom" "$work/fixture.out" || {
    cat "$work/fixture.out" >&2
    echo "check: the axiom audit did not name $axiom in its fixture" >&2
    exit 1
  }
done
if lake env lean audit/UnknownRoot.lean >"$work/unknown.out" 2>&1; then
  cat "$work/unknown.out" >&2
  echo "check: the axiom audit accepted a root that matches no module" >&2
  exit 1
fi
echo "check: axiom audit rejected the fixture and the unknown root"

# The replay below covers the modules of lean/GororobaMath/ and assumes what
# they import. Two checks keep that assumption to the package's
# dependencies (Mathlib and what it requires): Lake builds the
# library from the tracked files (no srcDir moves its sources), and no
# library module imports an object of another library of this package
# (AuditFixture, ReplayFixture, AxiomAudit or a later one), which the replay
# would not reach.
sets_srcdir() {
  grep -q -E '^[[:space:]]*srcDir' "$1"
}
printf 'name = "x"\n\n[[lean_lib]]\nname = "X"\nsrcDir = "shadow"\n' >"$work/srcdir.toml"
sets_srcdir "$work/srcdir.toml" || {
  echo "check: the srcDir rule accepted a lakefile that sets srcDir" >&2
  exit 1
}
if sets_srcdir lakefile.toml; then
  echo "check: lean/lakefile.toml sets srcDir; the gate reads modules from lean/GororobaMath/" >&2
  exit 1
fi
# Prints each object of this package outside GororobaMath that the Lean
# file $1 imports: an object under a build directory that is not a
# dependency's (packages/).
foreign_imports() {
  lake env lean --deps "$1" |
    sed -n -e '/\/packages\//d' -e 's|^.*/build/lib/lean/\(.*\)\.olean$|\1|p' |
    grep -v -E '^GororobaMath(/|$)' || true
}
git ls-files -- GororobaMath.lean ':(glob)GororobaMath/**/*.lean' >"$work/sources.txt"
while IFS= read -r source; do
  foreign=$(foreign_imports "$source")
  [ -z "$foreign" ] || {
    echo "check: $source imports an object the replay does not reach: $foreign" >&2
    exit 1
  }
done <"$work/sources.txt"
[ "$(foreign_imports audit/Fixture.lean | LC_ALL=C sort | tr '\n' ' ')" = "AuditFixture AxiomAudit " ] || {
  echo "check: the import check did not report the two foreign imports of lean/audit/Fixture.lean" >&2
  exit 1
}
echo "check: $(wc -l <"$work/sources.txt") library source(s) import only the library and its dependencies"

# ci/replay_modules.lean replays each module it is given from its imports with
# the kernel, by the function `replayFromImports` that leanchecker runs (copied
# verbatim from Lean v4.35.0), and assumes their imports, so every library
# module is named; Mathlib's objects are assumed, as its prebuilt cache already
# is. leanchecker resolves each argument as a module-name prefix by listing
# every object file of the search path, and its call per module paid that walk
# plus a `lake env` start each time (measured: 4.6 s of 8.2 s per module,
# about 14 min for the library); the driver names the module, so a name that
# prefixes others replays only itself. Eight modules share one process and
# at most four processes run at once; each holds the imports of one module,
# whose mapped objects are shared pages.
# Prints each line of the Lean file $1 that is neither blank, `module`, nor
# an import of a library module; succeeds when it printed one.
root_extra() {
  grep -v -x -E '(module|(public )?import GororobaMath(\.[A-Za-z0-9_]+)+)?' "$1"
}
printf 'module\n\npublic import GororobaMath.A\ntheorem t : True := trivial\n' >"$work/Root.lean"
[ "$(root_extra "$work/Root.lean" || true)" = "theorem t : True := trivial" ] || {
  echo "check: the root-file rule did not report a declaration in its known-bad root" >&2
  exit 1
}
if root_extra GororobaMath.lean >"$work/root-extra.txt"; then
  cat "$work/root-extra.txt" >&2
  echo "check: lean/GororobaMath.lean holds a line other than module and its imports of the library; the replay leaves the root module out" >&2
  exit 1
fi
[ -z "$build_only" ] || {
  echo "check: the build, the audit and the import rules passed; the kernel replay did not run"
  exit 0
}

replay_jobs=$(nproc 2>/dev/null || echo 1)
[ "$replay_jobs" -le 4 ] || replay_jobs=4
xargs -n 8 -P "$replay_jobs" lake env lean --run "$root/ci/replay_modules.lean" \
  <"$work/modules.txt" >"$work/replay.out" 2>&1 || {
  cat "$work/replay.out" >&2
  echo "check: the kernel replay rejected a tracked module" >&2
  exit 1
}
# The modules that printed PASS equal the tracked modules as sets: a count
# alone accepts a duplicated line that stands for a dropped module.
# Prints the names on which the sorted PASS list $1 and the sorted module
# list $2 differ; succeeds when they are equal.
pass_set_differs() {
  cmp -s "$1" "$2" && return 1
  diff "$1" "$2" | sed -n 's/^[<>] //p'
  return 0
}
LC_ALL=C sort "$work/modules.txt" >"$work/modules.sorted"
sed -n 's/^PASS //p' "$work/replay.out" | LC_ALL=C sort >"$work/passed.sorted"
if pass_set_differs "$work/passed.sorted" "$work/modules.sorted" >"$work/pass-diff.txt"; then
  cat "$work/replay.out" >&2
  echo "check: the kernel replay did not accept every tracked module; differing names:" >&2
  cat "$work/pass-diff.txt" >&2
  exit 1
fi
# Known-bad inputs: a PASS list with one module dropped and one duplicated
# (the same line count as the module list) must differ.
{
  sed 1d "$work/modules.sorted"
  sed -n 2p "$work/modules.sorted"
} | LC_ALL=C sort >"$work/passed.mutant"
if [ "$(wc -l <"$work/passed.mutant")" -ne "$(wc -l <"$work/modules.sorted")" ] ||
  ! pass_set_differs "$work/passed.mutant" "$work/modules.sorted" >/dev/null; then
  echo "check: the PASS set comparison accepted a list with a dropped and a duplicated module" >&2
  exit 1
fi
echo "check: the modules that passed the replay equal the $(wc -l <"$work/modules.sorted") tracked modules by name, and a list with a dropped and a duplicated module is rejected"
# replayFromImports of the driver equals that of the installed toolchain's
# leanchecker source, byte for byte: a toolchain bump that changes the
# function fails here until the driver copies it. The source is part of the
# release archive elan installs, hosted runners included; a missing file
# fails the gate.
replay_body() {
  awk '/^unsafe def replayFromImports/ { on = 1 } on && /^$/ { exit } on' "$1"
}
sysroot=$(lake env lean --print-prefix)
upstream="$sysroot/src/lean/LeanChecker.lean"
[ -f "$upstream" ] || {
  echo "check: $upstream is absent: the toolchain $(cat lean-toolchain) lacks the source of leanchecker the driver is compared with" >&2
  exit 1
}
replay_body "$upstream" >"$work/replay-upstream.txt"
replay_body "$root/ci/replay_modules.lean" >"$work/replay-driver.txt"
[ -s "$work/replay-upstream.txt" ] && [ -s "$work/replay-driver.txt" ] || {
  echo "check: replayFromImports was not found in $upstream or in ci/replay_modules.lean" >&2
  exit 1
}
if ! cmp -s "$work/replay-upstream.txt" "$work/replay-driver.txt"; then
  diff "$work/replay-upstream.txt" "$work/replay-driver.txt" >&2 || :
  echo "check: replayFromImports of ci/replay_modules.lean differs from $upstream" >&2
  exit 1
fi
# Known-bad input: the driver's body with one character changed must differ.
sed '3s/mFile/nFile/' "$work/replay-driver.txt" >"$work/replay-driver.mutant"
if cmp -s "$work/replay-upstream.txt" "$work/replay-driver.mutant" ||
  cmp -s "$work/replay-driver.txt" "$work/replay-driver.mutant"; then
  echo "check: the replayFromImports comparison accepted a copy with one character changed" >&2
  exit 1
fi
echo "check: replayFromImports of ci/replay_modules.lean equals $upstream, and a copy with one character changed is rejected"
lake build --wfail ReplayFixture >"$work/replay-fixture-build.log" 2>&1 || {
  cat "$work/replay-fixture-build.log" >&2
  echo "check: the replay fixture failed to build" >&2
  exit 1
}
# The fixture shows the gap only while the axiom audit accepts it.
lake env lean audit/ReplayFixture.lean >"$work/replay-fixture-audit.out" 2>&1 || {
  cat "$work/replay-fixture-audit.out" >&2
  echo "check: the axiom audit now rejects the replay fixture; the fixture no longer calibrates the replay" >&2
  exit 1
}
if lake env lean --run "$root/ci/replay_modules.lean" ReplayFixture >"$work/replay-fixture.out" 2>&1; then
  cat "$work/replay-fixture.out" >&2
  echo "check: the kernel replay accepted its known-bad fixture" >&2
  exit 1
fi
grep -q -F "while replaying declaration 'ReplayFixture.bogus'" "$work/replay-fixture.out" || {
  cat "$work/replay-fixture.out" >&2
  echo "check: the kernel replay failed on its fixture without naming ReplayFixture.bogus" >&2
  exit 1
}
# The same fixture inside a batch after a good module: the exit stays
# nonzero, the good module still passes and the diagnostic names the fixture.
good=$(sed -n 1p "$work/modules.txt")
if lake env lean --run "$root/ci/replay_modules.lean" "$good" ReplayFixture >"$work/replay-batch.out" 2>&1; then
  cat "$work/replay-batch.out" >&2
  echo "check: the kernel replay accepted a batch that holds its known-bad fixture" >&2
  exit 1
fi
grep -q -x -F "PASS $good" "$work/replay-batch.out" &&
  grep -q -F "while replaying declaration 'ReplayFixture.bogus'" "$work/replay-batch.out" || {
  cat "$work/replay-batch.out" >&2
  echo "check: the batch with the fixture did not report PASS $good and the fixture diagnostic" >&2
  exit 1
}
echo "check: a batch of $good and the fixture exits nonzero, passes $good and names ReplayFixture.bogus"
echo "check: kernel replay accepted $(wc -l <"$work/modules.txt") tracked module(s) and rejected the fixture"
echo "check: passed"
