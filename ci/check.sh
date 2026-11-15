#!/bin/sh
# Usage: sh ci/check.sh
# The Lean half of the admission gate of gororoba-math. From any directory of
# the checkout:
#   1. every tracked shell script passes the lint at severity error, every
#      tracked Python file passes ruff check and ruff format --check under
#      ruff.toml, every tracked workflow passes actionlint, and each line of
#      a tracked shell script that runs rm with a recursive option redirects
#      standard input from /dev/null;
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
#   7. leanchecker, which reads the compiled objects in a second process
#      and type-checks their theorems and definitions in the kernel again
#      (it skips unsafe and partial declarations; the kernel rejects a
#      theorem that uses one, measured under Lean 4.35.0), accepts each tracked module, one call per module, and rejects
#      lean/ReplayFixture.lean, whose declaration of type False was added
#      with the kernel switched off and which the build and the axiom
#      audit (lean/audit/ReplayFixture.lean) both accept. The root module
#      is left out of the replay and holds only `module` and its imports
#      of the library, which this step checks.
# Needs git, shellcheck, ruff, actionlint and lake (elan, with the toolchain
# of lean/lean-toolchain) on PATH. Exit status: 0 every check passed, 1 a check failed,
# 2 a tool is missing. Writes only under a temporary directory it removes.
set -eu

for tool in git lake shellcheck ruff actionlint; do
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

git ls-files -- '*.py' >"$work/python.txt"
if [ -s "$work/python.txt" ]; then
  while IFS= read -r source; do
    ruff check --quiet "$source"
    ruff format --quiet --check "$source"
  done <"$work/python.txt"
  echo "check: ruff passed on $(wc -l <"$work/python.txt") Python file(s)"
fi

git ls-files -- '.github/workflows/*.yml' >"$work/workflows.txt"
if [ -s "$work/workflows.txt" ]; then
  while IFS= read -r workflow; do
    actionlint "$workflow"
  done <"$work/workflows.txt"
  echo "check: actionlint passed on $(wc -l <"$work/workflows.txt") workflow(s)"
fi

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

# leanchecker replays the modules it is given and assumes their imports, so
# every library module is named; Mathlib's objects are assumed, as its
# prebuilt cache already is. One module per call keeps the peak at 6.9 GB
# (measured, Lean 4.35.0 with Mathlib v4.35.0, each of the seven modules
# under a 14 GB limit). The root module is left out: its replay needs
# 27.5 GB and ends with SIGTERM under a 20 GB limit (measured; cause not
# isolated), and the check below keeps it free of declarations.
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
for module in $(cat "$work/modules.txt"); do
  lake env leanchecker "$module" >"$work/replay.out" 2>&1 || {
    cat "$work/replay.out" >&2
    echo "check: the kernel replay rejected $module" >&2
    exit 1
  }
done
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
if lake env leanchecker ReplayFixture >"$work/replay-fixture.out" 2>&1; then
  cat "$work/replay-fixture.out" >&2
  echo "check: the kernel replay accepted its known-bad fixture" >&2
  exit 1
fi
grep -q -F "while replaying declaration 'ReplayFixture.bogus'" "$work/replay-fixture.out" || {
  cat "$work/replay-fixture.out" >&2
  echo "check: the kernel replay failed on its fixture without naming ReplayFixture.bogus" >&2
  exit 1
}
echo "check: kernel replay accepted $(wc -l <"$work/modules.txt") tracked module(s) and rejected the fixture"
echo "check: passed"
