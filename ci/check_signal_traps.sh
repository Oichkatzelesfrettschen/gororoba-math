#!/bin/sh
# Usage: sh ci/check_signal_traps.sh
# Checks that an interrupted gate or comparison script stops. A trap action
# bound to INT or TERM that returns lets a POSIX shell run on with the next
# command, so each tracked shell script binds INT to exit 130 and TERM to
# exit 143 alone, and leaves its cleanup to the EXIT trap.
#   1. A lexical rule reads every tracked shell script (each *.sh file and
#      each tracked file whose first line is a shell #! line) and reports
#      each non-comment line that holds the word trap outside the one-line
#      forms trap ACTION EXIT, trap 'exit 130' INT and trap 'exit 143' TERM;
#      samples calibrate it both ways.
#   2. Each subject script below runs from a scratch repository with stub
#      tools first on PATH. The first call of its trigger tool, the first
#      stubbed tool it reaches after its traps are set, waits until this
#      script has sent the signal;
#      every stub call after the signal records a later stage. The run
#      passes when the script exits with 130 after INT and 143 after TERM,
#      reaches no later stage, and leaves its temporary directory empty. A
#      mutant of each subject whose EXIT trap also names INT and TERM, the
#      form issue 66 reports, must fail the same test: the four comparison
#      scripts run on into a later stage, and check.sh, whose EXIT action
#      ends in exit "$status", exits 0.
# Needs git, an env that takes --default-signal (GNU coreutils 8.31 or later;
# uutils coreutils 0.10.0 measured), since an asynchronous command of a
# non-interactive shell starts with SIGINT ignored and a shell cannot trap a
# signal ignored at its start, and a sleep
# that takes fractions of a second. Exit status: 0 every subject stops and
# every mutant is caught, 1 a check failed, 2 a tool is missing. Writes only
# under a temporary directory it removes.
set -eu

for tool in git env sleep; do
  command -v "$tool" >/dev/null || {
    echo "check_signal_traps: $tool is not on PATH" >&2
    exit 2
  }
done
env --default-signal=INT true 2>/dev/null || {
  echo "check_signal_traps: env lacks --default-signal (GNU coreutils 8.31 or later)" >&2
  exit 2
}

root=$(git -C "$(dirname -- "$0")" rev-parse --show-toplevel)
scratch=
trap 'status=$?; [ -z "$scratch" ] || rm -r "$scratch" </dev/null || :; exit "$status"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
scratch=$(mktemp -d)

# Prints the lines of standard input, other than comment lines, that hold the
# word trap anywhere outside three forms, each the whole line: trap 'exit 130'
# INT, trap 'exit 143' TERM, and trap ACTION EXIT with ACTION a function name
# or a single-quoted string. The rule reads words, not command positions, so
# it fails closed on every spelling it cannot read (a case arm, an assignment
# or command prefix, trap --, double quotes, signal numbers, SIG names,
# several conditions, a trap spread over lines) and on prose that names the
# word outside a comment line; a command name built by quoting or expansion
# (t\rap, eval) is outside it. Its own patterns spell the word t[r]ap.
nonconforming_traps() {
  { grep -n -E '(^|[^[:alnum:]_])t[r]ap([^[:alnum:]_]|$)' || [ $? -eq 1 ]; } |
    { grep -v -E '^[0-9]+:[[:space:]]*#' || [ $? -eq 1 ]; } |
    { grep -v -E "^[0-9]+:[[:space:]]*t[r]ap ('exit 130' INT|'exit 143' TERM)\$" || [ $? -eq 1 ]; } |
    { grep -v -E "^[0-9]+:[[:space:]]*t[r]ap ('[^']*'|[[:alpha:]_][[:alnum:]_]*) EXIT\$" || [ $? -eq 1 ]; }
}
# The samples spell the word TRAP, and sed restores it, so the scan of this
# script below meets no sample.
word=$(printf 't%sap' r)
rejected="TRAP 'unlink w' EXIT INT TERM
TRAP 'unlink w' INT
TRAP 'exit 130' INT TERM
TRAP cleanup TERM
  TRAP 'exit 0' INT
TRAP 'exit 130' 2
TRAP 'exit 143' 15
TRAP 'exit 130' SIGINT
TRAP -- 'exit 130' INT
TRAP \"exit 130\" INT
TRAP '
TRAP 'rm w' 0
f() { TRAP 'rm w' INT; }
cd w && TRAP 'rm w' INT
(TRAP 'rm w' TERM)
if w; then TRAP 'rm w' INT; fi
for w in w; do TRAP 'rm w' INT; done
if w; then :; else TRAP 'rm w' INT; fi
! TRAP 'rm w' INT
case w in w) TRAP cleanup INT ;; esac
w=w TRAP cleanup INT
command TRAP cleanup INT
echo do not TRAP INT"
printf '%s\n' "$rejected" | sed "s/TRAP/$word/" | while IFS= read -r sample; do
  [ -n "$(printf '%s\n' "$sample" | nonconforming_traps)" ] || {
    echo "check_signal_traps: the lexical rule accepted: $sample" >&2
    exit 1
  }
done
accepted="TRAP 'exit 130' INT
TRAP 'exit 143' TERM
  TRAP 'exit 130' INT
TRAP cleanup EXIT
TRAP 'unlink \"\$work\"' EXIT
# TRAP 'rm w' INT
echo traps INT"
[ -z "$(printf '%s\n' "$accepted" | sed "s/TRAP/$word/" | nonconforming_traps)" ] || {
  echo "check_signal_traps: the lexical rule reported a conforming handler" >&2
  exit 1
}
cd "$root"
# The tracked shell scripts: each file named *.sh, and each other tracked file
# whose first line is a shell #! line.
git ls-files >"$scratch/tracked.txt"
: >"$scratch/scripts.txt"
while IFS= read -r path; do
  case $path in
    *.sh) printf '%s\n' "$path" >>"$scratch/scripts.txt" ;;
    *)
      if [ -f "$path" ] && head -n 1 "$path" | grep -q -E '^#!.*[/ ](sh|bash|dash|ksh|zsh)([[:space:]]|$)'; then
        printf '%s\n' "$path" >>"$scratch/scripts.txt"
      fi
      ;;
  esac
done <"$scratch/tracked.txt"
: >"$scratch/nonconforming.txt"
while IFS= read -r script; do
  found=$(nonconforming_traps <"$script")
  [ -z "$found" ] || printf '%s\n' "$found" | sed "s|^|$script:|" >>"$scratch/nonconforming.txt"
done <"$scratch/scripts.txt"
[ ! -s "$scratch/nonconforming.txt" ] || {
  cat "$scratch/nonconforming.txt" >&2
  echo "check_signal_traps: write each signal handler on one line in a form ci/check_signal_traps.sh names" >&2
  exit 1
}
echo "check_signal_traps: every signal handler of $(wc -l <"$scratch/scripts.txt") script(s) has a conforming form"

# Each subject with its trigger: the first stubbed tool it reaches after its
# traps are set.
subjects='check.sh:shellcheck
compare_dot.sh:python3
compare_estimator.sh:python3
compare_estimator_rocq.sh:python3
compare_kernel_map_bins.sh:python3'

mkdir "$scratch/bin"
cat >"$scratch/bin/stub" <<'STUB'
#!/bin/sh
name=${0##*/}
state=$SIGNAL_TRAPS_STATE
if [ -e "$state/signaled" ]; then
  echo "$name" >>"$state/later"
  exit 1
fi
if [ "$name" = opam ] && [ "${1-}" = switch ]; then
  echo rocq-9.3
  exit 0
fi
if [ "$name" = "$SIGNAL_TRAPS_TRIGGER" ]; then
  : >"$state/started"
  count=0
  while [ ! -e "$state/signaled" ]; do
    count=$((count + 1))
    [ "$count" -le 300 ] || exit 3
    sleep 0.1
  done
fi
exit 0
STUB
chmod +x "$scratch/bin/stub"
for tool in lake opam shellcheck ruff actionlint python3; do
  ln -s stub "$scratch/bin/$tool"
done

# A checkout stand-in for the scripts that read gororoba-quantum.
mkdir -p "$scratch/quantum/gororoba_quantum"
: >"$scratch/quantum/gororoba_quantum/pathion_kernel_map.py"
git -C "$scratch/quantum" init -q
git -C "$scratch/quantum" add gororoba_quantum
git -C "$scratch/quantum" -c user.name=check -c user.email=check@invalid commit -q -m quantum

# Two scratch repositories: the tracked scripts, and their mutants.
for kind in good mutant; do
  mkdir -p "$scratch/$kind/ci" "$scratch/$kind/lean"
  printf '%s\n' "$subjects" | while IFS=: read -r script trigger; do
    if [ "$kind" = good ]; then
      cp "ci/$script" "$scratch/$kind/ci/$script"
    else
      sed -e "/^t[r]ap 'exit 130' INT\$/d" -e "/^t[r]ap 'exit 143' TERM\$/d" \
        -e "s/^\(t[r]ap '.*'\) EXIT\$/\1 EXIT INT TERM/" "ci/$script" >"$scratch/$kind/ci/$script"
      ! cmp -s "ci/$script" "$scratch/$kind/ci/$script" || {
        echo "check_signal_traps: the mutation left ci/$script unchanged" >&2
        exit 1
      }
    fi
  done
  git -C "$scratch/$kind" init -q
  git -C "$scratch/$kind" add ci
  git -C "$scratch/$kind" -c user.name=check -c user.email=check@invalid commit -q -m "$kind"
done

# Runs one subject of one kind under one signal; status 0 when it stops.
stops() {
  kind=$1 script=$2 trigger=$3 signal=$4 expected=$5
  state=$scratch/state-$kind-$script-$signal
  mkdir "$state" "$state/tmp"
  PATH=$scratch/bin:$PATH PYTHON=python3 TMPDIR=$state/tmp GOROROBA_QUANTUM=$scratch/quantum \
    SIGNAL_TRAPS_STATE=$state SIGNAL_TRAPS_TRIGGER=$trigger \
    env --default-signal=INT sh "$scratch/$kind/ci/$script" </dev/null >"$state/output" 2>&1 &
  pid=$!
  count=0
  while [ ! -e "$state/started" ]; do
    count=$((count + 1))
    [ "$count" -le 300 ] && kill -0 "$pid" 2>/dev/null || {
      wait "$pid" || :
      echo "check_signal_traps: $kind ci/$script never reached $trigger" >&2
      cat "$state/output" >&2
      return 2
    }
    sleep 0.1
  done
  kill "-$signal" "$pid"
  : >"$state/signaled"
  got=0
  wait "$pid" || got=$?
  [ "$got" -eq "$expected" ] && [ ! -e "$state/later" ] && [ -z "$(ls -A "$state/tmp")" ] || {
    echo "check_signal_traps: $kind ci/$script after $signal: status $got, later stages: $(tr '\n' ' ' <"$state/later" 2>/dev/null || :)" >&2
    return 1
  }
}

failed=0
runs=0
while IFS=: read -r script trigger; do
  for pair in INT:130 TERM:143; do
    signal=${pair%%:*}
    expected=${pair#*:}
    stops good "$script" "$trigger" "$signal" "$expected" || failed=1
    status=0
    stops mutant "$script" "$trigger" "$signal" "$expected" 2>/dev/null || status=$?
    [ "$status" -eq 1 ] || {
      echo "check_signal_traps: the mutant of ci/$script stopped after $signal (status $status)" >&2
      failed=1
    }
    runs=$((runs + 1))
  done
done <<EOF
$subjects
EOF
[ "$failed" -eq 0 ] || exit 1
echo "check_signal_traps: $runs subject runs stop with the signal status; each mutant fails the test"
