#!/bin/sh
# Usage: GOROROBA_OPEN=PATH PYTHON=PATH sh ci/compare_split_tower.sh
# Compares the basis products of the split Cayley-Dickson tower in two implementations on the same
# inputs (ci/compare_split_tower.py): ZT.mul n g of rocq/quantum/SplitDoublingTower.v with
# g k = gammas[k], and cd_multiply_split of crates/cd_kernel/src/cayley_dickson/signature.rs in the
# gororoba-open checkout that GOROROBA_OPEN names, run through a temporary crate that depends on
# cd_kernel by path. Both evaluate e_p e_q for every p, q below 2^n at the levels n = 2 and 3 under
# every signature of {-1, 1}^n, 12 signatures, 576 products and 4,352 coordinates. Rocq evaluates with Compute after
# compiling the source from a copy of this checkout. Before the verdict counts, the comparison must
# reject a second Rocq evaluation of the same source whose signatures carry the opposite sign.
# Runs on demand, outside ci/check.sh, because it needs the Rocq switch of ci/install_rocq.sh and
# cargo with the crate cache of the checkout (the build runs with --offline; CARGO_TARGET_DIR names
# a persistent build tree, otherwise a temporary one is built and removed).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool, the switch or the
# checkout is missing, or a source does not build. The script writes only under a temporary
# directory it removes, and under CARGO_TARGET_DIR when that is set.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git opam cargo "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_split_tower: $tool is not on PATH" >&2
    exit 2
  }
done
[ -n "${GOROROBA_OPEN:-}" ] && [ -f "$GOROROBA_OPEN/crates/cd_kernel/src/cayley_dickson/signature.rs" ] || {
  echo "compare_split_tower: set GOROROBA_OPEN to a gororoba-open checkout" >&2
  exit 2
}
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_split_tower: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
open=$(CDPATH='' cd -- "$GOROROBA_OPEN" && pwd)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir "$work/quantum" "$work/ref" "$work/ref/src"
git -C "$root" show HEAD:rocq/quantum/SplitDoublingTower.v >"$work/quantum/SplitDoublingTower.v"
"$PYTHON" -I -B "$here/compare_split_tower.py" cases "$work/quantum/CompareSplitTower.v" \
  "$work/quantum/CompareSplitTowerMutant.v" || exit 2

cat >"$work/ref/Cargo.toml" <<EOF
[package]
name = "split_reference"
version = "0.0.0"
edition = "2021"

[dependencies]
cd_kernel = { path = "$open/crates/cd_kernel" }

[workspace]
EOF
cat >"$work/ref/src/main.rs" <<'EOF'
use cd_kernel::cayley_dickson::{cd_multiply_split, CdSignature};

fn main() {
    for n in 2..=3usize {
        let dim = 1usize << n;
        for mask in 0..(1usize << n) {
            let gammas: Vec<i32> = (0..n).map(|i| if (mask >> i) & 1 == 1 { 1 } else { -1 }).collect();
            let sig = CdSignature::from_gammas(&gammas);
            let names: Vec<String> = gammas.iter().map(|g| g.to_string()).collect();
            let mut line = format!("{} {}", n, names.join(","));
            for p in 0..dim {
                for q in 0..dim {
                    let mut a = vec![0.0f64; dim];
                    let mut b = vec![0.0f64; dim];
                    a[p] = 1.0;
                    b[q] = 1.0;
                    for v in cd_multiply_split(&a, &b, &sig) {
                        line.push_str(&format!(" {}", v as i64));
                    }
                }
            }
            println!("{}", line);
        }
    }
}
EOF
[ ! -f "$open/Cargo.lock" ] || cp "$open/Cargo.lock" "$work/ref/Cargo.lock"
CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$work/target}
export CARGO_TARGET_DIR
echo "compare_split_tower: building the cd_kernel reference"
(cd "$work/ref" && cargo run -q --offline --release >"$work/rust.txt" 2>"$work/cargo.log") || {
  echo "compare_split_tower: the Rust reference does not build or run:" >&2
  tail -n 20 "$work/cargo.log" >&2
  exit 2
}
(
  cd "$work/quantum"
  for source in SplitDoublingTower; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source.v" >>"$work/compile.log" 2>&1 || {
      echo "compare_split_tower: $source.v does not compile:" >&2
      tail -n 20 "$work/compile.log" >&2
      exit 2
    }
  done
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareSplitTower.v >"$work/rocq.txt" 2>&1 || {
    echo "compare_split_tower: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareSplitTowerMutant.v >"$work/mutant.txt" 2>&1 || {
    echo "compare_split_tower: the mutated Rocq evaluation fails:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
)
status=0
"$PYTHON" -I -B "$here/compare_split_tower.py" compare "$work/rust.txt" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_split_tower: the comparison did not reject the mutated Rocq reference (status $status)" >&2
  exit 1
}
echo "compare_split_tower: the Rocq tower with the sign of gamma exchanged is rejected"
"$PYTHON" -I -B "$here/compare_split_tower.py" compare "$work/rust.txt" "$work/rocq.txt" || exit $?
