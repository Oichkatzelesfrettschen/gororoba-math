#!/bin/sh
# Usage: sh ci/install_rocq.sh
# Builds the opam switch the Rocq trees compile under: OCaml 5.5.1,
# rocq-core 9.3.0, rocq-stdlib 9.2.0 and the libraries rocq/open imports
# (Flocq, MathComp, Hierarchy Builder, Elpi, Equations, ExtLib, the micromega
# plugin), at the versions rocq/open/opam/qualified-rocq-9.3.export records.
# rocq/open/opam is an opam repository holding the ports of the packages
# whose released metadata excludes Rocq 9.3.
# The switch is named rocq-9.3 and takes no other name: two test harnesses
# of rocq/open run their subprocesses under --switch=rocq-9.3, and a retained
# record of gororoba-open cites one of them by digest.
# Environment: OPAMROOT (default ~/.opam),
# OPAMJOBS (default the online processor count).
# A switch that already holds every root package of the export is left
# unchanged, so a restored cache makes a second run a no-op. The check reads
# the 14 root packages; the other packages of the export are their
# dependencies, which opam switch import installs at the recorded versions
# and which this script does not compare afterwards. The export pins each
# package version, and opam.ocaml.org and rocq-prover.org supply the
# metadata and checksums of those versions at the time of the run.
# Exit status: 0 the switch holds every root package, 1 an opam step failed,
# 2 a tool is missing. Reaches opam.ocaml.org and rocq-prover.org.
set -eu

for tool in git opam getconf; do
  command -v "$tool" >/dev/null || {
    echo "install_rocq: $tool is not on PATH" >&2
    exit 2
  }
done

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
ports="$root/rocq/open/opam"
export="$ports/qualified-rocq-9.3.export"
switch=rocq-9.3
OPAMJOBS=${OPAMJOBS:-$(getconf _NPROCESSORS_ONLN)}
export OPAMJOBS OPAMYES=1

# The root packages of the export, one "name.version" per line. The parser
# reads the lines between "roots: [" and "]", so an export that opens the
# list in another layout fails here.
grep -q -x 'roots: \[' "$export" || {
  echo "install_rocq: $export does not open its root list with the line 'roots: ['" >&2
  exit 1
}
roots=$(awk '/^roots: \[/ { inside = 1; next } inside && /^\]/ { exit } inside { gsub(/[" ]/, ""); print }' "$export")
[ -n "$roots" ] || {
  echo "install_rocq: $export names no root package" >&2
  exit 1
}

missing_roots() {
  installed=$(opam list --switch="$switch" --installed --columns=package --short 2>/dev/null || true)
  for package in $roots; do
    printf '%s\n' "$installed" | grep -q -x -F "$package" || echo "$package"
  done
}

opam_root=${OPAMROOT:-$HOME/.opam}
if [ ! -f "$opam_root/config" ]; then
  opam init --bare --disable-sandboxing --no-setup
fi
if ! opam switch list --short | grep -q -x -F "$switch"; then
  opam switch create "$switch" ocaml-base-compiler.5.5.1
fi
if [ -n "$(missing_roots)" ]; then
  if ! opam repository list --switch="$switch" --short | grep -q -x rocq-released; then
    opam repository add rocq-released https://rocq-prover.org/opam/released --switch="$switch"
  fi
  # A restored opam root keeps the checkout path of the run that saved it.
  if opam repository list --all --short | grep -q -x gororoba-proof-ports; then
    opam repository set-url gororoba-proof-ports "file://$ports"
  else
    opam repository add gororoba-proof-ports "$ports" --switch="$switch"
  fi
  opam install --switch="$switch" rocq-core.9.3.0 rocq-stdlib.9.2.0 coq-flocq.4.2.2 dune.3.23.1
  opam switch import --switch="$switch" "$export"
fi

left=$(missing_roots)
if [ -n "$left" ]; then
  echo "install_rocq: switch $switch lacks:" >&2
  printf '%s\n' "$left" >&2
  exit 1
fi
echo "install_rocq: switch $switch holds every root package of $(basename "$export")"
opam exec --switch="$switch" -- rocq --version
