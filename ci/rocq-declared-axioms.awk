# Usage: awk -f ci/rocq-declared-axioms.awk SOURCE.v
# Prints one line "NESTED.MODULE.PATH.NAME" (the name alone at file level) for each top-level declaration
# of an assumption in a Rocq source: Axiom, Axioms, Parameter, Parameters,
# Conjecture, Conjectures at any depth outside a Module Type, and Hypothesis,
# Hypotheses outside a Section as well. Comments (nested) are removed first.
# Limits, a textual reading: a declaration that continues over several lines
# contributes its first line's names; a Module that opens with a body after
# ":=" on a later line, and a keyword inside a string literal, are misread. The
# kernel check (rocq check -o) stays the authority on a tree's assumptions.
function push(kind, name) { depth++; kinds[depth] = kind; names[depth] = name }
function pop() { if (depth > 0) depth-- }
function in_module_type(i) { for (i = 1; i <= depth; i++) if (kinds[i] == "T") return 1; return 0 }
function in_section(i) { for (i = 1; i <= depth; i++) if (kinds[i] == "S") return 1; return 0 }
function module_path(i, path) { path = ""; for (i = 1; i <= depth; i++) if (kinds[i] == "M") path = path (path == "" ? "" : ".") names[i]; return path }
function emit(rest, i, count, tokens, token) {
  sub(/:.*/, "", rest)
  gsub(/[()]/, " ", rest)
  count = split(rest, tokens, /[ \t]+/)
  for (i = 1; i <= count; i++) {
    token = tokens[i]
    sub(/\.$/, "", token)
    if (token != "") print (module_path() == "" ? "" : module_path() ".") token
  }
}
{
  line = $0
  clean = ""
  length_of_line = length(line)
  for (position = 1; position <= length_of_line; position++) {
    pair = substr(line, position, 2)
    if (pair == "(*") { comment++; position++; continue }
    if (pair == "*)" && comment > 0) { comment--; position++; continue }
    if (comment == 0) clean = clean substr(line, position, 1)
  }
  line = clean
  sub(/^[ \t]*Local[ \t]+/, "", line)
  sub(/^[ \t]*Global[ \t]+/, "", line)
  sub(/^[ \t]+/, "", line)
  if (match(line, /^Section[ \t]+[A-Za-z0-9_']+[ \t]*\./)) { push("S", ""); next }
  if (match(line, /^Module[ \t]+Type[ \t]+[A-Za-z0-9_']+/) && line !~ /:=/) { push("T", ""); next }
  if (match(line, /^Module[ \t]+[A-Za-z0-9_']+/) && line !~ /:=/ && line ~ /\.[ \t]*$/) {
    name = line
    sub(/^Module[ \t]+/, "", name)
    sub(/[^A-Za-z0-9_'].*/, "", name)
    push("M", name)
    next
  }
  if (match(line, /^End[ \t]+[A-Za-z0-9_']+[ \t]*\./)) { pop(); next }
  if (in_module_type()) next
  if (match(line, /^(Axioms?|Parameters?|Conjectures?)[ \t]/)) {
    rest = line
    sub(/^[A-Za-z]+[ \t]+/, "", rest)
    emit(rest)
    next
  }
  if (!in_section() && match(line, /^Hypothes[ie]s[ \t]/)) {
    rest = line
    sub(/^[A-Za-z]+[ \t]+/, "", rest)
    emit(rest)
  }
}
