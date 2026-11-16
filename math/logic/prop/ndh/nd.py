#!/usr/bin/env python3

# A small natural deduction proof verifier for propositional logic that
# allows inference rules to be stated as axioms of a Hilbert system in
# which sequents are treated as propositions.
#
# Note that the equivalence of A ∧ B ⊢ C and A, B ⊢ C is automatically
# applied in this verifier. As part of a rule, one can only type in the
# first one.
#
# USAGE
# nd.py proofs.txt
#     If the program stays quiet, the deductions should be correct.
#
# nd.py -f proofs.txt
#     Format ASCII input to common notation.

from sys import argv, exit, stderr

class SyntaxError(ValueError):
    def __init__(self, line, text):
        self.line = line; self.text = text

class LogicError(ValueError):
    def __init__(self, line, text):
        self.line = line; self.text = text

sym2 = {"->": "->", "=>": "->", "/\\": "&", "\\/": "|", "|-": "|-"}
sym3 = {"<->": "<->", "<=>": "<->"}
kw_tab = {"and": "&", "or": "|", "not": "~", "box": "□", "dia": "◇",
    "false": "falsum", "true": "verum"}

def scan(s):
    i = 0; n = len(s); a = []; line = 1
    while i < n:
        if s[i].isalpha():
            j = i
            while i < n and (s[i].isalnum() or s[i] in "_'"):
                i += 1
            if s[j:i] in kw_tab:
                a.append((kw_tab[s[j:i]], line))
            else:
                a.append((s[j:i], line))
        elif s[i].isdigit():
            j = i
            while i < n and s[i].isdigit():
                i += 1
            a.append((int(s[j:i]), line))
        elif s[i].isspace():
            if s[i] == "\n": line += 1
            i += 1
        elif i + 2 < n and s[i:i+3] in sym3:
            a.append((sym3[s[i:i+3]], line))
            i += 3
        elif i + 1 < n and s[i:i+2] in sym2:
            a.append((sym2[s[i:i+2]], line))
            i += 2
        elif s[i] == '#':
            while i < n and s[i] != '\n':
                i += 1
        elif s[i] == '(' and i + 1 < n and s[i+1] == '*':
            comment_line = line
            while i + 1 < n and (s[i] != '*' or s[i+1] != ')'):
                if s[i] == '\n': line += 1
                i += 1
            if i + 1 >= n:
                raise SyntaxError(comment_line, "unclosed comment")
            i += 2
        else:
            a.append((s[i], line))
            i += 1
    a.append((None, line))
    return a

def atom(a, i):
    token = a[i][0]
    if token == "falsum" or token == "⊥":
        return i + 1, ("falsum",)
    elif token == "verum" or token == "⊤":
        return i + 1, ("verum",)
    elif isinstance(token, str) and token[0].isalpha():
        return i + 1, token
    elif token == "(":
        i, x = sequent(a, i + 1)
        if a[i][0] != ")":
            raise SyntaxError(a[i][1], "expected ')'")
        return i + 1, x
    else:
        raise SyntaxError(a[i][1],
            f"expected an atom, but got '{token}'")

def negation(a, i):
    if a[i][0] == "~" or a[i][0] == "¬":
        i, x = negation(a, i + 1)
        return i, ("neg", x)
    elif a[i][0] == "□":
        i, x = negation(a, i + 1)
        return i, ("nec", x)
    elif a[i][0] == "◇":
        i, x = negation(a, i + 1)
        return i, ("pos", x)
    else:
        return atom(a, i)

def conjunction(a, i):
    i, x = negation(a, i)
    while a[i][0] == "&" or a[i][0] == "∧":
        i, y = negation(a, i + 1)
        x = ("conj", x, y)
    return i, x

def disjunction(a, i):
    i, x = conjunction(a, i)
    while a[i][0] == "|" or a[i][0] == "∨":
        i, y = conjunction(a, i + 1)
        x = ("disj", x, y)
    return i, x

def subjunction(a, i):
    i, x = disjunction(a, i)
    if a[i][0] == "->" or a[i][0] == "→" or a[i][0] == "⇒":
        i, y = subjunction(a, i + 1)
        return i, ("subj", x, y)
    else:
        return i, x

def equijunction(a, i):
    i, x = subjunction(a, i)
    if a[i][0] == "<->" or a[i][0] == "↔" or a[i][0] == "⇔":
        i, y = subjunction(a, i + 1)
        return i, ("equi", x, y)
    else:
        return i, x

def sequent(a, i):
    if a[i][0] == "|-" or a[i][0] == "⊢":
        x = ("verum",)
    else:
        i, x = equijunction(a, i)
    if a[i][0] == "|-" or a[i][0] == "⊢":
        i, y = sequent(a, i + 1)
        return i, ("seq", x, y)
    else:
        return i, x

def is_identifier(t):
    return isinstance(t, str) and t[0].isalpha()

def rule_app(a, i):
    acc = []
    if not isinstance(a[i][0], int) and not is_identifier(a[i][0]):
        raise SyntaxError(a[i][1], "expected identifier or label")
    acc.append(a[i][0])
    i += 1
    while True:
        token = a[i][0]
        if isinstance(token, int) or is_identifier(token):
            acc.append(token); i += 1
        elif a[i][0] == ".":
            return i, acc
        else:
            raise SyntaxError(a[i][1], "expected identifier or label")

def ref_context(a, i):
    acc = []
    if a[i][0] == "|-" or a[i][0] == "⊢":
        return i, acc
    while True:
        token = a[i][0]
        if isinstance(token, int) or is_identifier(token):
            acc.append(token)
            i += 1
        if a[i][0] != ",": break
        i += 1
    return i, acc

def ref_sequent(a, i):
    i, ctx = ref_context(a, i)
    if a[i][0] == "|-" or a[i][0] == "⊢":
        i, x = sequent(a, i + 1)
        return i, ("ref_seq", ctx, x)
    else:
        raise SyntaxError(a[i][1], "expected context")

def parse_statement(i, a):
    label, line = a[i]; i += 1
    if not isinstance(label, int) and not is_identifier(label):
        raise SyntaxError(line, "expected identifier or label")
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    if isinstance(a[i+1][0], int) or a[i+1][0] in ("|-", "⊢"): 
        i, A = ref_sequent(a, i + 1)
    else:
        i, A = sequent(a, i + 1)
    if a[i][0] != ",":
        raise SyntaxError(a[i][1], "expected ','")
    i, rule = rule_app(a, i + 1)
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    return i + 1, (line, label, A, rule)

def parse(s):
    a = scan(s); i = 0; statements = []
    while a[i][0] != None:
        i, stmt = parse_statement(i, a)
        statements.append(stmt)
    return statements

def subst_rec(A, subst):
    if isinstance(A, str):
        if not A in subst: subst[A] = A
        return subst[A]
    else:
        return (A[0],) + tuple(subst_rec(X, subst) for X in A[1:])

def conj_set(A, subst):
    if A == ("verum",):
        return set()
    elif isinstance(A, tuple) and A[0] == "conj":
        return conj_set(A[1], subst) | conj_set(A[2], subst)
    elif not subst is None:
        return conj_set(subst_rec(A, subst), None)
    else:
        return {A}

def unify(A, pattern, subst):
    if isinstance(pattern, str):
        if pattern in subst:
            return subst[pattern] == A
        subst[pattern] = A
        return True
    if not isinstance(A, tuple):
        return False
    if len(A) != len(pattern) or A[0] != pattern[0]:
        return False
    if pattern[0] == "seq":
        tmp = subst.copy()
        if unify(A[1], pattern[1], tmp):
            subst.update(tmp)
        elif conj_set(A[1], None) != conj_set(pattern[1], subst):
            return False
        return unify(A[2], pattern[2], subst)
    for i in range(1, len(A)):
        if not unify(A[i], pattern[i], subst):
            return False
    return True

def modus_ponens(line, book, B, args):
    assert len(args) >= 1
    if args[0] not in book:
        raise LogicError(line, f"unknown label '{args[0]}'")
    C = book[args[0]]
    subst = {}
    for i in range(1, len(args)):
        if args[i] not in book:
            raise LogicError(line, f"unknown label '{args[i]}'")
        A = book[args[i]]
        if not isinstance(C, tuple) or C[0] != "subj":
            raise LogicError(line, "expected a rule/subjunction")
        if not unify(A, C[1], subst):
            raise LogicError(line,
                f"unification failed for {args[0]}, argument {i}")
        C = C[2]
    if not unify(B, C, subst):
        raise LogicError(line,
            f"unification failed for {args[0]}, in conclusion")

def nec_seq(line, book, B, args):
    if len(args) != 2:
        raise LogicError(line, "expected one argument for nec_seq")
    if args[1] not in book:
        raise LogicError(line, f"unknown label '{args[1]}'")
    A = book[args[1]]; subst = {"A": A}
    if not unify(B, ("seq", "H", "A"), subst):
        raise LogicError(line, "unification failed for nec_seq")

def unfold_labels(book, line, label, B):
    Gamma = B[1]; A = B[2]
    H = ("verum",)
    for k in Gamma:
        if k == label:
            E = A
        else:
            if k not in book:
                raise LogicError(line, f"unknown label '{k}'")
            if not isinstance(book[k], tuple) or book[k][0] != "seq":
                raise LogicError(line, f"label '{k}' is not a sequent")
            E = book[k][2]
        H = ("conj", H, E)
    return ("seq", H, A)

def verify(book, s):
    statements = parse(s)
    for (line, label, B, rule) in statements:
        if label in rule:
            raise LogicError(line, "cyclic deduction")
        if isinstance(B, tuple) and B[0] == "ref_seq":
            B = unfold_labels(book, line, label, B)
        if rule[0] == "nec_seq":
            nec_seq(line, book, B, rule)
        elif rule[0] not in ("axiom", "rule"):
            modus_ponens(line, book, B, rule)
        book[label] = B

fmt_tab = {
    "&": "∧", "|": "∨", "~": "¬", "->": "→", "=>": "→",
    "/\\": "∧", "\\/": "∨", "|-": "⊢", "<->": "↔", "<=>": "↔"
}
fmt_kw_tab = {
    "and": "∧", "or": "∨", "not": "¬", "box": "□", "dia": "◇",
    "falsum": "⊥", "false": "⊥"
}
unspace_set = {"not", "box", "dia"}

def format_source_code(s):
    acc = []; i = 0; n = len(s)
    while i < n:
        fmt = False
        for k in range(3, 0, -1):
            if i + k - 1 < n and s[i:i+k] in fmt_tab:
                acc.append(fmt_tab[s[i:i+k]])
                i += k; fmt = True; break
        if not fmt:
            if s[i].isalpha() or s[i] == '_':
                j = i
                while i < n and (s[i].isalnum() or s[i] in "_'"):
                    i += 1
                sji = s[j:i]; sf = fmt_kw_tab.get(sji)
                acc.append(sji if sf is None else sf)
                if sji in unspace_set and i < n and s[i] == ' ':
                    i += 1
            elif s[i] == '#':
                while i < n and s[i] != '\n':
                    acc.append(s[i])
                    i += 1
            elif s[i] == '(' and i + 1 < n and s[i+1] == '*':
                while i + 1 < n and (s[i] != '*' or s[i+1] != ')'):
                    acc.append(s[i])
                    i += 1
                acc.append(s[i:i+2])
                i += 2
            else:
                acc.append(s[i])
                i += 1
    return "".join(acc)

def read_all(path):
    with open(path) as f:
        return f.read()

prelude = """
hypo. (verum ∧ H ⊢ H), rule.
conj_intro. (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ A ∧ B), rule.
conj_eliml. (H ⊢ A ∧ B) → (H ⊢ A), rule.
conj_elimr. (H ⊢ A ∧ B) → (H ⊢ B), rule.
disj_introl. (H ⊢ A) → (H ⊢ A ∨ B), rule.
disj_intror. (H ⊢ B) → (H ⊢ A ∨ B), rule.
disj_elim. (H1 ⊢ A ∨ B) → (H2 ∧ A ⊢ C) → (H3 ∧ B ⊢ C) →
  (H1 ∧ H2 ∧ H3 ⊢ C), rule.
subj_intro. (H ∧ A ⊢ B) → (H ⊢ A → B), rule.
subj_elim. (H1 ⊢ A → B) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ B), rule.
neg_intro. (H ∧ A ⊢ ⊥) → (H ⊢ ¬A), rule.
neg_elim. (H1 ⊢ ¬A) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ ⊥), rule.
equi_intro. (H1 ⊢ A → B) → (H2 ⊢ B → A) → (H1 ∧ H2 ⊢ A ↔ B), rule.
equi_eliml. (H ⊢ A ↔ B) → (H ⊢ A → B), rule.
equi_elimr. (H ⊢ A ↔ B) → (H ⊢ B → A), rule.
wk. (H ⊢ B) → (H ∧ A ⊢ B), rule.
exch. (H ⊢ A) → (H ⊢ A), rule.
"""

def verify_file(book, path):
    try:
        verify(book, read_all(path))
    except (SyntaxError, LogicError) as e:
        kind = "Logic" if isinstance(e, LogicError) else "Syntax"
        msg = f"{kind} error in {path}, line {e.line}:\n{e.text}"
        print(msg, file=stderr)
        exit(1)

def main():
    if len(argv) < 2 or (argv[1] == "-f" and len(argv) < 3):
        print("usage: nd.py [-f] proofs.txt", file=stderr)
        exit(1)
    if argv[1] == "-f":
        text = read_all(argv[2])
        text_fmt = format_source_code(text)
        if text[0:3] == "#nd":
            if text != text_fmt:
                with open(argv[2], "w") as fout:
                    fout.write(text_fmt)
        else:
            print(text_fmt)
    else:
        book = {}
        verify(book, prelude)
        for path in argv[1:]:
            verify_file(book, path)

if __name__ == "__main__":
    main()
