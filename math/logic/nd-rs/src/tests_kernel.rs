
use super::{
    Env, verify, ErrorKind, load_prelude, KEYWORDS, Error,
    Term, Type, Var, Const, PatVar, App, Lambda, BoundVar, term,
    Prop, Ind, fn_type, scan, formula_type_checked,
    Expr, Item, parse_items, parse_formula, define_macro, expand,
    Bstr, Subs, Binding, unify, pattern_from, term_eq,
    free_in, subs_rec, replace_terms, defined_name
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Expected {Ok, ErrLogic, ErrSyntax, ErrType}

const OK: Expected = Expected::Ok;
const ELOGIC: Expected = Expected::ErrLogic;
const ESYNTAX: Expected = Expected::ErrSyntax;
const ETYPE: Expected = Expected::ErrType;

#[test]
fn keywords_sorted() {
    fn is_sorted(a: &[(&[u8], &str, u8)]) -> bool {
        let mut i = 1;
        while i < a.len() {
            if a[i-1].0 >= a[i].0 {return false;}
            i += 1;
        }
        true
    }
    assert!(is_sorted(KEYWORDS));
}

// Environment with the prelude. It declares the logical vocabulary
// only; the operators of a theory (element, add, lt, ...) must be
// declared by the test.
fn new_env() -> Env {
    let mut env = Env::new();
    load_prelude(&mut env);
    env
}

fn run_list(tests: &[(&str, Expected, &str)]) {
    let mut env = Env::new();
    for (test_id, expected, code) in tests {
        env.reset();
        load_prelude(&mut env);
        let result = match verify(&mut env, code.as_bytes()) {
            Ok(()) => OK,
            Err(e) => {
                if *expected == OK {
                    println!("\nERROR MESSAGE:\n{}", e.info);
                }
                match e.kind {
                    ErrorKind::Logic => ELOGIC,
                    ErrorKind::Syntax => ESYNTAX,
                    ErrorKind::Type => ETYPE
                }
            }
        };
        assert!(result == *expected, "Test {} failed.", test_id);
    }
}

#[test]
fn run_test_list() {
    run_list(TESTS);
}

fn check_type(t: &Term, id: &str, ty: &Type) -> Result<(), ()> {
    match &t.value {
        Var(x) | Const(x) | PatVar(x) => {
            if x.as_slice() == id.as_bytes() {
                if t.ty != *ty {return Err(());}
            }
        },
        App(a) => {
            for x in a.iter() {check_type(x, id, ty)?;}
        },
        Lambda(x) => {
            check_type(x, id, ty)?;
        }
        _ => {}
    }
    Ok(())
}

fn assert_type(test_id: &str, code: &str, s: &str, id: &str, ty: Type) {
    let mut env = new_env();
    if !code.is_empty() {
        // Allows for definitions
        let Ok(_) = verify(&mut env, code.as_bytes()) else {
            unreachable!()
        };
    }
    env.tokens = scan(s.as_bytes()).unwrap();
    env.index.set(0);
    let Ok(t) = formula_type_checked(&env) else {unreachable!("Test {}", test_id)};
    let result = check_type(&t, id, &ty);
    assert!(matches!(result, Ok(_)), "Type test {} failed.", test_id);
}

#[test]
fn type_tests() {
    for (test_id, code, term, id, ty) in TYPE_TESTS {
        assert_type(test_id, code, term, id, ty());
    }
}

static TESTS: &[(&str, Expected, &str)] = &[
("01.01", OK, ""),
("01.02", OK, "
1. 1 ⊢ A, hypo.
2. ⊢ A → A, subj_intro 1.
"),
("01.03", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. ⊢ A ∧ B → A ∧ B, subj_intro 1.
"),
("01.04", OK, "
1. 1 ⊢ A ∧ B ∧ C, hypo.
2. ⊢ A ∧ B ∧ C → A ∧ B ∧ C, subj_intro 1.
"),
("01.05", OK, "
1. 1 ⊢ A ∧ B ∧ C ∧ D, hypo.
2. ⊢ A ∧ B ∧ C ∧ D → A ∧ B ∧ C ∧ D, subj_intro 1.
"),
("01.06", OK, "
1. 1 ⊢ A → B, hypo.
2. ⊢ (A → B) → A → B, subj_intro 1.
"),
("01.07", OK, "
1. 1 ⊢ A → B → C, hypo.
2. ⊢ (A → B → C) → A → B → C, subj_intro 1.
"),
("01.08", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
"),
("01.09", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 2, 1 ⊢ A ∧ B, conj_intro 1 2.
"),
("01.10", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ B ∧ A, conj_intro 2 1.
"),
("01.11", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 1, 2, 3 ⊢ A ∧ B ∧ C, conj_intro 4 3.
"),
("01.12", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 3, 2, 1 ⊢ A ∧ B ∧ C, conj_intro 4 3.
"),
("01.13", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 3, 1, 2 ⊢ C ∧ (A ∧ B), conj_intro 3 4.
"),
("01.14", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 2, 1 ⊢ A ∧ B, conj_intro 1 2.
5. 1, 2, 3 ⊢ C ∧ (A ∧ B), conj_intro 3 4.
"),
("01.15", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A ∨ B, disj_introl 1.
"),
("01.16", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ B ∨ A, disj_intror 1.
"),
("01.17", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A ∨ A, disj_introl 1.
"),
("01.18", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A ∨ A, disj_intror 1.
"),
("01.19", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A ∧ B ∨ C, disj_introl 1.
"),
("01.20", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ C ∨ A ∧ B, disj_intror 1.
"),
("01.21", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A ∧ B ∨ A ∧ B, disj_introl 1.
"),
("01.22", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A ∧ B ∨ A ∧ B, disj_intror 1.
"),
("01.23", OK, "
1. 1 ⊢ ⊥, hypo.
2. ⊢ ¬⊥, neg_intro 1.
"),
("01.24", OK, "
1. 1 ⊢ A → B, hypo.
2. 2 ⊢ B → A, hypo.
3. 1, 2 ⊢ A ↔ B, equi_intro 1 2.
"),
("01.25", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A, conj_eliml 1.
"),
("01.26", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ B, conj_elimr 1.
"),
("01.27", OK, "
1. 1 ⊢ A ∧ B ∧ C, hypo.
2. 1 ⊢ A ∧ B, conj_eliml 1.
"),
("01.28", OK, "
1. 1 ⊢ A ∧ B ∧ C, hypo.
2. 1 ⊢ C, conj_elimr 1.
"),
("01.29", OK, "
1. 1 ⊢ A → B, hypo.
2. 2 ⊢ A, hypo.
3. 1, 2 ⊢ B, subj_elim 1 2.
"),
("01.30", OK, "
1. 1 ⊢ A ∧ B → C ∧ D, hypo.
2. 2 ⊢ A ∧ B, hypo.
3. 1, 2 ⊢ C ∧ D, subj_elim 1 2.
"),
("01.31", OK, "
1. 1 ⊢ A → B → C, hypo.
2. 2 ⊢ A, hypo.
3. 1, 2 ⊢ B → C, subj_elim 1 2.
4. 4 ⊢ B, hypo.
5. 1, 2, 4 ⊢ C, subj_elim 3 4.
6. 4, 2, 1 ⊢ C, subj_elim 3 4.
"),
("01.32", OK, "
1. 1 ⊢ A ↔ B, hypo.
2. 1 ⊢ A → B, equi_eliml 1.
"),
("01.33", OK, "
1. 1 ⊢ A ↔ B, hypo.
2. 1 ⊢ B → A, equi_elimr 1.
"),
("01.34", OK, "
1. 1 ⊢ ¬A, hypo.
2. 2 ⊢ A, hypo.
3. 2, 1 ⊢ ⊥, neg_elim 1 2.
4. 2 ⊢ ¬¬A, neg_intro 3.
5. ⊢ A → ¬¬A, subj_intro 4.
"),
("01.35", OK, "
1. 1 ⊢ (A → B) ∧ A, hypo.
2. 1 ⊢ A → B, conj_eliml 1.
3. 1 ⊢ A, conj_elimr 1.
4. 1 ⊢ B, subj_elim 2 3.
5. ⊢ (A → B) ∧ A → B, subj_intro 4.
"),
("01.36", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A, conj_eliml 1.
3. 1 ⊢ B, conj_elimr 1.
4. 1 ⊢ B ∧ A, conj_intro 3 2.
5. ⊢ A ∧ B → B ∧ A, subj_intro 4.
"),
("01.37", OK, "
1. 1 ⊢ A ∨ B, hypo.
2. 2 ⊢ A, hypo.
3. 2 ⊢ B ∨ A, disj_intror 2.
4. 4 ⊢ B, hypo.
5. 4 ⊢ B ∨ A, disj_introl 4.
6. 1 ⊢ B ∨ A, disj_elim 1 3 5.
7. ⊢ A ∨ B → B ∨ A, subj_intro 6.
"),
("01.38", OK, "
1. 1 ⊢ ¬B, hypo.
2. 2 ⊢ A → B, hypo.
3. 3 ⊢ A, hypo.
4. 2, 3 ⊢ B, subj_elim 2 3.
5. 2, 1, 3 ⊢ ⊥, neg_elim 1 4.
6. 2, 1 ⊢ ¬A, neg_intro 5.
7. 2 ⊢ ¬B → ¬A, subj_intro 6.
8. ⊢ (A → B) → ¬B → ¬A, subj_intro 7.
"),

("02.01", ELOGIC, "
1. 1 ⊢ A, hypo.
2. ⊢ B → A, subj_intro 1.
"),
("02.02", ELOGIC, "
1. 1 ⊢ A, hypo.
2. ⊢ A → B, subj_intro 1.
"),
("02.03", ELOGIC, "
1. 1 ⊢ A ∧ B, hypo.
2. ⊢ A ∧ A → A ∧ A, subj_intro 1.
"),

("03.01", OK, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ A u, uq_elim 1.
"),
("03.02", OK, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ A w, uq_elim 1.
"),
("03.03", OK, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ A x, uq_elim 1.
"),
("03.04", OK, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ B u, uq_elim 1.
"),
("03.05", OK, "
1. 1 ⊢ A u, hypo.
2. ⊢ A u → A u, subj_intro 1.
3. ⊢ ∀x. A x → A x, uq_intro 2.
"),
("03.06", OK, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∃x. A x, ex_intro 1.
"),
("03.07", OK, "
1. 1 ⊢ A u ∧ B u, hypo.
2. 1 ⊢ ∃x. A x ∧ B x, ex_intro 1.
"),
("03.08", OK, "
1. 1 ⊢ A u ∧ B u, hypo.
2. 1 ⊢ A u, conj_eliml 1.
3. 1 ⊢ B u, conj_elimr 1.
4. 1 ⊢ B u ∧ A u, conj_intro 3 2.
5. 1 ⊢ ∃x. B x ∧ A x, ex_intro 4.
6. 6 ⊢ ∃x. A x ∧ B x, hypo.
7. 6 ⊢ ∃x. B x ∧ A x, ex_elim 6 5.
8. ⊢ (∃x. A x ∧ B x) → (∃x. B x ∧ A x), subj_intro 7.
"),
("03.09", OK, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ B u, uq_elim 1.
3. 1 ⊢ A u, conj_eliml 2.
4. 1 ⊢ B u, conj_elimr 2.
5. 1 ⊢ B u ∧ A u, conj_intro 4 3.
6. 1 ⊢ ∀x. B x ∧ A x, uq_intro 5.
7. ⊢ (∀x. A x ∧ B x) → (∀x. B x ∧ A x), subj_intro 6.
"),
("03.10", OK, "
1. 1 ⊢ ∀x. A ∧ P x, hypo.
2. 1 ⊢ A ∧ P u, uq_elim 1.
3. 1 ⊢ A, conj_eliml 2.
4. 1 ⊢ P u, conj_elimr 2.
5. 1 ⊢ ∀x. P x, uq_intro 4.
6. 1 ⊢ A ∧ ∀x. P x, conj_intro 3 5.
const_conj. ⊢ (∀x. A ∧ P x) → A ∧ (∀x. P x), subj_intro 6.
"),
("03.11", OK, "
1. 1 ⊢ ∃x. P x ∧ Q x, hypo.
2. 2 ⊢ P u ∧ Q u, hypo.
3. 2 ⊢ P u, conj_eliml 2.
4. 2 ⊢ Q u, conj_elimr 2.
5. 2 ⊢ ∃x. P x, ex_intro 3.
6. 2 ⊢ ∃x. Q x, ex_intro 4.
7. 2 ⊢ (∃x. P x) ∧ (∃x. Q x), conj_intro 5 6.
8. 1 ⊢ (∃x. P x) ∧ (∃x. Q x), ex_elim 1 7.
9. ⊢ (∃x. P x ∧ Q x) → (∃x. P x) ∧ (∃x. Q x), subj_intro 8.
"),
("03.12", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ B x → B x, 1.
"),
("03.13", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ A y → A y, 1.
"),
("03.14", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ B y → B y, 1.
"),
("03.15", OK, "
decl element: Ind → Ind → Prop.
1. ⊢ P x A → P x A, axiom.
2. ⊢ x ∈ A → x ∈ A, 1.
"),
("03.16", OK, "
decl element: Ind → Ind → Prop.
1. ⊢ P x A → P x A, axiom.
2. ⊢ y ∈ A → y ∈ A, 1.
"),
("03.17", OK, "
decl element: Ind → Ind → Prop.
1. ⊢ P x A → P x A, axiom.
2. ⊢ y ∈ B → y ∈ B, 1.
"),
("03.18", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀x. A x, 1.
"),
("03.19", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀y. A y, 1.
"),
("03.20", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀x. B x, 1.
"),
("03.21", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀y. B y, 1.
"),

// Unbound variables are accepted
("03.22", OK, "
1. 1 ⊢ B, hypo.
2. ⊢ B → B, subj_intro 1.
3. ⊢ ∀x. B → B, uq_intro 2.
"),
("03.23", OK, "
1. 1 ⊢ B, hypo.
2. ⊢ B → B, subj_intro 1.
3. ⊢ ∀y. B → B, uq_intro 2.
"),
("03.24", OK, "
1. 1 ⊢ B, hypo.
2. 1 ⊢ ∀x. B, uq_intro 1.
"),
("03.25", OK, "
1. 1 ⊢ B, hypo.
2. 1 ⊢ ∀y. B, uq_intro 1.
"),
("03.26", OK, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∀x. A u, uq_intro 1.
"),
("03.27", OK, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∀y. A u, uq_intro 1.
"),
("03.28", OK, "
1. 1 ⊢ A w, hypo.
2. 1 ⊢ ∀x. A w, uq_intro 1.
"),
("03.29", OK, "
1. 1 ⊢ A w, hypo.
2. 1 ⊢ ∀y. A w, uq_intro 1.
"),
("03.30", OK, "
1. 1 ⊢ A x, hypo.
2. 1 ⊢ ∀y. A x, uq_intro 1.
"),
("03.31", OK, "
1. 1 ⊢ P u, hypo.
2. 1 ⊢ ∀x. P u, uq_intro 1.
"),
("03.32", OK, "
1. 1 ⊢ P u, hypo.
2. 1 ⊢ ∀y. P u, uq_intro 1.
"),
("03.33", OK, "
1. 1 ⊢ P w, hypo.
2. 1 ⊢ ∀x. P w, uq_intro 1.
"),
("03.34", OK, "
1. 1 ⊢ P w, hypo.
2. 1 ⊢ ∀y. P w, uq_intro 1.
"),
("03.35", OK, "
1. 1 ⊢ P x, hypo.
2. 1 ⊢ ∀y. P x, uq_intro 1.
"),
("03.36", OK, "
1. 1 ⊢ Q u, hypo.
2. 1 ⊢ ∀x. Q u, uq_intro 1.
"),
("03.37", OK, "
1. 1 ⊢ Q u, hypo.
2. 1 ⊢ ∀y. Q u, uq_intro 1.
"),
("03.38", OK, "
1. 1 ⊢ Q w, hypo.
2. 1 ⊢ ∀x. Q w, uq_intro 1.
"),
("03.39", OK, "
1. 1 ⊢ Q w, hypo.
2. 1 ⊢ ∀y. Q w, uq_intro 1.
"),
("03.40", OK, "
1. 1 ⊢ Q x, hypo.
2. 1 ⊢ ∀y. Q x, uq_intro 1.
"),
("03.41", OK, "
decl p: Ind → Prop.
1. 1 ⊢ p u, hypo.
2. 1 ⊢ ∀x. p u, uq_intro 1.
"),
("03.42", OK, "
decl p: Ind → Prop.
1. 1 ⊢ p u, hypo.
2. 1 ⊢ ∀y. p u, uq_intro 1.
"),
("03.43", OK, "
decl p: Ind → Prop.
1. 1 ⊢ p w, hypo.
2. 1 ⊢ ∀x. p w, uq_intro 1.
"),
("03.44", OK, "
decl p: Ind → Prop.
1. 1 ⊢ p w, hypo.
2. 1 ⊢ ∀y. p w, uq_intro 1.
"),
("03.45", OK, "
decl p: Ind → Prop.
1. 1 ⊢ p x, hypo.
2. 1 ⊢ ∀y. p x, uq_intro 1.
"),
("03.46", OK, "
1. 1 ⊢ u = u, hypo.
2. 1 ⊢ ∀x. u = u, uq_intro 1.
"),
("03.47", OK, "
1. 1 ⊢ w = w, hypo.
2. 1 ⊢ ∀x. w = w, uq_intro 1.
"),
("03.48", OK, "
1. 1 ⊢ w = w, hypo.
2. 1 ⊢ ∀y. w = w, uq_intro 1.
"),
("03.49", OK, "
1. 1 ⊢ x = x, hypo.
2. 1 ⊢ ∀y. x = x, uq_intro 1.
"),
("03.50", OK, "
1. ⊢ x = x, axiom.
2. ⊢ ∀y. y = y, uq_intro 1.
"),
("03.51", OK, "
1. ⊢ u = u, axiom.
2. ⊢ ∀y. y = y, uq_intro 1.
"),
("03.52", OK, "
1. ⊢ w = w, axiom.
2. ⊢ ∀y. y = y, uq_intro 1.
"),
("03.53", OK, "
1. ⊢ u = u, axiom.
2. ⊢ ∀x. x = x, uq_intro 1.
"),
("03.54", OK, "
1. ⊢ x = x, axiom.
2. ⊢ ∀x. x = x, uq_intro 1.
"),

("04.01", ELOGIC, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ B u, uq_elim 1.
"),
("04.02", ELOGIC, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ A u, uq_elim 1.
"),
("04.03", ELOGIC, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ B w, uq_elim 1.
"),
("04.04", ELOGIC, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∀x. A x, uq_intro 1.
"),
("04.05", ELOGIC, "
1. 1 ⊢ A w, hypo.
2. 1 ⊢ ∀x. A x, uq_intro 1.
"),
("04.06", ELOGIC, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∀y. A y, uq_intro 1.
"),
("04.07", ELOGIC, "
1. 1 ⊢ A w, hypo.
2. 1 ⊢ ∀y. A y, uq_intro 1.
"),
("04.08", ELOGIC, "
1. 1 ⊢ A x, hypo.
2. 1 ⊢ ∀y. A y, uq_intro 1.
"),
("04.09", ELOGIC, "
1. 1 ⊢ P u, hypo.
2. 1 ⊢ ∀x. P x, uq_intro 1.
"),
("04.10", ELOGIC, "
1. 1 ⊢ P w, hypo.
2. 1 ⊢ ∀x. P x, uq_intro 1.
"),
("04.11", ELOGIC, "
1. 1 ⊢ P u, hypo.
2. 1 ⊢ ∀y. P y, uq_intro 1.
"),
("04.12", ELOGIC, "
1. 1 ⊢ P w, hypo.
2. 1 ⊢ ∀y. P y, uq_intro 1.
"),
("04.13", ELOGIC, "
1. 1 ⊢ P x, hypo.
2. 1 ⊢ ∀y. P y, uq_intro 1.
"),
("04.14", ELOGIC, "
1. 1 ⊢ Q u, hypo.
2. 1 ⊢ ∀x. Q x, uq_intro 1.
"),
("04.15", ELOGIC, "
1. 1 ⊢ Q w, hypo.
2. 1 ⊢ ∀x. Q x, uq_intro 1.
"),
("04.16", ELOGIC, "
1. 1 ⊢ Q u, hypo.
2. 1 ⊢ ∀y. Q y, uq_intro 1.
"),
("04.17", ELOGIC, "
1. 1 ⊢ Q w, hypo.
2. 1 ⊢ ∀y. Q y, uq_intro 1.
"),
("04.18", ELOGIC, "
1. 1 ⊢ Q x, hypo.
2. 1 ⊢ ∀y. Q y, uq_intro 1.
"),
("04.19", ELOGIC, "
1. 1 ⊢ B u, hypo.
2. 1 ⊢ ∃x. A x, ex_intro 1.
"),
("04.20", ELOGIC, "
1. 1 ⊢ A x, hypo.
2. ⊢ A x → A y, subj_intro 1.
"),
("04.21", ELOGIC, "
1. ⊢ A x → A x, axiom.
2. ⊢ A x → B x, 1.
"),
("04.22", ELOGIC, "
1. ⊢ A x → A x, axiom.
2. ⊢ A x → A y, 1.
"),
("04.23", ELOGIC, "
1. ⊢ A x → A x, axiom.
2. ⊢ A x → B y, 1.
"),
("04.24", ELOGIC, "
decl element: Ind → Ind → Prop.
1. ⊢ P x A → P x A, axiom.
2. ⊢ x ∈ A → x ∈ B, 1.
"),
("04.25", ELOGIC, "
decl element: Ind → Ind → Prop.
1. ⊢ P x A → P x A, axiom.
2. ⊢ x ∈ A → y ∈ A, 1.
"),
("04.26", ELOGIC, "
1. 1 ⊢ A x, axiom.
2. 1 ⊢ B x, 1.
"),
("04.27", ELOGIC, "
1. 1 ⊢ A x, axiom.
2. 1 ⊢ A y, 1.
"),
("04.28", ELOGIC, "
1. 1 ⊢ A x, axiom.
2. 1 ⊢ B y, 1.
"),
// c is declared to be a constant.
("04.29", ELOGIC, "
decl c: Ind.
1. 1 ⊢ P c, hypo.
2. ⊢ P c → P c, subj_intro 1.
3. ⊢ ∀x. P x → P x, uq_intro 2.
"),
// Eigenvariable condition: u occurs free on the right-hand side of
// the quantification (via instantiation of predicate A), so it must
// be rejected.
("04.30", ELOGIC, "
1. ⊢ u = u, axiom.
2. ⊢ ∀x. x = u, uq_intro 1.
"),
("04.31", ELOGIC, "
1. ⊢ w = w, axiom.
2. ⊢ ∀x. x = w, uq_intro 1.
"),
("04.32", ELOGIC, "
1. ⊢ u = u, axiom.
2. ⊢ ∀y. y = u, uq_intro 1.
"),
("04.33", ELOGIC, "
1. ⊢ w = w, axiom.
2. ⊢ ∀y. y = w, uq_intro 1.
"),

("05.01", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a) → A (f a), 1.
"),
("05.02", OK, "
decl f: Ind → Ind.
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a) → A (f a), 1.
"),
("05.03", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a b) → A (f a b), 1.
"),
("05.04", OK, "
decl f: Ind → Ind → Ind.
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a b) → A (f a b), 1.
"),
("05.05", OK, "
decl add: Ind → Ind → Ind.
1. ⊢ x = x, axiom.
2. ⊢ a + b = a + b, 1.
"),
("05.06", OK, "
decl add: Ind → Ind → Ind.
1. ⊢ A x → A x, axiom.
2. ⊢ A (a + b) → A (a + b), 1.
"),

("06.01", ELOGIC, "
decl p: Ind → Prop.
1. ⊢ p x → p x, axiom.
2. ⊢ A x → A x, 1.
"),
("06.02", ELOGIC, "
decl add: Ind → Ind → Ind.
1. ⊢ x = x, axiom.
2. ⊢ a + b = a + c, 1.
"),
("06.03", ELOGIC, "
decl add: Ind → Ind → Ind.
1. ⊢ x = x, axiom.
2. ⊢ x = a, 1.
"),
("06.04", ELOGIC, "
decl add: Ind → Ind → Ind.
1. ⊢ A x → A x, axiom.
2. ⊢ A (a + b) → A (a + c), 1.
"),
("06.05", ETYPE, "
1. ⊢ f x ∧ x = y → f (¬A), axiom.
"),
("06.06", ETYPE, "
1. ⊢ x = x ∧ (f x y → f (¬A) y), axiom.
"),
("06.07", ETYPE, "
1. ⊢ y = y ∧ (f x y → f x (¬A)), axiom.
"),
// In type inference with unification, x is simply of type Prop here.
("06.11", OK, "
1. ⊢ f x → f (¬A), axiom.
"),
// Occurs check
("06.12", ETYPE, "
1. ⊢ f f = f f, axiom.
"),
// Wrong arity
("06.13", ETYPE, "
decl p: Ind → Prop.
1. ⊢ p x y → p x y, axiom.
"),
// Ind instead of Prop
("06.14", ETYPE, "
decl add: Ind → Ind → Ind.
1. ⊢ a + b, axiom.
"),

/*
// TODO
("06.15", ETYPE, "
1. ⊢ P (x: Ind), axiom.
2. ⊢ P (¬A), 1.
"),
("06.16", ETYPE, "
1. ⊢ P x y, axiom.
2. ⊢ P (¬A) y, 1.
"),
("06.17", ETYPE, "
1. ⊢ P x y, axiom.
2. ⊢ P x (¬A), 1.
"),
*/

("07.01", OK, "
decl a: Ind.
decl b: Ind.
decl add: Ind → Ind → Ind.
c_eq. ⊢ c = a + b, def.
"),
("07.02", OK, "
decl a: Ind.
decl b: Ind.
decl add: Ind → Ind → Ind.
p_equi. ⊢ p ↔ a = b, def.
"),
("07.03", OK, "
decl p: Ind → Prop.
decl q: Ind → Prop.
r_equi. ⊢ r x ↔ p x ∧ q x, def.
"),
("07.04", OK, "
decl p: Ind → Prop.
decl q: Ind → Prop.
r_equi. ⊢ r ↔ ∀x. p x ∧ q x, def.
"),
("07.05", OK, "
decl f: Ind → Ind.
decl g: Ind → Ind.
h_eq. ⊢ h x = g (f x), def.
"),
("07.06", OK, "
decl f: Ind → Ind.
decl g: Ind → Ind.
r_equi. ⊢ r ↔ ∀x. f x = g x, def.
"),

("08.01", ELOGIC, "
1. ⊢ a = b, def.
"),
("08.02", ELOGIC, "
1. ⊢ a = a, def.
"),
("08.03", ELOGIC, "
1. ⊢ p ↔ q, def.
"),
("08.04", ELOGIC, "
1. ⊢ p ↔ p, def.
"),
("08.05", ELOGIC, "
1. ⊢ f x = f x, def.
"),
("08.06", ELOGIC, "
1. ⊢ f x = g x, def.
"),
("08.07", ELOGIC, "
1. ⊢ p x ↔ p x, def.
"),
("08.08", ELOGIC, "
1. ⊢ p x ↔ q x, def.
"),

("09.01", ELOGIC, "
decl c: Ind. # Declares c to be a constant symbol
eq_refl. ⊢ x = x, axiom.
1. nf u (⊥) → (⊢ u = c) → (⊢ ∀x. x = c), axiom.
2. ⊢ c = c, eq_refl.
3. ⊢ ∀x. x = c, 1 2. # nf c (⊥) fails, because c is not a variable
"),
("09.02", ELOGIC, "
decl f: Ind → Ind → Ind. # Declares f to be a fixed function symbol
eq_refl. ⊢ x = x, axiom.
1. nf u (⊥) → (⊢ u = f a b) → (⊢ ∀x. x = f a b), axiom.
2. ⊢ f a b = f a b, eq_refl.
3. ⊢ ∀x. x = f a b, 1 2.
"),
("09.03", ELOGIC, "
eq_refl. ⊢ x = x, axiom.
1. nf u (⊥) → (⊢ u = f a b) → (⊢ ∀x. x = f a b), axiom.
2. ⊢ f a b = f a b, eq_refl.
3. ⊢ ∀x. x = f a b, 1 2.
"),
("09.04", ELOGIC, "
eq_refl. ⊢ x = x, axiom.
1. nf u (⊥) → (⊢ u = f a b) → (⊢ ∀x. x = f a b), axiom.
2. ⊢ g a b = g a b, eq_refl.
3. ⊢ ∀x. x = g a b, 1 2, f a b = g a b.
"),

// Macros: evaluation before type checking
("10.01", OK, "
begin
let S ↔ A ∧ B.
1. 1 ⊢ S, hypo.
2. 1 ⊢ A, conj_eliml 1.
end
"),
// After `end`, S is an ordinary variable again.
("10.02", ELOGIC, "
begin
let S ↔ A ∧ B.
end
1. 1 ⊢ S, hypo.
2. 1 ⊢ A, conj_eliml 1.
"),
("10.03", ESYNTAX, "
end
"),
("10.04", OK, "
let Both X Y ↔ X ∧ Y.
1. 1 ⊢ Both A B, hypo.
2. 1 ⊢ A, conj_eliml 1.
"),
("10.05", ESYNTAX, "
let Both X Y ↔ X ∧ Y.
1. 1 ⊢ Both A, hypo.
"),
("10.06", ESYNTAX, "
let Both X Y ↔ X ∧ Y.
1. 1 ⊢ Both, hypo.
"),
// A macro with a quantifier, expanded twice in the same term.
("10.07", OK, "
let All P ↔ ∀x. P x.
1. 1 ⊢ All A ∧ All B, hypo.
2. 1 ⊢ All A, conj_eliml 1.
3. 1 ⊢ All B, conj_elimr 1.
"),

// A macro with a binder whose argument is a binder of the call site:
// T z must not become ∀y. y = y (variable capture).
("10.08", OK, "
let T a ↔ ∀y. y = a.
1. 1 ⊢ ∀z. T z, hypo.
2. 1 ⊢ ∀z. ∀y. y = z, exch 1.
"),
("10.09", ELOGIC, "
let T a ↔ ∀y. y = a.
1. 1 ⊢ ∀z. T z, hypo.
2. 1 ⊢ ∀z. ∀y. y = y, exch 1.
"),
("10.10", ELOGIC, "
let T a ↔ ∀y. y = a.
1. 1 ⊢ ∀z. T z, hypo.
2. 1 ⊢ ∀z. ∀y. z = y, exch 1.
"),

// Type annotations
("T.01", OK, "
decl R: Ind → Prop.
decl G: (Ind → Prop) → Prop.
1. ⊢ G R → G R, axiom.
"),
("T.02", ETYPE, "
decl add: Ind → Ind → Ind.
decl G: (Ind → Prop) → Prop.
1. ⊢ G (a + b), axiom.
"),
("T.03", ETYPE, "
1. ⊢ (A : Ind) ∧ B, axiom.
"),
("T.04", ETYPE, "
1. ⊢ (f : Ind → Ind) x y = z, axiom.
"),
("T.05", OK, "
decl element: Ind → Ind → Prop.
decl H: Prop → Prop.
1. ⊢ H (x ∈ y) → H (x ∈ y), axiom.
"),
("T.06", ETYPE, "
decl H: Prop → Prop.
1. ⊢ H a ∧ a = b, axiom.
"),
("T.07", OK, "
1. ⊢ ∀x. (x: Ind) = x, axiom.
"),
("T.08", ESYNTAX, "
1. ⊢ (x: Foo) = y, axiom.
"),
("T.09", ETYPE, "
1. ⊢ (x: Ind → Ind → Prop) = y, axiom.
"),
// An annotated declaration is treated as a sort during matching:
// R only accepts Ind, not Prop.
("T.10", ETYPE, "
decl R: Ind → Prop.
1. ⊢ R (A ∧ B), axiom.
"),
// Multi-argument types
("T.11", OK, "
1. ⊢ (f: Ind → Ind → Ind) x y = z, axiom.
"),
("T.12", ETYPE, "
1. ⊢ (f: Ind → Ind → Ind) x = y, axiom.
"),
("T.13", ETYPE, "
1. ⊢ (f: Ind → Ind → Ind) x y z = w, axiom.
"),
// No partial application: R a is not a predicate.
("T.14", ETYPE, "
decl R: Ind → Ind → Prop.
decl G: (Ind → Prop) → Prop.
1. ⊢ G (R a), axiom.
"),

// Statements
("11.01", ELOGIC, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A, nonexistent_rule 1.
"),
("11.02", ELOGIC, "
1. ⊢ A, 1.
"),
("11.03", ESYNTAX, "
1. ⊢ A, axiom
"),
("11.04", ESYNTAX, "
1 ⊢ A, axiom.
"),
("11.05", ESYNTAX, "
1. ⊢ A ∧, axiom.
"),
("11.06", ESYNTAX, "
1. ⊢ (A, axiom.
"),
("11.07", ELOGIC, "
decl f: Ind → Ind.
decl f: Ind → Ind.
"),
("11.08", ELOGIC, "
1. ⊢ A, calc.
"),

// Computation
("12.01", OK, "
decl add: Ind → Ind → Ind.
1. ⊢ 2 + 3 = 5, calc.
"),
("12.02", ELOGIC, "
decl add: Ind → Ind → Ind.
1. ⊢ 2 + 3 = 6, calc.
"),
("12.03", OK, "
decl add: Ind → Ind → Ind.
decl sub: Ind → Ind → Ind.
decl mul: Ind → Ind → Ind.
decl lt: Ind → Ind → Prop.
1. ⊢ 2 * 3 - 1 < 6, calc.
"),
("12.04", OK, "
decl lt: Ind → Ind → Prop.
1. ⊢ ¬2 < 1, calc.
"),
("12.05", ELOGIC, "
1. ⊢ a = a, calc.
"),
("12.06", ELOGIC, "
1. 1 ⊢ 2 = 2, hypo.
2. 1 ⊢ 2 = 2, calc.
"),
("12.07", OK, "
decl element: Ind → Ind → Prop.
decl ℕ: Ind.
1. ⊢ 0 ∈ ℕ, calc.
"),
("12.08", OK, "
decl element: Ind → Ind → Prop.
decl ℕ: Ind.
1. ⊢ 1 ∈ ℕ, calc.
"),
("12.09", ELOGIC, "
decl element: Ind → Ind → Prop.
decl minus: Ind → Ind.
decl ℕ: Ind.
1. ⊢ -1 ∈ ℕ, calc.
"),
("12.10", OK, "
decl element: Ind → Ind → Prop.
decl minus: Ind → Ind.
decl ℤ: Ind.
1. ⊢ -1 ∈ ℤ, calc.
"),
("12.11", ELOGIC, "
decl element: Ind → Ind → Prop.
decl mul: Ind → Ind → Ind.
decl ℕ: Ind.
1. ⊢ 5000000000 * 5000000000 ∈ ℕ, calc.
"),

// Nesting and functions as arguments
("H.01", OK, "
1. ⊢ f (f x) = f (f x), axiom.
"),
// Function as argument; subsequently used in head position.
("H.02", OK, "
twice_eq. ⊢ twice f x = f (f x), def.
decl g: Ind → Ind.
1. ⊢ twice g a = g (g a), twice_eq.
"),
// Compound arguments of P: requires imitation instead of abstraction.
("H.03", OK, "
eq_subst_f. ⊢ x = y → P (f x) → P (f y), axiom.
decl g: Ind → Ind.
decl Q: Ind → Prop.
1. 1 ⊢ a = b, hypo.
2. 2 ⊢ Q (g a), hypo.
3. 1, 2 ⊢ Q (g b), eq_subst_f 1 2.
"),
// Predicates as arguments (eta-equality between abstraction and symbol)
("H.04", OK, "
ext_ho. ⊢ (∀x. P x ↔ Q x) → (F P ↔ F Q), axiom.
decl R: Ind → Prop.
decl S: Ind → Prop.
G_eq. ⊢ G P ↔ ∀x. P x, def.
1. 1 ⊢ ∀x. R x ↔ S x, hypo.
2. 1 ⊢ G R ↔ G S, ext_ho 1.
"),
("H.05", ELOGIC, "
ext_ho. ⊢ (∀x. P x ↔ Q x) → (F P ↔ F Q), axiom.
decl R: Ind → Prop.
decl S: Ind → Prop.
decl T: Ind → Prop.
G_eq. ⊢ G P ↔ ∀x. P x, def.
1. 1 ⊢ ∀x. R x ↔ S x, hypo.
2. 1 ⊢ G R ↔ G T, ext_ho 1.
"),

// Sequents close all their variables (FV(H ⊢ A) = ∅, see
// Term::is_closed_scope). When substituting into an abstraction,
// nothing may be replaced inside them: (λt. ⊢ x = t) y is ⊢ x = t.
// With the hint P t ↔ ⊢ x = t, x = y → (⊢ x = x) → (⊢ x = y) was
// provable, even though the statement is false (⊢ x = y closes x and
// y).
("13.01", ELOGIC, "
eq_refl. ⊢ x = x, axiom.
eq_subst. ⊢ x = y → P x → P y, axiom.
1. ⊢ x = y → (⊢ x = x) → (⊢ x = y), eq_subst, P t ↔ ⊢ x = t.
"),
// In contrast, □ in the object language (nec) is an ordinary
// connective: necessity of identity holds (rigid variables), so the
// sentence is valid.
("13.02", OK, "
decl nec: Prop → Prop.
eq_subst. ⊢ x = y → P x → P y, axiom.
1. ⊢ x = y → □(x = x) → □(x = y), eq_subst, P t ↔ □(x = t).
"),
// Sequent under a universal quantifier: ∀z changes nothing,
// ⊢ x = t is closed.
("13.03", ELOGIC, "
eq_subst. ⊢ x = y → P x → P y, axiom.
1. ⊢ x = y → (∀z. (⊢ x = x)) → (∀z. (⊢ x = y)), eq_subst, P t ↔ ∀z. (⊢ x = t).
"),
// Sequent under an existential quantifier.
("13.04", ELOGIC, "
eq_subst. ⊢ x = y → P x → P y, axiom.
1. ⊢ x = y → (∃z. (⊢ x = x)) → (∃z. (⊢ x = y)), eq_subst, P t ↔ ∃z. (⊢ x = t).
"),
// ex_intro: A t would be ⊢ t = c, and t := c would confuse c inside
// the sequent with the witness. ∃x. (⊢ x = c) is false (meaning
// ∃x. ∀x'. ∀c'. x' = c'), whereas the premise ⊢ (⊢ c = c) is valid.
("13.05", ELOGIC, "
1. ⊢ (⊢ c = c), axiom.
2. ⊢ ∃x. (⊢ x = c), ex_intro 1.
"),
// If the bound parameter does not occur in the sequent, nothing
// changes.
("13.06", OK, "
1. ⊢ (⊢ c = c) ∧ a = a, axiom.
2. ⊢ ∃x. (⊢ c = c) ∧ x = x, ex_intro 1.
"),
// The same with ∀-elimination from a hypothesis.
("13.07", OK, "
1. 1 ⊢ ∀x. (⊢ c = c) ∧ x = x, hypo.
2. 1 ⊢ (⊢ c = c) ∧ a = a, uq_elim 1.
"),
// P is constant here (λt. ⊢ x = x); both sides are the same closed
// formula. This is now accepted.
("13.08", OK, "
eq_subst. ⊢ x = y → P x → P y, axiom.
1. ⊢ x = y → (⊢ x = x) → (⊢ x = x), eq_subst.
"),
// Definitions: a parameter inside a sequent is bound; otherwise,
// p x y ↔ (⊢ x = y) would have the wrong instance p a a ↔ (⊢ a = a).
("13.09", ELOGIC, "
1. ⊢ p x y ↔ (⊢ x = y), def.
"),
// Parameters under nec/pos, however, are free (e.g. modal
// definitions).
("13.10", OK, "
decl nec: Prop → Prop.
1. ⊢ p x ↔ □(x = x), def.
2. ⊢ p a ↔ □(a = a), 1.
"),
("13.11", ELOGIC, "
1. ⊢ s x = {y | (⊢ y = x)}, def.
"),
// A closed subformula without parameters is fine.
("13.12", OK, "
1. ⊢ p x ↔ x = x ∧ (⊢ ⊤), def.
2. ⊢ p a ↔ a = a ∧ (⊢ ⊤), 1.
"),

/*("09.01", ELOGIC, "
1. 1 ⊢ P x, hypo.
2. ⊢ P x → P x, subj_intro 1.
3. ⊢ ∀P. P x → P x, uq_intro 2.
"),*/
// Declarations: `decl name : Type.`; operators must be declared.
("14.01", OK, "
decl element: Ind → Ind → Prop.
1. ⊢ x ∈ A → x ∈ A, axiom.
"),
// Notation without declaration of its constant
("14.02", ETYPE, "
1. ⊢ x ∈ A → x ∈ A, axiom.
"),
("14.03", ELOGIC, "
decl element: Ind → Ind → Prop.
decl element: Ind → Ind → Prop.
"),
// The prelude has declared the logical vocabulary
("14.04", ELOGIC, "
decl conj: Prop → Prop → Prop.
"),
// Names that are keywords for symbols are taken literally after `decl`.
("14.05", OK, "
decl sub: Ind → Ind → Ind.
decl equivalent: Ind → Ind → Prop.
decl product: Ind → Ind → Ind.
1. ⊢ a - b = a × b, axiom.
2. ⊢ a ≡ b → a ≡ b, axiom.
"),
("14.06", ESYNTAX, "
decl f Ind.
"),
("14.07", ESYNTAX, "
decl f: Foo.
"),
("14.08", ESYNTAX, "
decl f: Ind
"),
// Higher-order declaration
("14.09", OK, "
decl F: (Ind → Prop) → Prop.
decl R: Ind → Prop.
1. ⊢ F R → F R, axiom.
"),
// The type of a declaration is binding
("14.10", ETYPE, "
decl c: Ind.
1. ⊢ c → c, axiom.
"),
("14.11", ELOGIC, "
decl element: Ind → Ind → Prop.
decl element: Ind → Ind → Prop.
"),
// A definition may only use declared symbols on its right hand side;
// the notation does not declare anything by itself.
("14.12", ELOGIC, "
decl a: Ind.
decl b: Ind.
c_eq. ⊢ c = a + b, def.
"),
("14.13", OK, "
decl add: Ind → Ind → Ind.
decl a: Ind.
decl b: Ind.
c_eq. ⊢ c = a + b, def.
"),

// Definitions of operator constants: the definition declares the
// constant, its type is inferred from both sides.
("15.01", OK, "
decl element: Ind → Ind → Prop.
incl_equi. ⊢ A ⊆ B ↔ ∀x. x ∈ A → x ∈ B, def.
"),
("15.02", OK, "
decl element: Ind → Ind → Prop.
incl_equi. ⊢ A ⊆ B ↔ ∀x. x ∈ A → x ∈ B, def.
1. ⊢ a ⊆ b ↔ ∀x. x ∈ a → x ∈ b, incl_equi.
"),
// Definition as an equation
("15.03", OK, "
decl add: Ind → Ind → Ind.
mul_def. ⊢ x * y = x + y, def.
"),
// ∈ is not declared: free in the right hand side
("15.04", ELOGIC, "
incl_equi. ⊢ A ⊆ B ↔ ∀x. x ∈ A → x ∈ B, def.
"),
("15.05", ELOGIC, "
decl element: Ind → Ind → Prop.
decl subset: Ind → Ind → Prop.
incl_equi. ⊢ A ⊆ B ↔ ∀x. x ∈ A → x ∈ B, def.
"),
// The prelude has declared conj
("15.06", ELOGIC, "
dummy. ⊢ A ∧ B ↔ B ∧ A, def.
"),
// The inferred type is binding: ⊆ takes individuals.
("15.07", ETYPE, "
decl element: Ind → Ind → Prop.
incl_equi. ⊢ A ⊆ B ↔ ∀x. x ∈ A → x ∈ B, def.
1. ⊢ (C ∧ D) ⊆ E, axiom.
"),

// Macros: notation is sugar for the constant and vice versa.
("16.01", OK, "
decl element: Ind → Ind → Prop.
let A ⊆ B ↔ (∀x. x ∈ A → x ∈ B).
1. 1 ⊢ a ⊆ b, hypo.
2. ⊢ a ⊆ b → ∀x. x ∈ a → x ∈ b, subj_intro 1.
"),
("16.02", OK, "
decl element: Ind → Ind → Prop.
let A ⊆ B ↔ (∀x. x ∈ A → x ∈ B).
1. 1 ⊢ a ⊆ b, hypo.
2. ⊢ subset a b → ∀x. x ∈ a → x ∈ b, subj_intro 1.
"),
("16.03", OK, "
decl element: Ind → Ind → Prop.
let subset A B ↔ (∀x. x ∈ A → x ∈ B).
1. 1 ⊢ a ⊆ b, hypo.
2. ⊢ subset a b → ∀x. x ∈ a → x ∈ b, subj_intro 1.
"),
// Constants and macros share one namespace.
("16.04", ELOGIC, "
decl element: Ind → Ind → Prop.
let A ∈ B ↔ (A = B).
"),
("16.05", ELOGIC, "
let A ∧ B ↔ (B ∧ A).
"),
("16.06", ELOGIC, "
let A ⊆ B ↔ (A = B).
decl subset: Ind → Ind → Prop.
"),
("16.07", ELOGIC, "
decl element: Ind → Ind → Prop.
let A ⊆ B ↔ (∀x. x ∈ A → x ∈ B).
incl_equi. ⊢ A ⊆ B ↔ ∀x. x ∈ A → x ∈ B, def.
"),
("16.08", ELOGIC, "
let A ⊆ B ↔ (A = B).
decl subset: Ind → Ind → Prop.
"),
// After `end` the macro is gone.
("16.09", OK, "
begin
let A ⊆ B ↔ (A = B).
end
decl subset: Ind → Ind → Prop.
"),
// A bound variable does not capture the constant of a notation.
("16.10", OK, "
decl element: Ind → Ind → Prop.
1. ⊢ (∀element. element ∈ A) → (∀element. element ∈ A), axiom.
"),
];

static TYPE_TESTS: &[(&str, &str, &str, &str, fn() -> Type)] = &[
("01.01", "", "A", "A", || Prop),
("01.02", "", "⊢ A", "A", || Prop),
("01.03", "", "H ⊢ A", "H", || Prop),
("01.04", "", "H ⊢ A", "A", || Prop),
("01.05", "", "A ∧ B", "A", || Prop),
("01.06", "", "A ∧ B", "B", || Prop),
("01.07", "", "H ⊢ A ∧ B", "A", || Prop),
("01.08", "", "H ⊢ A ∧ B", "B", || Prop),
("01.09", "", "A ∨ B", "A", || Prop),
("01.10", "", "A ∨ B", "B", || Prop),
("01.11", "", "H ⊢ A ∨ B", "A", || Prop),
("01.12", "", "H ⊢ A ∨ B", "B", || Prop),
("01.13", "", "A → B", "A", || Prop),
("01.14", "", "A → B", "B", || Prop),
("01.15", "", "H ⊢ A → B", "A", || Prop),
("01.16", "", "H ⊢ A → B", "B", || Prop),
("01.17", "", "A ↔ B", "A", || Prop),
("01.18", "", "A ↔ B", "B", || Prop),
("01.19", "", "H ⊢ A ↔ B", "A", || Prop),
("01.20", "", "H ⊢ A ↔ B", "B", || Prop),
("01.21", "", "¬A", "A", || Prop),
("01.21", "", "H ⊢ ¬A", "A", || Prop),

("02.01", "", "x = y", "x", || Ind),
("03.01", "", "P x", "x", || Ind),
("03.02", "", "P x y", "x", || Ind),
("03.03", "", "P x y", "y", || Ind),
("03.04", "", "P x", "P", || fn_type(vec![Ind], Prop)),
("03.05", "", "P x y", "P", || fn_type(vec![Ind, Ind], Prop)),

("04.01", "decl P: Prop → Prop.", "P A", "A", || Prop),
("04.01", "decl P: Prop → Prop.",
    "P A", "P", || fn_type(vec![Prop], Prop)),

// Quantifiers and comprehensions are constants applied to lambdas.
("05.01", "", "∀x. P x", "P", || fn_type(vec![Ind], Prop)),
("05.02", "", "A ∧ ∀x. P x", "A", || Prop),
("05.03", "", "∃x. P x ∧ Q x x", "Q", || fn_type(vec![Ind, Ind], Prop)),
("05.04", SETS_PRELUDE, "x ∈ {y | P y}", "P", || fn_type(vec![Ind], Prop)),

// Nested application of the same symbol
("06.01", "", "f (f x) = f (f x)", "f", || fn_type(vec![Ind], Ind)),
("06.02", "", "f (f x) = f (f x)", "x", || Ind),
// Function as argument, type from the definition
("06.03", "twice_eq. ⊢ twice f x = f (f x), def.",
    "twice g a = g (g a)", "g", || fn_type(vec![Ind], Ind)),
("06.04", "twice_eq. ⊢ twice f x = f (f x), def.",
    "twice g a = g (g a)", "twice",
    || fn_type(vec![fn_type(vec![Ind], Ind), Ind], Ind)),
// Predicate as argument
("06.05", "G_eq. ⊢ G P x ↔ P x, def.", "G Q a", "Q",
    || fn_type(vec![Ind], Prop)),
("06.06", "G_eq. ⊢ G P x ↔ P x, def.", "G Q a", "G",
    || fn_type(vec![fn_type(vec![Ind], Prop), Ind], Prop)),
// A variable has a single type within a formula.
("06.07", "", "f x → f (¬A)", "x", || Prop),

// Type annotations
("07.01", "", "P (x : Prop)", "P", || fn_type(vec![Prop], Prop)),
("07.02", "", "F (P : Ind → Prop)", "F",
    || fn_type(vec![fn_type(vec![Ind], Prop)], Prop)),
("07.03", "", "F (P : Ind → Prop)", "P", || fn_type(vec![Ind], Prop)),
("07.04", "", "(f : Ind → Ind → Ind) x y = z", "f",
    || fn_type(vec![Ind, Ind], Ind)),
("07.05", "decl G: (Ind → Prop) → Prop.", "G Q", "Q",
    || fn_type(vec![Ind], Prop)),
("07.06", "decl G: (Ind → Prop) → Prop.", "G Q", "G",
    || fn_type(vec![fn_type(vec![Ind], Prop)], Prop)),
("07.07", "decl element: Ind → Ind → Prop.\ndecl H: Prop → Prop.",
    "H (x ∈ y)", "H",
    || fn_type(vec![Prop], Prop)),
// Higher-order function whose parameter is only annotated
("07.08", "decl T: (Ind → Ind) → Ind → Ind.  ", "T g a = a",
    "T", || fn_type(vec![fn_type(vec![Ind], Ind), Ind], Ind)),
("07.09", "", "(F : (Ind → Prop) → Ind → Prop) Q a", "F",
    || fn_type(vec![fn_type(vec![Ind], Prop), Ind], Prop)),
("07.10", "", "(F : (Ind → Prop) → Ind → Prop) Q a", "Q",
    || fn_type(vec![Ind], Prop)),
// A → (B → C) is A → B → C
("07.11", "", "(f : Ind → (Ind → Ind)) x y = z", "f",
    || fn_type(vec![Ind, Ind], Ind))
];


// == Unit tests for the individual phases ==

fn parse_expr(src: &str) -> Expr {
    let mut env = Env::new();
    env.tokens = scan(src.as_bytes()).unwrap();
    env.index.set(0);
    parse_formula(&env).unwrap().0
}

// Parses `code` (macro definitions only) and then expands `src`.
fn expand_with(code: &str, src: &str) -> Result<Expr, Error> {
    let mut env = Env::new();
    env.tokens = scan(code.as_bytes())?;
    env.index.set(0);
    for item in parse_items(&env)? {
        if let Item::Let(e, line) = item {
            define_macro(&mut env, line, &e)?;
        }
    }
    env.tokens = scan(src.as_bytes())?;
    env.index.set(0);
    let (e, line) = parse_formula(&env)?;
    expand(&env, line, &e, &[])
}

// For each occurrence of a bound variable, the index of its binder
// counted from the outside (de Bruijn level). This identifies which
// binder is meant, regardless of occurrence depth. A loose index
// (pointing out of the expression) is an error.
fn collect_levels(e: &Expr, depth: usize, acc: &mut Vec<usize>) {
    match e {
        Expr::Bound(i) => {
            assert!(*i < depth, "loose index {} in {}", i, e);
            acc.push(depth - 1 - *i);
        },
        Expr::App(a) => {for x in a {collect_levels(x, depth, acc);}},
        Expr::Lam(b) => collect_levels(b, depth + 1, acc),
        Expr::Ascribe(x, _) => collect_levels(x, depth, acc),
        _ => {}
    }
}

fn levels(e: &Expr) -> Vec<usize> {
    let mut acc = Vec::new();
    collect_levels(e, 0, &mut acc);
    acc
}

fn count_lams(e: &Expr) -> usize {
    match e {
        Expr::App(a) => a.iter().map(count_lams).sum::<usize>(),
        Expr::Lam(b) => 1 + count_lams(b),
        Expr::Ascribe(x, _) => count_lams(x),
        _ => 0
    }
}

#[test]
fn operators_are_desugared() {
    assert_eq!(parse_expr("a + b * c").to_string(), "(add a (mul b c))");
    assert_eq!(parse_expr("A → B → C").to_string(), "(subj A (subj B C))");
    assert_eq!(parse_expr("A ∧ B ∨ C").to_string(), "(disj (conj A B) C)");
    assert_eq!(parse_expr("~A ∧ B").to_string(), "(conj (neg A) B)");
    assert_eq!(parse_expr("⊢ A").to_string(), "(seq verum A)");
    assert_eq!(parse_expr("H ⊢ A").to_string(), "(seq H A)");
    assert_eq!(parse_expr("f x y").to_string(), "(f x y)");
    assert_eq!(parse_expr("{a, b}").to_string(), "(union (sg a) (sg b))");
    assert_eq!(parse_expr("(a, b)").to_string(), "(pair a b)");
}

#[test]
fn parser_resolves_binders() {
    let e = parse_expr("∀x. ∃x. A x ∧ x = y");
    let Expr::App(a) = &e else {panic!()};
    assert_eq!(a[0].to_string(), "uq");
    let Expr::Lam(b1) = &a[1] else {panic!()};
    let Expr::App(b) = &**b1 else {panic!()};
    assert_eq!(b[0].to_string(), "ex");
    assert!(matches!(&b[1], Expr::Lam(_)));
    // Both occurrences of x belong to the inner binder (index 0,
    // level 1); y remains free.
    assert_eq!(levels(&e), vec![1, 1]);
    assert_eq!(e.to_string(),
        "(uq (fn (ex (fn (conj (A $0) (eq $0 y))))))");
}

#[test]
fn bound_variable_scope_ends_with_the_body() {
    let e = parse_expr("(∀x. A x) ∧ B x");
    assert_eq!(levels(&e), vec![0]);
    assert!(e.to_string().ends_with("(B x))"), "{}", e);
}

#[test]
fn indices_count_binders_from_the_inside() {
    let e = parse_expr("∀x. ∀y. x = y");
    assert_eq!(e.to_string(), "(uq (fn (uq (fn (eq $1 $0)))))");
    assert_eq!(levels(&e), vec![0, 1]);
}

#[test]
fn comprehension_binder_may_shadow() {
    let e = parse_expr("∀x. {x | x ∈ A}");
    assert_eq!(count_lams(&e), 2);
    assert_eq!(levels(&e), vec![1]);
}

#[test]
fn macro_copies_are_independent() {
    let e = expand_with("let S a ↔ (∀y. P a y).", "S x ∧ S z").unwrap();
    assert_eq!(count_lams(&e), 2);
    assert_eq!(levels(&e), vec![0, 0]);
    let s = e.to_string();
    assert_eq!(s.matches("(P x $0)").count(), 1, "{}", s);
    assert_eq!(s.matches("(P z $0)").count(), 1, "{}", s);
}

#[test]
fn nested_macro_calls_keep_binders_apart() {
    let e = expand_with("let Q p ↔ (∀y. p ∨ R y).", "Q (Q A)").unwrap();
    // Both binders carry index 0, but refer to different lambdas:
    // level 1 inside, level 0 outside.
    assert_eq!(e.to_string(),
        "(uq (fn (disj (uq (fn (disj A (R $0)))) (R $0))))");
    assert_eq!(levels(&e), vec![1, 0]);
}

#[test]
fn free_names_of_macro_body_are_not_captured() {
    // The free x in the body must not be captured by ∀x at the
    // call site.
    let e = expand_with("let M ↔ x ∈ A.", "∀x. M").unwrap();
    assert!(levels(&e).is_empty(), "{}", e);
    assert!(e.to_string().contains("(element x A)"), "{}", e);
}

#[test]
fn macro_arguments_may_contain_bound_variables_of_the_call_site() {
    let e = expand_with("let S a ↔ (a = a).", "∀z. S z").unwrap();
    assert_eq!(e.to_string(), "(uq (fn (eq $0 $0)))");
    assert_eq!(levels(&e), vec![0, 0]);
}

#[test]
fn macro_arguments_are_shifted_below_binders_of_the_body() {
    // Argument z has index 0 at the call site. Under binder y of
    // the body, it must become 1; y itself has 0. Without shifting,
    // y would capture z: ∀z. ∀y. y = y.
    let e = expand_with("let T a ↔ (∀y. y = a).", "∀z. T z").unwrap();
    assert_eq!(e.to_string(), "(uq (fn (uq (fn (eq $0 $1)))))");
    assert_eq!(levels(&e), vec![1, 0]);
}

#[test]
fn shifting_leaves_indices_of_inner_binders_alone() {
    // The argument is itself a quantifier with its own binder
    // (index 0) and a reference to z (level 0, here index 1):
    // only the reference shifts.
    let e = expand_with("let T a ↔ (∀y. a ∨ y = y).", "∀z. T (∀w. w = z)")
        .unwrap();
    assert_eq!(e.to_string(), concat!(
        "(uq (fn (uq (fn (disj ",
        "(uq (fn (eq $0 $2))) (eq $0 $0))))))"));
    assert_eq!(levels(&e), vec![2, 0, 1, 1]);
}

#[test]
fn macro_parameters_shadow_macros() {
    let e = expand_with("let c ↔ ⊤. let F c ↔ c ∧ c.", "F A").unwrap();
    assert_eq!(e.to_string(), "(conj A A)");
}

#[test]
fn macro_arity_is_checked() {
    let e = expand_with("let S x y ↔ x = y.", "S a").unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Syntax));
    let e = expand_with("let S x y ↔ x = y.", "S").unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Syntax));
    let e = expand_with("let S ↔ x = y.", "S a").unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Syntax));
}

#[test]
fn macros_may_be_defined_and_called_with_notation() {
    let notation = expand_with(
        "let A ⊆ B ↔ (∀x. x ∈ A → x ∈ B).", "a ⊆ b").unwrap().to_string();
    assert_eq!(notation, "(uq (fn (subj (element $0 a) (element $0 b))))");
    // The notation is the constant `subset`, and vice versa
    let ident = expand_with(
        "let subset A B ↔ (∀x. x ∈ A → x ∈ B).", "a ⊆ b").unwrap().to_string();
    assert_eq!(ident, notation);
    let call = expand_with(
        "let A ⊆ B ↔ (∀x. x ∈ A → x ∈ B).", "subset a b").unwrap().to_string();
    assert_eq!(call, notation);
    // Arity is checked for notation as well
    let e = expand_with("let A ⊆ B ↔ A = B.", "subset a").unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Syntax));
}

#[test]
fn defined_name_reads_the_head_of_the_left_side() {
    for (src, expected) in [
        ("A ⊆ B ↔ C", Some("subset")),
        ("c = d", Some("c")),
        ("p ↔ q", Some("p")),
        ("f x y = z", Some("f")),
        ("(f : Ind → Ind) x = y", Some("f")),
        ("A ∧ B", None),
        ("A", None)
    ] {
        let e = parse_expr(src);
        assert_eq!(defined_name(&e).map(|x| x.to_string()),
            expected.map(|s| s.to_string()), "{}", src);
    }
}

#[test]
fn invalid_macro_definitions_are_rejected() {
    for code in ["let A ∧ B.", "let f x x ↔ x.", "let f (x + y) ↔ x.",
        "let f 1 ↔ x."] {
        let e = expand_with(code, "A").unwrap_err();
        assert!(matches!(e.kind, ErrorKind::Syntax), "{}", code);
    }
}

static SETS_PRELUDE: &str = "
decl element: Ind → Ind → Prop.
decl comp: (Ind → Prop) → Ind.
";

#[test]
fn quantifier_is_forall_applied_to_lambda() {
    let mut env = new_env();
    verify(&mut env, SETS_PRELUDE.as_bytes()).unwrap();
    env.tokens = scan("∀x. P x".as_bytes()).unwrap();
    env.index.set(0);
    let t = formula_type_checked(&env).unwrap();
    assert!(t.is_quantifier());
    assert!(matches!(t.as_unary("uq"), Some(_)));
    assert!(matches!(&t.arg(1).value, Lambda(_)));
    assert_eq!(t.arg(1).ty, fn_type(vec![Ind], Prop));

    env.tokens = scan("{x | P x}".as_bytes()).unwrap();
    env.index.set(0);
    let t = formula_type_checked(&env);
    // A set is not a Prop
    assert!(matches!(t.unwrap_err().kind, ErrorKind::Type));
    env.tokens = scan("y ∈ {x | P x}".as_bytes()).unwrap();
    env.index.set(0);
    let t = formula_type_checked(&env).unwrap();
    assert!(matches!(t.as_binary("element"), Some(_)));
    assert!(matches!(t.arg(2).as_unary("comp"), Some(_)));
    assert_eq!(t.arg(2).ty, Ind);
}

#[test]
fn no_type_variables_survive() {
    fn has_var(ty: &Type) -> bool {
        match ty {
            Type::Var(_) => true,
            Type::Fn(f) => f.argv.iter().any(has_var) || has_var(&f.value),
            _ => false
        }
    }
    fn check(t: &Term) {
        assert!(!has_var(&t.ty), "{}", t);
        match &t.value {
            App(a) => {for x in a.iter() {check(x);}},
            Lambda(a) => check(a),
            _ => {}
        }
    }
    let mut env = new_env();
    for src in ["f (g x) = h y", "∀x. ∃y. P x y ∨ Q", "twice f x ↔ f (f x)"] {
        env.tokens = scan(src.as_bytes()).unwrap();
        env.index.set(0);
        check(&formula_type_checked(&env).unwrap());
    }
}

#[test]
fn format_source_code_basics() {
    use crate::fmt::format_source_code;
    let f = |s: &str| String::from_utf8(format_source_code(s.as_bytes())).unwrap();
    assert_eq!(f("A /\\ B -> C"), "A ∧ B → C");
    assert_eq!(f("forall x. A x"), "∀x. A x");
    assert_eq!(f("not A"), "¬A");
    assert_eq!(f("A # comment\nB"), "A # comment\nB");
}

#[test]
fn format_source_code_unterminated_comments_do_not_panic() {
    use crate::fmt::format_source_code;
    let f = |s: &str| String::from_utf8(format_source_code(s.as_bytes())).unwrap();
    assert_eq!(f("A # comment"), "A # comment");
    assert_eq!(f("A (* x"), "A (* x");
    assert_eq!(f("A (* x *) B"), "A (* x *) B");
}


// == Type annotations ==

fn parse_ty(src: &str) -> Result<Type, Error> {
    let mut env = Env::new();
    env.tokens = scan(format!("(x : {})", src).as_bytes())?;
    env.index.set(0);
    match parse_formula(&env)?.0 {
        Expr::Ascribe(_, ty) => Ok(ty),
        e => panic!("not an annotation: {}", e)
    }
}

#[test]
fn type_annotations_parse() {
    assert_eq!(parse_ty("Prop").unwrap(), Prop);
    assert_eq!(parse_ty("Ind").unwrap(), Ind);
    assert_eq!(parse_ty("(Ind)").unwrap(), Ind);
    assert_eq!(parse_ty("Ind → Prop").unwrap(), fn_type(vec![Ind], Prop));
    assert_eq!(parse_ty("(Ind → Prop)").unwrap(), fn_type(vec![Ind], Prop));
    assert_eq!(parse_ty("Ind → Ind → Ind").unwrap(),
        fn_type(vec![Ind, Ind], Ind));
    assert_eq!(parse_ty("Ind → Ind → Ind → Prop").unwrap(),
        fn_type(vec![Ind, Ind, Ind], Prop));
    assert_eq!(parse_ty("(Ind → Prop) → Prop").unwrap(),
        fn_type(vec![fn_type(vec![Ind], Prop)], Prop));
    assert_eq!(parse_ty("(Ind → Prop) → Ind → Prop").unwrap(),
        fn_type(vec![fn_type(vec![Ind], Prop), Ind], Prop));
}

// → is right-associative, and a function type as return value is
// the same multi-argument function; only a function type as argument
// remains nested.
#[test]
fn arrow_is_right_associative_and_flattens_the_value() {
    assert_eq!(parse_ty("Ind → (Ind → Prop)").unwrap(),
        parse_ty("Ind → Ind → Prop").unwrap());
    assert_eq!(parse_ty("(Ind → Prop) → (Ind → Prop)").unwrap(),
        parse_ty("(Ind → Prop) → Ind → Prop").unwrap());
    assert_ne!(parse_ty("(Ind → Ind) → Ind").unwrap(),
        parse_ty("Ind → Ind → Ind").unwrap());
    assert_ne!(parse_ty("Ind → Ind → Prop").unwrap(),
        parse_ty("Ind → Prop").unwrap());
}

#[test]
fn malformed_type_annotations_are_syntax_errors() {
    for src in ["Foo", "(Ind, Ind)", "(Ind, Ind) → Ind", "→ Prop", "Ind →",
        "(Ind", "()", "Ind → → Prop", "Ind → Foo → Prop"]
    {
        let e = parse_ty(src).unwrap_err();
        assert!(matches!(e.kind, ErrorKind::Syntax), "{}", src);
    }
}

// The old syntax is no longer accepted; the message suggests the
// new one.
#[test]
fn tuple_syntax_for_function_types_gets_a_hint() {
    let e = parse_ty("(Ind, Ind) → Ind").unwrap_err();
    assert!(e.info.contains("A → B → C"), "{}", e.info);
}

#[test]
fn types_are_displayed_in_curried_notation() {
    for (src, shown) in [
        ("Prop", "Prop"),
        ("Ind → Prop", "Ind → Prop"),
        ("Ind → Ind → Prop", "Ind → Ind → Prop"),
        ("Ind → (Ind → Prop)", "Ind → Ind → Prop"),
        ("(Ind → Prop) → Prop", "(Ind → Prop) → Prop"),
        ("(Ind → Ind) → Ind → Ind", "(Ind → Ind) → Ind → Ind"),
        ("(Ind → Prop) → (Ind → Prop)", "(Ind → Prop) → Ind → Prop")]
    {
        let ty = parse_ty(src).unwrap();
        assert_eq!(ty.to_string(), shown);
        assert_eq!(parse_ty(shown).unwrap(), ty, "{}", src);
    }
    // A function return type (only possible via inference)
    // remains recognizable.
    let nested = fn_type(vec![Ind], fn_type(vec![Ind], Prop));
    assert_eq!(nested.to_string(), "Ind → (Ind → Prop)");
}

#[test]
fn annotation_is_part_of_the_expression() {
    assert_eq!(parse_expr("(x : Ind) = y").to_string(), "(eq (x : Ind) y)");
    assert_eq!(parse_expr("(f : Ind → Ind) x").to_string(),
        "((f : Ind → Ind) x)");
    // Bound variables may be annotated
    let e = parse_expr("∀x. (x : Ind) = x");
    assert_eq!(levels(&e).len(), 2);
}

#[test]
fn macro_expansion_descends_into_annotations() {
    let e = expand_with("let S a ↔ ((a : Ind) = a).", "S z").unwrap();
    assert_eq!(e.to_string(), "(eq (z : Ind) z)");
    // Binders and arguments are handled correctly under
    // annotations as well.
    let e = expand_with("let T a ↔ ∀y. ((y : Ind) = a).", "T x ∧ T x").unwrap();
    assert_eq!(count_lams(&e), 2);
    assert_eq!(levels(&e), vec![0, 0]);
    assert_eq!(e.to_string().matches("(eq ($0 : Ind) x)").count(), 2, "{}", e);
}


// == Internal functions: equality, matching, abstraction ==

const DECLS: &str = "
decl R: Ind → Prop.
decl S: Ind → Prop.
decl g: Ind → Ind.
decl nec: Prop → Prop.
decl pos: Prop → Prop.
";

fn env_with(code: &str) -> Env {
    let mut env = new_env();
    let Ok(_) = verify(&mut env, code.as_bytes()) else {panic!("setup failed")};
    env
}

fn term_in(env: &mut Env, src: &str) -> Term {
    env.tokens = scan(src.as_bytes()).unwrap();
    env.index.set(0);
    formula_type_checked(env).unwrap()
}

// Term of type Ind (formula_type_checked requires a formula).
fn ind_in(env: &mut Env, src: &str) -> Term {
    term_in(env, &format!("{} = {}", src, src)).arg(1).clone()
}

fn unify_src(env: &mut Env, t: &str, pat: &str) -> (bool, Subs) {
    let t = term_in(env, t);
    let p = pattern_from(&term_in(env, pat));
    let mut subs = Subs::new();
    let ok = unify(env, 0, &t, &p, &mut subs);
    (ok, subs)
}

fn bound_to_term(subs: &Subs, name: &str) -> Option<String> {
    match subs.get(&Bstr::from(name)) {
        Some(Binding::Term(t)) => Some(t.to_string()),
        _ => None
    }
}

#[test]
fn term_eq_is_alpha_equivalence() {
    let mut env = env_with(DECLS);
    verify(&mut env, SETS_PRELUDE.as_bytes()).unwrap();
    let mut eq = |a: &str, b: &str| {
        let x = term_in(&mut env, a);
        let y = term_in(&mut env, b);
        term_eq(&x, &y)
    };
    assert!(eq("∀x. R x", "∀y. R y"));
    assert!(!eq("∀x. R x", "∀x. S x"));
    assert!(eq("∀x. ∀y. R x ∧ S y", "∀a. ∀b. R a ∧ S b"));
    assert!(!eq("∀x. ∀y. R x ∧ S y", "∀a. ∀b. R b ∧ S a"));
    assert!(!eq("∀x. R x", "∃x. R x"));
    assert!(!eq("∀x. R x", "R x"));
    assert!(eq("{x | R x} = {y | R y}", "{z | R z} = {z | R z}"));
}

#[test]
fn alpha_equivalent_terms_are_identical() {
    let mut env = env_with(DECLS);
    let x = term_in(&mut env, "∀x. ∃y. R x ∧ S y");
    let y = term_in(&mut env, "∀a. ∃b. R a ∧ S b");
    assert!(x == y);
    assert_eq!(x.to_string(), y.to_string());
}

#[test]
fn unify_binds_and_checks_consistency() {
    let mut env = env_with(DECLS);
    let (ok, subs) = unify_src(&mut env, "R a ∧ S b", "R x ∧ S y");
    assert!(ok);
    assert_eq!(bound_to_term(&subs, "x").as_deref(), Some("a"));
    assert_eq!(bound_to_term(&subs, "y").as_deref(), Some("b"));
    assert!(!unify_src(&mut env, "R a ∧ S b", "R x ∧ S x").0);
    assert!(unify_src(&mut env, "R a ∧ S a", "R x ∧ S x").0);
    assert!(!unify_src(&mut env, "R a", "S a").0);
    assert!(!unify_src(&mut env, "R a ∧ S a", "R a ∨ S a").0);
}

#[test]
fn unify_pred_miller_pattern_abstracts_bound_variable() {
    let mut env = env_with(DECLS);
    let (ok, subs) = unify_src(&mut env, "∀x. R x ∧ S (g x)", "∀x. P x");
    assert!(ok);
    let Some(Binding::Abs(s)) = subs.get(&Bstr::from("P")) else {panic!()};
    assert_eq!(s.args.len(), 1);
    let a = ind_in(&mut env, "g c");
    let r = s.call(&[a]);
    let expected = term_in(&mut env, "R (g c) ∧ S (g (g c))");
    assert!(term_eq(&r, &expected));
}

#[test]
fn unify_pred_abstracts_occurrences_of_known_terms() {
    let mut env = env_with(DECLS);
    let t = term_in(&mut env, "R (g a) ∧ S a");
    let p = pattern_from(&term_in(&mut env, "P x"));
    let mut subs = Subs::new();
    subs.set(Bstr::from("x"), Binding::Term(ind_in(&mut env, "a")));
    assert!(unify(&env, 0, &t, &p, &mut subs));
    let Some(Binding::Abs(s)) = subs.get(&Bstr::from("P")) else {panic!()};
    let b = ind_in(&mut env, "b");
    let r = s.call(&[b]);
    let expected = term_in(&mut env, "R (g b) ∧ S b");
    assert!(term_eq(&r, &expected));
}

#[test]
fn replace_terms_abstracts_compound_formals() {
    let mut env = env_with(DECLS);
    let t = term_in(&mut env, "R (g a) ∧ S (g a) ∧ S a");
    let formal = ind_in(&mut env, "g a");
    let arg = ind_in(&mut env, "c");
    let r = replace_terms(&t, &[formal], &[arg]);
    let expected = term_in(&mut env, "R c ∧ S c ∧ S a");
    assert!(term_eq(&r, &expected));
}

#[test]
fn unify_pred_imitates_when_arguments_are_unknown() {
    let mut env = env_with(DECLS);
    let (ok, subs) = unify_src(&mut env, "R (g a)", "F x");
    assert!(ok);
    assert_eq!(bound_to_term(&subs, "F").as_deref(), Some("R"));
    assert_eq!(bound_to_term(&subs, "x").as_deref(), Some("(g a)"));
}

#[test]
fn unify_pred_falls_back_to_constant_abstraction() {
    let mut env = env_with(DECLS);
    let (ok, subs) = unify_src(&mut env, "A", "F x");
    assert!(ok);
    let Some(Binding::Abs(s)) = subs.get(&Bstr::from("F")) else {panic!()};
    let b = ind_in(&mut env, "b");
    let r = s.call(&[b]);
    let expected = term_in(&mut env, "A");
    assert!(term_eq(&r, &expected));
}

#[test]
fn unify_pred_applies_a_head_bound_to_a_symbol() {
    let mut env = env_with(DECLS);
    let r = term_in(&mut env, "R a").arg(0).clone();
    let p = pattern_from(&term_in(&mut env, "F x"));
    let t = term_in(&mut env, "R (g a)");
    let mut subs = Subs::new();
    subs.set(Bstr::from("F"), Binding::Term(r.clone()));
    assert!(unify(&env, 0, &t, &p, &mut subs));
    assert_eq!(bound_to_term(&subs, "x").as_deref(), Some("(g a)"));
    // A different symbol does not match
    let t2 = term_in(&mut env, "S (g a)");
    let mut subs2 = Subs::new();
    subs2.set(Bstr::from("F"), Binding::Term(r));
    assert!(!unify(&env, 0, &t2, &p, &mut subs2));
}

#[test]
fn abstraction_is_eta_equal_to_its_symbol() {
    let mut env = env_with(DECLS);
    let (ok, subs) = unify_src(&mut env, "∀x. R x", "∀x. P x");
    assert!(ok);
    let r = term_in(&mut env, "R a").arg(0).clone();
    let s = term_in(&mut env, "S a").arg(0).clone();
    let pv = pattern_from(term_in(&mut env, "P a").arg(0));
    let mut subs1 = subs.clone();
    assert!(unify(&env, 0, &r, &pv, &mut subs1));
    let mut subs2 = subs.clone();
    assert!(!unify(&env, 0, &s, &pv, &mut subs2));
}

#[test]
fn free_in_looks_into_abstractions() {
    let mut env = env_with(DECLS);
    let (ok, subs) = unify_src(&mut env, "∀z. z = u", "∀z. P z");
    assert!(ok);
    let pat = pattern_from(&term_in(&mut env, "∀z. P z"));
    let u = ind_in(&mut env, "u");
    let v = ind_in(&mut env, "v");
    assert!(free_in(&env, &u, &pat, &subs));
    assert!(!free_in(&env, &v, &pat, &subs));
}

#[test]
fn free_in_ignores_the_formal_parameters_of_an_abstraction() {
    let mut env = env_with(DECLS);
    let t = term_in(&mut env, "R u ∧ S w");
    let p = pattern_from(&term_in(&mut env, "P x"));
    let mut subs = Subs::new();
    subs.set(Bstr::from("x"), Binding::Term(ind_in(&mut env, "u")));
    assert!(unify(&env, 0, &t, &p, &mut subs));
    // P is λz. R z ∧ S w
    let pv = pattern_from(term_in(&mut env, "P a").arg(0));
    let u = ind_in(&mut env, "u");
    let w = ind_in(&mut env, "w");
    assert!(!free_in(&env, &u, &pv, &subs));
    assert!(free_in(&env, &w, &pv, &subs));
}

#[test]
fn subs_rec_reduces_applications_of_abstractions() {
    let mut env = env_with(DECLS);
    let (ok, mut subs) = unify_src(&mut env, "∀x. R x ∧ S x", "∀x. P x");
    assert!(ok);
    let p = pattern_from(&term_in(&mut env, "P c"));
    subs.set(Bstr::from("c"), Binding::Term(ind_in(&mut env, "d")));
    let r = subs_rec(&p, &subs);
    let expected = term_in(&mut env, "R d ∧ S d");
    assert!(term_eq(&r, &expected));
}

#[test]
fn type_error_messages_are_specific() {
    let mut env = env_with(DECLS);
    env.tokens = scan("R a b".as_bytes()).unwrap();
    env.index.set(0);
    let e = formula_type_checked(&env).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Type));
    assert!(e.info.contains("R expects 1 argument(s), but got 2"), "{}", e.info);

    env.tokens = scan("R (A ∧ B)".as_bytes()).unwrap();
    env.index.set(0);
    let e = formula_type_checked(&env).unwrap_err();
    assert!(matches!(e.kind, ErrorKind::Type));
    assert!(e.info.contains("Prop") && e.info.contains("Ind"), "{}", e.info);
}

#[test]
fn replace_terms_does_not_enter_sequents() {
    let mut env = env_with(DECLS);
    let t = term_in(&mut env, "R x ∧ (⊢ S x) ∧ □(S x) ∧ ◇(S x)");
    let formal = ind_in(&mut env, "x");
    let arg = ind_in(&mut env, "c");
    let r = replace_terms(&t, &[formal], &[arg]);
    // In the sequent, x is bound; under □ and ◇ (nec, pos) it
    // remains free.
    let expected = term_in(&mut env, "R c ∧ (⊢ S x) ∧ □(S c) ∧ ◇(S c)");
    assert!(term_eq(&r, &expected));
}

#[test]
fn abstraction_does_not_reach_into_sequents() {
    let mut env = env_with(DECLS);
    let t = term_in(&mut env, "(⊢ R a) ∧ S a");
    let p = pattern_from(&term_in(&mut env, "P x"));
    let mut subs = Subs::new();
    subs.set(Bstr::from("x"), Binding::Term(ind_in(&mut env, "a")));
    assert!(unify(&env, 0, &t, &p, &mut subs));
    let Some(Binding::Abs(s)) = subs.get(&Bstr::from("P")) else {panic!()};
    let b = ind_in(&mut env, "b");
    let r = s.call(&[b]);
    // P is λz. (⊢ R a) ∧ S z; the a inside the sequent remains
    // untouched.
    let expected = term_in(&mut env, "(⊢ R a) ∧ S b");
    assert!(term_eq(&r, &expected));
}

#[test]
fn replace_terms_shifts_arguments_below_binders() {
    let mut env = env_with(DECLS);
    // ∀y. u = y, with loose variable 0 for u
    let t = term_in(&mut env, "∀y. u = y");
    let formal = ind_in(&mut env, "u");
    let arg = term(BoundVar(0), Ind);
    let r = replace_terms(&t, &[formal], &[arg]);
    // Under binder y, 0 becomes 1: the body of ∀z. ∀y. z = y.
    let outer = term_in(&mut env, "∀z. ∀y. z = y");
    let Lambda(body) = &outer.arg(1).value else {panic!()};
    assert!(term_eq(&r, body));
}

#[test]
fn subs_rec_does_not_capture_when_instantiating_under_binders() {
    let mut env = env_with(DECLS);
    // P is λu. ∀y. u = y; the instance of ∀x. P x under binder x
    // must be ∀x. ∀y. x = y and not ∀x. ∀y. y = y.
    let (ok, subs) = unify_src(&mut env, "∀x. ∀y. x = y", "∀x. P x");
    assert!(ok);
    let p = pattern_from(&term_in(&mut env, "∀x. P x"));
    let r = subs_rec(&p, &subs);
    let expected = term_in(&mut env, "∀x. ∀y. x = y");
    assert!(term_eq(&r, &expected));
    let wrong = term_in(&mut env, "∀x. ∀y. y = y");
    assert!(!term_eq(&r, &wrong));
}

#[test]
fn unify_compares_bodies_of_nested_binders() {
    let mut env = env_with(DECLS);
    assert!(unify_src(&mut env, "∀x. ∃y. x = y", "∀a. ∃b. a = b").0);
    assert!(!unify_src(&mut env, "∀x. ∃y. x = y", "∀a. ∃b. b = a").0);
    // x does not occur in the body: P's value must not depend on it
    let (ok, subs) = unify_src(&mut env, "∀x. R c", "∀x. P x");
    assert!(ok);
    let Some(Binding::Abs(s)) = subs.get(&Bstr::from("P")) else {panic!()};
    let d = ind_in(&mut env, "d");
    let r = s.call(&[d]);
    let expected = term_in(&mut env, "R c");
    assert!(term_eq(&r, &expected));
}

// Scope condition: A pattern variable that occurs only in a premise
// under a binder must not be bound to the opened variable. Otherwise,
// ∀y. S y y would yield the theorem ∃z. ∀y. S z y.
#[test]
fn pattern_variable_must_not_capture_an_opened_binder() {
    run_list(&[
("S.01", ELOGIC, "
bad. (H ⊢ ∀y. R x y) → (H ⊢ ∃z. ∀y. R z y), axiom.
1. ⊢ ∀y. S y y, axiom.
2. ⊢ ∃z. ∀y. S z y, bad 1.
"),
// With a term that does not contain the binder, the rule applies.
("S.02", OK, "
bad. (H ⊢ ∀y. R x y) → (H ⊢ ∃z. ∀y. R z y), axiom.
1. ⊢ ∀y. S c y, axiom.
2. ⊢ ∃z. ∀y. S z y, bad 1.
"),
]);
}

#[test]
fn unify_rejects_bindings_that_contain_an_opened_binder() {
    let mut env = env_with(DECLS);
    // x is outside ∀y and must not depend on y
    assert!(!unify_src(&mut env, "∀y. y = y", "∀y. x = y").0);
    let (ok, subs) = unify_src(&mut env, "∀y. c = y", "∀y. x = y");
    assert!(ok);
    assert_eq!(bound_to_term(&subs, "x"), Some("c".to_string()));
    // Imitation: g y contains y, x cannot take it, but F y can
    assert!(!unify_src(&mut env, "∀y. R (g y)", "∀y. R x").0);
    assert!(unify_src(&mut env, "∀y. R (g y)", "∀y. R (F y)").0);
}

#[test]
fn abstraction_may_only_contain_its_own_formals() {
    let mut env = env_with(DECLS);
    // P y would have to contain outer binder x: not a pattern
    assert!(!unify_src(&mut env, "∀x. ∀y. x = y", "∀x. ∀y. P y").0);
    // Q x y may abstract both
    assert!(unify_src(&mut env, "∀x. ∀y. x = y", "∀x. ∀y. Q x y").0);
    // An abstraction over the inner binder alone is possible if the
    // outer one does not occur
    assert!(unify_src(&mut env, "∀x. ∀y. y = y", "∀x. ∀y. W y").0);
}
