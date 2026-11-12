
use crate::export::export_named;

fn to_str_trimmed(a: &[u8]) -> &str {
    str::from_utf8(a.trim_ascii()).unwrap()
}

static TESTS: &[(&str, &str, &str)] = &[
("1.1", "thm1. |- A → B → A ∧ B, axiom.", "\
1. 1 |- A, hypo.
2. 2 |- B, hypo.
3. 1, 2 |- A ∧ B, conj_intro 1 2.
4. 1 |- B → A ∧ B, subj_intro 3.
thm1. |- A → B → A ∧ B, subj_intro 4."),

("1.2", "thm1. ⊢ A → B → A ∧ B, axiom.", "\
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
4. 1 ⊢ B → A ∧ B, subj_intro 3.
thm1. ⊢ A → B → A ∧ B, subj_intro 4."),

("1.3", "thm1. ⊢ A → B → A ∧ B, axiom.", "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
4. 1 ⊢ B → A ∧ B, subj_intro 3.
thm1. ⊢ A → B → A ∧ B, subj_intro 4."),

("1.4", "eq_refl. ⊢ x = x, axiom.
thm1. ⊢ A → B → A ∧ B, axiom.", "
eq_refl. ⊢ x = x, axiom.
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
4. 1 ⊢ B → A ∧ B, subj_intro 3.
thm1. ⊢ A → B → A ∧ B, subj_intro 4."),

("1.5", "eq_refl. ⊢ x = x, axiom.
thm1. ⊢ A → B → A ∧ B, axiom.", "
eq_refl. ⊢ x = x, axiom.\n
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.\n
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.\n
4. 1 ⊢ B → A ∧ B, subj_intro 3.

thm1. ⊢ A → B → A ∧ B, subj_intro 4."),

("2.1", "let C A B ↔ A ∧ B.
eq_refl. ⊢ x = x, axiom.
thm1. ⊢ A → B → A ∧ B, axiom.", "
let C A B ↔ A ∧ B.
eq_refl. ⊢ x = x, axiom.
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
4. 1 ⊢ B → A ∧ B, subj_intro 3.
thm1. ⊢ A → B → A ∧ B, subj_intro 4."),

("2.2", "eq_refl. ⊢ x = x, axiom.
thm1. ⊢ A → B → A ∧ B, axiom.", "
begin
let C A B ↔ A ∧ B.
eq_refl. ⊢ x = x, axiom.
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
4. 1 ⊢ B → A ∧ B, subj_intro 3.
thm1. ⊢ A → B → A ∧ B, subj_intro 4.
end"),

("3.1", "eq_refl. ⊢ x = x, axiom.
decl f: Ind → Ind.", "
eq_refl. ⊢ x = x, axiom.
decl f: Ind → Ind."),

("3.2", "decl f: Ind → Ind.
eq_refl. ⊢ x = x, axiom.", "
decl f: Ind → Ind.
eq_refl. ⊢ x = x, axiom."),

("3.3", "eq_refl. ⊢ x = x, axiom.
decl f: Ind → Ind.", "
eq_refl. ⊢ x = x, axiom.decl f: Ind → Ind."),

("3.4", "decl f: Ind → Ind.
eq_refl. ⊢ x = x, axiom.", "
decl f: Ind → Ind.eq_refl. ⊢ x = x, axiom."),

("3.5", "eq_refl. ⊢ x = x, axiom.
decl f: Ind → Ind.", "
eq_refl. ⊢ x = x, axiom. decl f: Ind → Ind."),

("3.6", "decl f: Ind → Ind.
eq_refl. ⊢ x = x, axiom.", "
decl f: Ind → Ind. eq_refl. ⊢ x = x, axiom."),

("3.7", "eq_refl. ⊢ x = x, axiom.
decl f: Ind → Ind.", "
eq_refl. ⊢ x = x, axiom.  decl f: Ind → Ind."),

("3.8", "decl f: Ind → Ind.
eq_refl. ⊢ x = x, axiom.", "
decl f: Ind → Ind.  eq_refl. ⊢ x = x, axiom.")
];

#[test]
fn basic() {
    for (test_id, expected, input) in TESTS {
        let result_plain = export_named(input.as_bytes());
        let result = to_str_trimmed(&result_plain);
        assert_eq!(&result, expected, "test {}", test_id);
    }
}