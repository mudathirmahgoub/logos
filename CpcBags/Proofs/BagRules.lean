module


public import CpcBags.Proofs.BagMaps
import all CpcBags.Proofs.BagMaps

/-!
# Soundness of the bag rules of cvc5 in the Logos semantics of bags

The semantics of bags is the one of `install/defs/bags/smt.eos`, compiled by
the Eunoia compiler into `CpcBags.SmtModel`: a bag is a map from elements to
their multiplicities, which are positive numerals, and it maps everything else
to zero.

Each theorem below says that the conclusion of a rule of
`proofs/eo/cpc/expert/rules/Bags.eo` (cvc5), translated to the SMT-LIB terms
of the embedding, evaluates to true in every model, given that the bag terms
it mentions evaluate to bag values (`IsBag`). That hypothesis is what type
preservation gives for a well-typed term in a well-formed model; every
canonical bag value satisfies it, see `isBag_of_canonical`.

The translation is pointwise. Each n-ary `and` and `or` of the rule keeps its
terminator `true` and `false`, and each `+` drops its terminator `0`, which is
why the conclusions below are written the way they are.

What is not stated here is the step from these theorems to the per-rule
obligations `cmd_step_<rule>_properties` of the checker (see CpcBags/README.md), which are
stated over the deep embedding of Eunoia terms and need the infrastructure of
`Cpc/Proofs` (translation and type preservation) for the bag constructors.
-/

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm
namespace Bags

open SmtEval

/-- A bag value: a map to numerals whose default is zero. -/
def IsBag (v : SmtValue) : Prop :=
  ∃ m, v = SmtValue.Bag m ∧ __smtx_map_get_default m = SmtValue.Numeral 0 ∧
    __smtx_bag_counts_pos m = true

/-- Every canonical bag value is a bag value. -/
theorem isBag_of_canonical (uc : SmtUSortDom) (m : SmtMap)
    (h : __smtx_value_canonical uc (SmtValue.Bag m) = true) : IsBag (SmtValue.Bag m) := by
  simp [__smtx_value_canonical, native_and, native_veq] at h
  exact ⟨m, rfl, h.2.1, h.2.2⟩

/-- The multiplicity of every element of a bag value is a non-negative numeral. -/
theorem lookup_numeral : ∀ (m : SmtMap), __smtx_map_get_default m = SmtValue.Numeral 0 →
    __smtx_bag_counts_pos m = true →
    ∀ i, ∃ n, __smtx_map_lookup m i = SmtValue.Numeral n ∧ 0 ≤ n
  | .cons j e m, hd, hp, i => by
      rw [get_default_cons] at hd
      cases e with
      | Numeral n =>
          simp only [__smtx_bag_counts_pos, native_and, native_zlt, Bool.and_eq_true,
            decide_eq_true_eq] at hp
          rw [lookup_cons]
          by_cases hji : j = i
          · rw [ite_t hji]; exact ⟨n, rfl, Int.le_of_lt hp.1⟩
          · rw [ite_f hji]; exact lookup_numeral m hd hp.2 i
      | _ => simp [__smtx_bag_counts_pos] at hp
  | .default T d, hd, _, i => by
      simp [__smtx_map_get_default] at hd
      exact ⟨0, by simp [lookup_default, hd], Int.le_refl 0⟩

/-- The multiplicity of an element in a bag value, as a numeral. -/
theorem count_numeral {v : SmtValue} (hv : IsBag v) (i : SmtValue) :
    ∃ n, __smtx_bag_count i v = SmtValue.Numeral n ∧ 0 ≤ n := by
  obtain ⟨m, rfl, hd, hp⟩ := hv
  simpa [__smtx_bag_count] using lookup_numeral m hd hp i

theorem eval_eq_of_not_reglan {v w : SmtValue} (hv : ∀ r, v ≠ SmtValue.RegLan r) :
    __smtx_model_eval_eq v w = SmtValue.Boolean (decide (v = w)) := by
  cases v <;> simp_all [__smtx_model_eval_eq, native_veq]

theorem eval_eq_numeral (a b : native_Int) :
    __smtx_model_eval_eq (SmtValue.Numeral a) (SmtValue.Numeral b) =
      SmtValue.Boolean (decide (a = b)) := by
  simp [__smtx_model_eval_eq, native_veq]

/-- The multiplicity of `i` in the result of operator `k`, from its
multiplicities `c1` and `c2` in the operands. -/
theorem count_bag_op (k : native_Int) {a b : SmtValue} (ha : IsBag a) (hb : IsBag b)
    (i : SmtValue) {c1 c2 : native_Int}
    (h1 : __smtx_bag_count i a = SmtValue.Numeral c1)
    (h2 : __smtx_bag_count i b = SmtValue.Numeral c2) :
    __smtx_bag_count i (__smtx_bag_op k a b) =
      SmtValue.Numeral (__smtx_bag_combine k c1 c2) := by
  obtain ⟨m1, rfl, hd1, _⟩ := ha
  obtain ⟨m2, rfl, hd2, _⟩ := hb
  simp only [__smtx_bag_count] at h1 h2
  rw [lookup_bag_op k hd1 hd2 i]
  simp [combineAt, h1, h2, __smtx_bag_mult]

/-! ## BAGS_COUNT_NON_NEG -/

/-- `(>= (bag.count e a) 0)` -/
theorem bags_count_non_neg (M : SmtModel) (e a : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) :
    __smtx_model_eval M (SmtTerm.geq (SmtTerm.bag_count e a) (SmtTerm.Numeral 0)) =
      SmtValue.Boolean true := by
  obtain ⟨n, hn, h0⟩ := count_numeral ha (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_bag_count, hn,
    __smtx_model_eval_leq, native_zleq]
  simp [h0]

/-! ## BAGS_COUNT_DEF -/

/-- `(= (bag.count e (as bag.empty (Bag T))) 0)` -/
theorem bags_count_def_empty (M : SmtModel) (e : SmtTerm) (T : SmtType) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_empty T)) (SmtTerm.Numeral 0)) =
      SmtValue.Boolean true := by
  simp [__smtx_model_eval, __smtx_model_eval_bag_count, __smtx_bag_count, lookup_default,
    eval_eq_numeral]

/-- `(= (bag.count e (bag x c)) (ite (and (= e x) (>= c 1)) c 0))`, where the
element `e` is not a regular language, which no bag holds. -/
theorem bags_count_def_bag (M : SmtModel) (e x c : SmtTerm) {n : Int}
    (hc : __smtx_model_eval M c = SmtValue.Numeral n)
    (he : ∀ r, __smtx_model_eval M e ≠ SmtValue.RegLan r) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag x c))
          (SmtTerm.ite
            (SmtTerm.and (SmtTerm.eq e x)
              (SmtTerm.and (SmtTerm.geq c (SmtTerm.Numeral 1)) (SmtTerm.Boolean true)))
            c (SmtTerm.Numeral 0))) =
      SmtValue.Boolean true := by
  generalize hve : __smtx_model_eval M e = ve at he
  generalize hvx : __smtx_model_eval M x = vx
  simp only [__smtx_model_eval, hve, hvx, hc, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag, __smtx_bag_make, __smtx_model_eval_geq, __smtx_model_eval_leq,
    __smtx_model_eval_and, __smtx_model_eval_ite, eval_eq_of_not_reglan he, native_zleq,
    native_zlt, native_ite, native_and]
  by_cases hn : 0 < n
  · have h1 : 1 ≤ n := by omega
    by_cases hx : vx = ve
    · subst hx
      simp [hn, h1, __smtx_bag_count, lookup_cons, eval_eq_numeral]
    · have hx' : ¬ ve = vx := fun h => hx h.symm
      simp [hn, h1, hx, hx', __smtx_bag_count, lookup_cons, lookup_default, eval_eq_numeral]
  · have h1 : ¬ 1 ≤ n := by omega
    by_cases hx : ve = vx <;>
      simp [hn, h1, hx, __smtx_bag_count, lookup_default, eval_eq_numeral]

/-- `(= (bag.count e (bag.union_disjoint a b)) (+ (bag.count e a) (bag.count e b)))` -/
theorem bags_count_def_union_disjoint (M : SmtModel) (e a b : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) (hb : IsBag (__smtx_model_eval M b)) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_union_disjoint a b))
          (SmtTerm.plus (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))) =
      SmtValue.Boolean true := by
  obtain ⟨c1, h1, _⟩ := count_numeral ha (__smtx_model_eval M e)
  obtain ⟨c2, h2, _⟩ := count_numeral hb (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag_union_disjoint, count_bag_op 0 ha hb _ h1 h2, h1, h2,
    __smtx_model_eval_plus, eval_eq_numeral]
  simp [__smtx_bag_combine, native_ite, native_zeq, native_zplus]

/-- `(= (bag.count e (bag.union_max a b))
       (ite (> (bag.count e a) (bag.count e b)) (bag.count e a) (bag.count e b)))` -/
theorem bags_count_def_union_max (M : SmtModel) (e a b : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) (hb : IsBag (__smtx_model_eval M b)) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_union_max a b))
          (SmtTerm.ite (SmtTerm.gt (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))
            (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))) =
      SmtValue.Boolean true := by
  obtain ⟨c1, h1, _⟩ := count_numeral ha (__smtx_model_eval M e)
  obtain ⟨c2, h2, _⟩ := count_numeral hb (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag_union_max, count_bag_op 1 ha hb _ h1 h2, h1, h2,
    __smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_ite]
  by_cases h : c2 < c1 <;>
    simp [h, __smtx_bag_combine, native_ite, native_zeq, native_zlt, eval_eq_numeral]

/-- `(= (bag.count e (bag.inter_min a b))
       (ite (< (bag.count e a) (bag.count e b)) (bag.count e a) (bag.count e b)))` -/
theorem bags_count_def_inter_min (M : SmtModel) (e a b : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) (hb : IsBag (__smtx_model_eval M b)) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_inter_min a b))
          (SmtTerm.ite (SmtTerm.lt (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))
            (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))) =
      SmtValue.Boolean true := by
  obtain ⟨c1, h1, _⟩ := count_numeral ha (__smtx_model_eval M e)
  obtain ⟨c2, h2, _⟩ := count_numeral hb (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag_inter_min, count_bag_op 2 ha hb _ h1 h2, h1, h2,
    __smtx_model_eval_lt, __smtx_model_eval_ite]
  by_cases h : c1 < c2 <;>
    simp [h, __smtx_bag_combine, native_ite, native_zeq, native_zlt, eval_eq_numeral]

/-- `(= (bag.count e (bag.difference_subtract a b))
       (ite (>= (bag.count e a) (bag.count e b))
            (- (bag.count e a) (bag.count e b)) 0))` -/
theorem bags_count_def_difference_subtract (M : SmtModel) (e a b : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) (hb : IsBag (__smtx_model_eval M b)) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_difference_subtract a b))
          (SmtTerm.ite (SmtTerm.geq (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))
            (SmtTerm.neg (SmtTerm.bag_count e a) (SmtTerm.bag_count e b))
            (SmtTerm.Numeral 0))) =
      SmtValue.Boolean true := by
  obtain ⟨c1, h1, _⟩ := count_numeral ha (__smtx_model_eval M e)
  obtain ⟨c2, h2, _⟩ := count_numeral hb (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag_difference_subtract, count_bag_op 3 ha hb _ h1 h2, h1, h2,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
    __smtx_model_eval__]
  by_cases h : c2 ≤ c1 <;>
    simp [h, __smtx_bag_combine, native_ite, native_zeq, native_zleq, native_zplus,
      native_zneg, eval_eq_numeral]

/-- `(= (bag.count e (bag.difference_remove a b))
       (ite (<= (bag.count e b) 0) (bag.count e a) 0))` -/
theorem bags_count_def_difference_remove (M : SmtModel) (e a b : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) (hb : IsBag (__smtx_model_eval M b)) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_difference_remove a b))
          (SmtTerm.ite (SmtTerm.leq (SmtTerm.bag_count e b) (SmtTerm.Numeral 0))
            (SmtTerm.bag_count e a) (SmtTerm.Numeral 0))) =
      SmtValue.Boolean true := by
  obtain ⟨c1, h1, _⟩ := count_numeral ha (__smtx_model_eval M e)
  obtain ⟨c2, h2, _⟩ := count_numeral hb (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag_difference_remove, count_bag_op 4 ha hb _ h1 h2, h1, h2,
    __smtx_model_eval_leq, __smtx_model_eval_ite]
  by_cases h : c2 ≤ 0 <;>
    simp [h, __smtx_bag_combine, native_ite, native_zeq, native_zleq, eval_eq_numeral]

/-- `(= (bag.count e (bag.setof a)) (ite (>= (bag.count e a) 1) 1 0))` -/
theorem bags_count_def_setof (M : SmtModel) (e a : SmtTerm)
    (ha : IsBag (__smtx_model_eval M a)) :
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.bag_count e (SmtTerm.bag_setof a))
          (SmtTerm.ite (SmtTerm.geq (SmtTerm.bag_count e a) (SmtTerm.Numeral 1))
            (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) =
      SmtValue.Boolean true := by
  obtain ⟨c1, h1, _⟩ := count_numeral ha (__smtx_model_eval M e)
  simp only [__smtx_model_eval, __smtx_model_eval_bag_count,
    __smtx_model_eval_bag_setof, count_bag_op 5 ha ha _ h1 h1, h1,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite]
  by_cases h : 1 ≤ c1 <;>
    simp [h, __smtx_bag_combine, native_ite, native_zeq, native_zleq, eval_eq_numeral]

/-! ## BAGS_MAKE_SPLIT -/

/-- `(or (and (not (>= c 1)) (= (bag x c) (as bag.empty (Bag T))))
        (and (>= c 1) (not (= (bag x c) (as bag.empty (Bag T))))))`,
where `T` is the type of `x`. -/
theorem bags_make_split (M : SmtModel) (x c : SmtTerm) (T : SmtType) {n : Int}
    (hc : __smtx_model_eval M c = SmtValue.Numeral n)
    (hx : __smtx_typeof_value (__smtx_model_eval M x) = T) :
    __smtx_model_eval M
        (SmtTerm.or
          (SmtTerm.and (SmtTerm.not (SmtTerm.geq c (SmtTerm.Numeral 1)))
            (SmtTerm.and (SmtTerm.eq (SmtTerm.bag x c) (SmtTerm.bag_empty T))
              (SmtTerm.Boolean true)))
          (SmtTerm.or
            (SmtTerm.and (SmtTerm.geq c (SmtTerm.Numeral 1))
              (SmtTerm.and (SmtTerm.not (SmtTerm.eq (SmtTerm.bag x c) (SmtTerm.bag_empty T)))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean false))) =
      SmtValue.Boolean true := by
  generalize hvx : __smtx_model_eval M x = vx at hx
  subst hx
  simp only [__smtx_model_eval, hvx, hc, __smtx_model_eval_bag, __smtx_bag_make,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_not,
    __smtx_model_eval_and, __smtx_model_eval_or, native_zleq, native_zlt, native_ite]
  by_cases hn : 0 < n
  · have h1 : 1 ≤ n := by omega
    simp [hn, h1, __smtx_model_eval_eq, native_veq, native_and, native_or, native_not]
  · have h1 : ¬ 1 ≤ n := by omega
    simp [hn, h1, __smtx_model_eval_eq, native_veq, native_and, native_or, native_not]

end Bags
end Smtm
