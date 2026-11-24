module


public import CpcBags.Proofs.BagRules
import all CpcBags.Proofs.BagRules

/-!
# BAGS_EXT

Two canonical bags of one type that are different values differ in the
multiplicity of some element, and `map_diff` picks one. The step from the
first to the second is extensionality of canonical maps, `map_ext`: a
canonical map is sorted and stores no entry equal to its default, so it is
determined by its lookups.
-/

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm
namespace Bags

open SmtEval

theorem canonical_cons {uc : SmtUSortDom} {i e : SmtValue} {m : SmtMap}
    (h : __smtx_map_canonical uc (.cons i e m) = true) :
    __smtx_value_canonical uc i = true ∧ __smtx_map_canonical uc m = true ∧
      __smtx_map_entries_ordered_after i m = true ∧ e ≠ __smtx_map_get_default m := by
  simp only [__smtx_map_canonical, native_and, native_not, native_veq, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact ⟨h.1.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem sorted_of_canonical (uc : SmtUSortDom) :
    ∀ (m : SmtMap), __smtx_map_canonical uc m = true → Sorted m
  | .cons i e m, h => by
      obtain ⟨_, hm, hord, _⟩ := canonical_cons h
      have hs := sorted_of_canonical uc m hm
      refine ⟨?_, hs⟩
      intro k hk
      cases m with
      | cons j e' m' =>
          simp only [__smtx_map_entries_ordered_after] at hord
          simp only [keys, List.mem_cons] at hk
          rcases hk with hk | hk
          · subst hk; exact hord
          · exact vcmp_trans (hs.1 k hk) hord
      | default T d => simp [keys] at hk
  | .default T d, _ => trivial

theorem typeof_cons {i e : SmtValue} {m : SmtMap} {T U : SmtType}
    (h : __smtx_typeof_map_value (.cons i e m) = SmtType.Map T U) :
    __smtx_typeof_value i = T ∧ __smtx_typeof_map_value m = SmtType.Map T U := by
  simp only [__smtx_typeof_map_value, native_ite, native_Teq] at h
  by_cases hc : SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
      __smtx_typeof_map_value m
  · simp only [hc, decide_true, ite_true] at h
    rw [h] at hc
    exact ⟨(SmtType.Map.inj hc).1, h⟩
  · simp [hc] at h

/-- The first key of a sorted map comes before the key `i`, so `i` is not one
of its keys. -/
theorem not_mem_keys_of_lt {j e : SmtValue} {m : SmtMap} {i : SmtValue}
    (hs : Sorted (.cons j e m)) (hne : j ≠ i) (hlt : native_vcmp j i = true) :
    i ∉ keys (.cons j e m) := by
  simp only [keys, List.mem_cons, not_or]
  exact ⟨fun h => hne h.symm, not_mem_of_sorted hs (Or.inr hlt)⟩

/-- Extensionality of canonical maps. -/
theorem map_ext (uc : SmtUSortDom) : ∀ (m1 m2 : SmtMap) (T U : SmtType),
    __smtx_map_canonical uc m1 = true → __smtx_map_canonical uc m2 = true →
    __smtx_typeof_map_value m1 = SmtType.Map T U →
    __smtx_typeof_map_value m2 = SmtType.Map T U →
    __smtx_map_get_default m1 = __smtx_map_get_default m2 →
    (∀ i, __smtx_typeof_value i = T → __smtx_value_canonical uc i = true →
      __smtx_map_lookup m1 i = __smtx_map_lookup m2 i) →
    m1 = m2
  | .default T1 d1, .default T2 d2, T, U, _, _, ht1, ht2, hd, _ => by
      simp only [__smtx_typeof_map_value] at ht1 ht2
      simp only [__smtx_map_get_default] at hd
      rw [(SmtType.Map.inj ht1).1, (SmtType.Map.inj ht2).1, hd]
  | .default T1 d1, .cons j e2 r2, T, U, _, hc2, _, ht2, hd, hl => by
      obtain ⟨hcj, _, _, hne⟩ := canonical_cons hc2
      have h := hl j (typeof_cons ht2).1 hcj
      rw [lookup_default, lookup_cons, ite_t rfl] at h
      simp only [__smtx_map_get_default] at hd
      exact (hne (h.symm.trans hd)).elim
  | .cons i e1 r1, .default T2 d2, T, U, hc1, _, ht1, _, hd, hl => by
      obtain ⟨hci, _, _, hne⟩ := canonical_cons hc1
      have h := hl i (typeof_cons ht1).1 hci
      rw [lookup_cons, ite_t rfl, lookup_default] at h
      simp only [__smtx_map_get_default] at hd
      exact (hne (h.trans hd.symm)).elim
  | .cons i e1 r1, .cons j e2 r2, T, U, hc1, hc2, ht1, ht2, hd, hl => by
      have hs1 := sorted_of_canonical uc _ hc1
      have hs2 := sorted_of_canonical uc _ hc2
      obtain ⟨hci, hr1, _, hne1⟩ := canonical_cons hc1
      obtain ⟨hcj, hr2, _, hne2⟩ := canonical_cons hc2
      obtain ⟨hti, htr1⟩ := typeof_cons ht1
      obtain ⟨htj, htr2⟩ := typeof_cons ht2
      rw [get_default_cons, get_default_cons] at hd
      by_cases hij : i = j
      · subst hij
        have he : e1 = e2 := by
          have h := hl i hti hci
          rwa [lookup_cons, ite_t rfl, lookup_cons, ite_t rfl] at h
        subst he
        have hr : r1 = r2 := by
          apply map_ext uc r1 r2 T U hr1 hr2 htr1 htr2 hd
          intro k hkT hkc
          by_cases hik : i = k
          · subst hik
            rw [lookup_not_mem r1 i (not_mem_of_sorted hs1 (Or.inl rfl)),
              lookup_not_mem r2 i (not_mem_of_sorted hs2 (Or.inl rfl)), hd]
          · have h := hl k hkT hkc
            rwa [lookup_cons, ite_f hik, lookup_cons, ite_f hik] at h
        rw [hr]
      · by_cases hv : native_vcmp j i = true
        · -- i comes first, so it is not a key of the second map
          have hni := not_mem_keys_of_lt hs2 (fun h => hij h.symm) hv
          have h := hl i hti hci
          rw [lookup_cons, ite_t rfl, lookup_not_mem _ i hni, get_default_cons] at h
          exact absurd (h.trans hd.symm) hne1
        · -- j comes first, so it is not a key of the first map
          have hv' : native_vcmp i j = true := vcmp_flip (fun h => hij h.symm) (by simpa using hv)
          have hnj := not_mem_keys_of_lt hs1 hij hv'
          have h := hl j htj hcj
          rw [lookup_not_mem _ j hnj, get_default_cons, lookup_cons, ite_t rfl] at h
          exact (hne2 (h.symm.trans hd)).elim

theorem map_of_bag_type {X : SmtType} {T : SmtType}
    (h : __smtx_map_to_bag_type X = SmtType.Bag T) : X = SmtType.Map T SmtType.Int := by
  unfold __smtx_map_to_bag_type at h
  split at h
  · cases h; rfl
  · cases h

/-- `(not (= a b))` implies
`(not (= (bag.count (@bags_deq_diff a b) a) (bag.count (@bags_deq_diff a b) b)))`,
where `@bags_deq_diff` is translated to `map_diff`, for bags `a` and `b` that
evaluate to canonical bags of one type in the model. -/
theorem bags_ext (M : SmtModel) (a b : SmtTerm) {m1 m2 : SmtMap} {T : SmtType}
    (ha : __smtx_model_eval M a = SmtValue.Bag m1)
    (hb : __smtx_model_eval M b = SmtValue.Bag m2)
    (hca : __smtx_value_canonical M.usortDom (SmtValue.Bag m1) = true)
    (hcb : __smtx_value_canonical M.usortDom (SmtValue.Bag m2) = true)
    (hta : __smtx_typeof_value (SmtValue.Bag m1) = SmtType.Bag T)
    (htb : __smtx_typeof_value (SmtValue.Bag m2) = SmtType.Bag T)
    (hne : __smtx_model_eval M (SmtTerm.not (SmtTerm.eq a b)) = SmtValue.Boolean true) :
    __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.eq (SmtTerm.bag_count (SmtTerm.map_diff a b) a)
            (SmtTerm.bag_count (SmtTerm.map_diff a b) b))) =
      SmtValue.Boolean true := by
  simp only [__smtx_typeof_value] at hta htb
  have ht1 := map_of_bag_type hta
  have ht2 := map_of_bag_type htb
  simp only [__smtx_value_canonical, native_and, native_veq, Bool.and_eq_true,
    decide_eq_true_eq] at hca hcb
  -- the two bags are different maps
  have hm : m1 ≠ m2 := by
    intro h
    subst h
    simp [__smtx_model_eval, ha, hb, __smtx_model_eval_eq, __smtx_model_eval_not,
      native_veq, native_not] at hne
  -- so they differ at some typed, canonical element
  have hDiff : ∃ i : SmtValue, __smtx_typeof_value i = T ∧
      __smtx_value_canonical M.usortDom i = true ∧
      native_veq (__smtx_map_lookup m1 i) (__smtx_map_lookup m2 i) = false := by
    apply Classical.byContradiction
    intro hno
    apply hm
    apply map_ext M.usortDom m1 m2 T SmtType.Int hca.1 hcb.1 ht1 ht2
      (hca.2.1.trans hcb.2.1.symm)
    intro i hiT hic
    apply Classical.byContradiction
    intro hl
    exact hno ⟨i, hiT, hic, by simpa [native_veq] using hl⟩
  have hspec := Classical.choose_spec hDiff
  obtain ⟨c1, hc1, _⟩ := lookup_numeral m1 hca.2.1 hca.2.2 (Classical.choose hDiff)
  obtain ⟨c2, hc2, _⟩ := lookup_numeral m2 hcb.2.1 hcb.2.2 (Classical.choose hDiff)
  rw [hc1, hc2] at hspec
  simp only [__smtx_model_eval, ha, hb, __smtx_map_diff, ht1, ht2,
    __smtx_model_eval_bag_count, __smtx_bag_count, native_ite, native_and, native_Teq,
    decide_true, Bool.and_self, ite_true, dite_eq_left hDiff, hc1, hc2,
    eval_eq_numeral,
    __smtx_model_eval_not, native_not]
  simp only [native_veq, decide_eq_false_iff_not, SmtValue.Numeral.injEq] at hspec
  simp [hspec.2.2]

end Bags
end Smtm
