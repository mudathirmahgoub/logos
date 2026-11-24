module

-- Facts about the finite maps a bag value is built over, in the embedding of
-- CpcBags: what a lookup returns after an update, and what a lookup returns
-- in the map the walk $smtx_bag_op_rec of install/defs/bags/smt.eos builds.

public import CpcBags.SmtModel
import all CpcBags.SmtModel
public import CpcBags.Proofs.SmtValueOrder
import all CpcBags.Proofs.SmtValueOrder

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm
namespace Bags

open SmtEval

/-- The keys stored in a map, in order. -/
def keys : SmtMap → List SmtValue
  | .cons i _ m => i :: keys m
  | .default _ _ => []

/-- The keys of a map strictly increase in the order `native_vcmp`. -/
def Sorted : SmtMap → Prop
  | .cons i _ m => (∀ k ∈ keys m, native_vcmp k i = true) ∧ Sorted m
  | .default _ _ => True

theorem vcmp_irrefl (a : SmtValue) : native_vcmp a a = false := by
  cases h : native_vcmp a a
  · rfl
  · exact absurd rfl (SmtValueOrder.lt_ne h)

theorem vcmp_trans {a b c : SmtValue} (hab : native_vcmp a b = true)
    (hbc : native_vcmp b c = true) : native_vcmp a c = true :=
  SmtValueOrder.lt_trans hab hbc

theorem vcmp_flip {a b : SmtValue} (hne : a ≠ b) (hlt : native_vcmp a b = false) :
    native_vcmp b a = true :=
  SmtValueOrder.lt_flip hne hlt

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem lookup_cons (j e : SmtValue) (m : SmtMap) (i : SmtValue) :
    __smtx_map_lookup (.cons j e m) i = if j = i then e else __smtx_map_lookup m i := by
  simp [__smtx_map_lookup, native_ite, native_veq]

theorem lookup_default (T : SmtType) (d i : SmtValue) :
    __smtx_map_lookup (.default T d) i = d := by
  simp [__smtx_map_lookup]

theorem get_default_cons (j e : SmtValue) (m : SmtMap) :
    __smtx_map_get_default (.cons j e m) = __smtx_map_get_default m := by
  simp [__smtx_map_get_default]

theorem lookup_not_mem : ∀ (m : SmtMap) (i : SmtValue), i ∉ keys m →
    __smtx_map_lookup m i = __smtx_map_get_default m
  | .cons j e m, i, h => by
      simp only [keys, List.mem_cons, not_or] at h
      rw [lookup_cons, ite_f (fun hji => h.1 hji.symm), get_default_cons]
      exact lookup_not_mem m i h.2
  | .default T e, i, _ => by simp [__smtx_map_lookup, __smtx_map_get_default]

theorem update_cons (ed j e1 : SmtValue) (m : SmtMap) (i e2 : SmtValue) :
    __smtx_map_update_aux ed (.cons j e1 m) i e2 =
      if j = i then (if ed = e2 then m else .cons i e2 m)
      else if native_vcmp j i = true then
        (if ed = e2 then .cons j e1 m else .cons i e2 (.cons j e1 m))
      else .cons j e1 (__smtx_map_update_aux ed m i e2) := by
  simp only [__smtx_map_update_aux, __smtx_map_update_aux_no_default, native_ite,
    native_veq, decide_eq_true_eq]

theorem update_default (ed : SmtValue) (T : SmtType) (d i e2 : SmtValue) :
    __smtx_map_update_aux ed (.default T d) i e2 =
      if ed = e2 then .default T d else .cons i e2 (.default T d) := by
  simp only [__smtx_map_update_aux, __smtx_map_update_aux_no_default, native_ite,
    native_veq, decide_eq_true_eq]

theorem get_default_update (ed : SmtValue) : ∀ (m : SmtMap) (i e : SmtValue),
    __smtx_map_get_default (__smtx_map_update_aux ed m i e) = __smtx_map_get_default m
  | .cons j e1 m, i, e => by
      have ih := get_default_update ed m i e
      rw [update_cons, get_default_cons]
      by_cases hji : j = i
      · rw [ite_t hji]
        by_cases he : ed = e
        · rw [ite_t he]
        · rw [ite_f he, get_default_cons]
      · rw [ite_f hji]
        by_cases hv : native_vcmp j i = true
        · rw [ite_t hv]
          by_cases he : ed = e
          · rw [ite_t he, get_default_cons]
          · rw [ite_f he, get_default_cons, get_default_cons]
        · rw [ite_f hv, get_default_cons, ih]
  | .default T d, i, e => by
      rw [update_default]
      by_cases he : ed = e
      · rw [ite_t he]
      · rw [ite_f he, get_default_cons]

theorem keys_update (ed : SmtValue) : ∀ (m : SmtMap) (i e k : SmtValue),
    k ∈ keys (__smtx_map_update_aux ed m i e) → k = i ∨ k ∈ keys m
  | .cons j e1 m, i, e, k, h => by
      have ih := keys_update ed m i e k
      rw [update_cons] at h
      simp only [keys, List.mem_cons]
      by_cases hji : j = i
      · rw [ite_t hji] at h
        by_cases he : ed = e
        · rw [ite_t he] at h; exact Or.inr (Or.inr h)
        · rw [ite_f he] at h
          simp only [keys, List.mem_cons] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · rw [ite_f hji] at h
        by_cases hv : native_vcmp j i = true
        · rw [ite_t hv] at h
          by_cases he : ed = e
          · rw [ite_t he] at h
            simp only [keys, List.mem_cons] at h
            exact Or.inr h
          · rw [ite_f he] at h
            simp only [keys, List.mem_cons] at h
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr h
        · rw [ite_f hv] at h
          simp only [keys, List.mem_cons] at h
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · rcases ih h with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inr h')
  | .default T d, i, e, k, h => by
      rw [update_default] at h
      by_cases he : ed = e
      · rw [ite_t he] at h; simp [keys] at h
      · rw [ite_f he] at h
        simp only [keys, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inl h
        · simp [keys] at h

theorem sorted_update (ed : SmtValue) : ∀ (m : SmtMap) (i e : SmtValue),
    Sorted m → Sorted (__smtx_map_update_aux ed m i e)
  | .cons j e1 m, i, e, ⟨hall, hm⟩ => by
      rw [update_cons]
      by_cases hji : j = i
      · rw [ite_t hji]
        by_cases he : ed = e
        · rw [ite_t he]; exact hm
        · rw [ite_f he]; subst hji; exact ⟨hall, hm⟩
      · rw [ite_f hji]
        by_cases hv : native_vcmp j i = true
        · rw [ite_t hv]
          by_cases he : ed = e
          · rw [ite_t he]; exact ⟨hall, hm⟩
          · rw [ite_f he]
            refine ⟨?_, hall, hm⟩
            intro k hk
            simp only [keys, List.mem_cons] at hk
            rcases hk with hk | hk
            · subst hk; exact hv
            · exact vcmp_trans (hall k hk) hv
        · rw [ite_f hv]
          refine ⟨?_, sorted_update ed m i e hm⟩
          intro k hk
          rcases keys_update ed m i e k hk with hk' | hk'
          · subst hk'
            exact vcmp_flip hji (by simpa using hv)
          · exact hall k hk'
  | .default T d, i, e, _ => by
      rw [update_default]
      by_cases he : ed = e
      · rw [ite_t he]; trivial
      · rw [ite_f he]; exact ⟨by simp [keys], trivial⟩

theorem lookup_update_ne (ed : SmtValue) : ∀ (m : SmtMap) (i e j : SmtValue), i ≠ j →
    __smtx_map_lookup (__smtx_map_update_aux ed m i e) j = __smtx_map_lookup m j
  | .cons k e1 m, i, e, j, hij => by
      have ih := lookup_update_ne ed m i e j hij
      rw [update_cons]
      by_cases hki : k = i
      · rw [ite_t hki]
        subst hki
        have hkj : ¬ k = j := hij
        by_cases he : ed = e
        · rw [ite_t he, lookup_cons, ite_f hkj]
        · rw [ite_f he, lookup_cons, ite_f hkj, lookup_cons, ite_f hkj]
      · rw [ite_f hki]
        by_cases hv : native_vcmp k i = true
        · rw [ite_t hv]
          by_cases he : ed = e
          · rw [ite_t he]
          · rw [ite_f he, lookup_cons, ite_f hij]
        · rw [ite_f hv, lookup_cons, lookup_cons, ih]
  | .default T d, i, e, j, hij => by
      rw [update_default]
      by_cases he : ed = e
      · rw [ite_t he]
      · rw [ite_f he, lookup_cons, ite_f hij]

/-- A key that comes before every key of a sorted map is not one of them. -/
theorem not_mem_of_sorted {j e1 : SmtValue} {m : SmtMap} {i : SmtValue}
    (hs : Sorted (.cons j e1 m)) (hi : j = i ∨ native_vcmp j i = true) : i ∉ keys m := by
  intro hmem
  have hij : native_vcmp i j = true := hs.1 i hmem
  rcases hi with hi | hi
  · subst hi; simp [vcmp_irrefl] at hij
  · have := vcmp_trans hij hi
    simp [vcmp_irrefl] at this

theorem lookup_update_eq (ed : SmtValue) : ∀ (m : SmtMap) (i e : SmtValue),
    Sorted m → ed = __smtx_map_get_default m →
    __smtx_map_lookup (__smtx_map_update_aux ed m i e) i = e
  | .cons k e1 m, i, e, hs, hed => by
      rw [get_default_cons] at hed
      rw [update_cons]
      by_cases hki : k = i
      · rw [ite_t hki]
        by_cases he : ed = e
        · rw [ite_t he, lookup_not_mem m i (not_mem_of_sorted hs (Or.inl hki)), ← hed, he]
        · rw [ite_f he, lookup_cons, ite_t rfl]
      · rw [ite_f hki]
        by_cases hv : native_vcmp k i = true
        · rw [ite_t hv]
          by_cases he : ed = e
          · rw [ite_t he, lookup_cons, ite_f hki,
              lookup_not_mem m i (not_mem_of_sorted hs (Or.inr hv)), ← hed, he]
          · rw [ite_f he, lookup_cons, ite_t rfl]
        · rw [ite_f hv, lookup_cons, ite_f hki]
          exact lookup_update_eq ed m i e hs.2 hed
  | .default T d, i, e, _, hed => by
      simp only [__smtx_map_get_default] at hed
      rw [update_default]
      by_cases he : ed = e
      · rw [ite_t he, lookup_default, ← hed, he]
      · rw [ite_f he, lookup_cons, ite_t rfl]

/-- A lookup after an update of a sorted map, by the update of the embedding. -/
theorem lookup_update {m : SmtMap} (hs : Sorted m) (i e j : SmtValue) :
    __smtx_map_lookup
        (__smtx_map_update_aux (__smtx_map_get_default m) m i e) j =
      if i = j then e else __smtx_map_lookup m j := by
  by_cases hij : i = j
  · subst hij; simp [lookup_update_eq _ m i e hs rfl]
  · simp [hij, lookup_update_ne _ m i e j hij]

/-! ## The walk over the elements of a bag -/

/-- The multiplicity the operator `k` gives `i`, from the bags `m1` and `m2`. -/
@[reducible] noncomputable def combineAt (k : native_Int) (m1 m2 : SmtMap) (i : SmtValue) : SmtValue :=
  SmtValue.Numeral (__smtx_bag_combine k (__smtx_bag_mult (__smtx_map_lookup m1 i))
    (__smtx_bag_mult (__smtx_map_lookup m2 i)))

theorem op_rec_cons (k : native_Int) (e c : SmtValue) (m m1 m2 acc : SmtMap) :
    __smtx_bag_op_rec k (.cons e c m) m1 m2 acc =
      __smtx_bag_op_rec k m m1 m2
        (__smtx_map_update_aux (__smtx_map_get_default acc) acc e (combineAt k m1 m2 e)) := by
  simp [__smtx_bag_op_rec, combineAt]

theorem op_rec_default (k : native_Int) (T : SmtType) (d : SmtValue) (m1 m2 acc : SmtMap) :
    __smtx_bag_op_rec k (.default T d) m1 m2 acc = acc := by
  simp [__smtx_bag_op_rec]

/-- The walk keeps the accumulator sorted and its default, and sets the
multiplicity of each element it visits. -/
theorem op_rec_spec (k : native_Int) (m1 m2 : SmtMap) : ∀ (m acc : SmtMap), Sorted acc →
    Sorted (__smtx_bag_op_rec k m m1 m2 acc) ∧
    __smtx_map_get_default (__smtx_bag_op_rec k m m1 m2 acc) = __smtx_map_get_default acc ∧
    ∀ i, __smtx_map_lookup (__smtx_bag_op_rec k m m1 m2 acc) i =
      if i ∈ keys m then combineAt k m1 m2 i else __smtx_map_lookup acc i
  | .cons e c m, acc, hs => by
      rw [op_rec_cons]
      have hs' := sorted_update (__smtx_map_get_default acc) acc e (combineAt k m1 m2 e) hs
      obtain ⟨ih1, ih2, ih3⟩ := op_rec_spec k m1 m2 m _ hs'
      refine ⟨ih1, by rw [ih2, get_default_update], ?_⟩
      intro i
      rw [ih3 i, lookup_update hs]
      by_cases him : i ∈ keys m
      · simp [him, keys]
      · by_cases hei : e = i
        · subst hei; simp [keys]
        · have hie : ¬ i = e := fun h => hei h.symm
          simp [him, hei, hie, keys]
  | .default T d, acc, hs => by
      simp [op_rec_default, hs, keys]

theorem bag_combine_zero (k : native_Int) : __smtx_bag_combine k 0 0 = 0 := by
  simp [__smtx_bag_combine, native_ite, native_zeq, native_zplus, native_zlt,
    native_zleq, native_zneg]

/-- The multiplicity of every element in the result of a binary bag operator
is the one $smtx_bag_combine gives it, provided the operands map everything
else to zero. -/
theorem lookup_bag_op (k : native_Int) {m1 m2 : SmtMap}
    (h1 : __smtx_map_get_default m1 = SmtValue.Numeral 0)
    (h2 : __smtx_map_get_default m2 = SmtValue.Numeral 0) (i : SmtValue) :
    __smtx_bag_count i (__smtx_bag_op k (SmtValue.Bag m1) (SmtValue.Bag m2)) =
      combineAt k m1 m2 i := by
  simp only [__smtx_bag_op, __smtx_bag_count]
  generalize hT : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = T
  have hs0 : Sorted (SmtMap.default T (SmtValue.Numeral 0)) := trivial
  obtain ⟨hsA, hdA, hlA⟩ := op_rec_spec k m1 m2 m1 _ hs0
  obtain ⟨_, _, hlB⟩ := op_rec_spec k m1 m2 m2 _ hsA
  rw [hlB i, hlA i]
  by_cases hi2 : i ∈ keys m2
  · simp [hi2]
  · by_cases hi1 : i ∈ keys m1
    · simp [hi1, hi2]
    · simp only [hi1, hi2, ite_false, lookup_default]
      simp only [combineAt, lookup_not_mem m1 i hi1, lookup_not_mem m2 i hi2, h1, h2,
        __smtx_bag_mult, bag_combine_zero]

end Bags
end Smtm
