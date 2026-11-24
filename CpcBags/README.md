# CpcBags: the bag rules of cvc5, with their semantics

`CpcBags` is CPC reduced to the bag rules of cvc5, compiled with a semantics of
bags. It is separate from `Cpc`, which it leaves untouched.

## The semantics

A bag is a map from elements to positive multiplicities; every other element
maps to `0`.

```smt2
(bag.union_disjoint (bag "a" 2) (bag "a" 3))   ; value: Bag {"a" ↦ 5}
(bag.count "b" (bag "a" 2))                    ; value: 0
```

It is written in Eunoia, as patches that add to `install/defs/smt.eos` and
`install/defs/Cpc.eos`. They only add lines, so the semantics of every other
symbol is the one `Cpc` has:

| file                               | adds                                                      |
| ---------------------------------- | --------------------------------------------------------- |
| `install/defs/bags/smt.eos.patch`  | sort `Bag`, value `Bag m`, and the `:eval` of each symbol |
| `install/defs/bags/Cpc.eos.patch`  | how each CPC bag symbol, and `tuple.project`, translates to the SMT-LIB symbols |

`tuple.project` is there because the bags signature of cvc5 includes it (the
type of `table.project` uses it), and every symbol of the signature needs a
meaning. It is the tuple of the selected components:

```smt2
(tuple.project (@list 2 0) t)   ; is (tuple (tuple.select 2 t) (tuple.select 0 t))
(tuple.project @list.nil t)     ; is (@purify tuple.unit), for t well typed
```

`bag.member` and `bag.subbag` are eliminated, the way the bags rewriter
eliminates them:

```smt2
(bag.member x a)   ; becomes (>= (bag.count x a) 1)
(bag.subbag a b)   ; becomes (= (bag.difference_subtract a b) (as bag.empty (Bag T)))
```

`@bags_deq_diff` becomes `map_diff`, as `@sets_deq_diff` does. `bag.card`,
`bag.filter`, `bag.map`, `bag.fold` and the table operators have no semantics
yet.

## Regenerate and build

```bash
install/defs/bags/install-bags.sh <cvc5>          # applies the patches, then compiles
lake -d verification build CpcBagsVerification    # semantics and proofs, with Mathlib
```

`<cvc5>` is a checkout of a cvc5 branch with the bag rules,
`proofs/eo/cpc/expert/rules/Bags.eo`, such as
[bags-eunoia](https://github.com/mudathirmahgoub/cvc5/tree/bags-eunoia).

A patch that no longer applies means `install/defs` changed under it. Apply it
by hand and write it again, e.g. for `Cpc.eos`:

```bash
diff -u --label Cpc.eos --label Cpc.eos install/defs/Cpc.eos Cpc-with-bags.eos > install/defs/bags/Cpc.eos.patch
```

## What is proven

`CpcBags/Proofs/BagRules.lean` and `BagExt.lean` prove that the conclusion of
each rule evaluates to true in every model, given that its bag terms evaluate
to bags. For example, `bags_count_def_union_disjoint`:

```smt2
(= (bag.count e (bag.union_disjoint a b)) (+ (bag.count e a) (bag.count e b)))
```

| cvc5 rule            | theorems                                        |
| -------------------- | ----------------------------------------------- |
| `BAGS_COUNT_NON_NEG` | `bags_count_non_neg`                            |
| `BAGS_COUNT_DEF`     | `bags_count_def_{empty,bag,union_disjoint,union_max,inter_min,difference_subtract,difference_remove,setof}` |
| `BAGS_MAKE_SPLIT`    | `bags_make_split`                               |
| `BAGS_EXT`           | `bags_ext` (via `map_ext`, extensionality of canonical maps) |

They use only `propext`, `Classical.choice` and `Quot.sound`.

## What is not proven

The per-rule obligations `cmd_step_<rule>_properties` of the checker are not
discharged. The compiler writes them under `CpcBags/Proofs/Rules/` with `sorry`
for a proof, and `install-bags.sh` drops them. Discharging them needs the infrastructure of `Cpc/Proofs` (translation,
type preservation) extended to the bag constructors. In particular, type
preservation must show that the bag operators return canonical bags, which is
what the hypothesis `IsBag` assumes.

`BAGS_FILTER_UP`, `BAGS_FILTER_DOWN` and `BAGS_MAP_UP` are higher-order and are
not compiled here.
