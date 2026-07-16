[English](README.md) | [Japanese](README-ja.md)

# prss-proof

Version: **v0.1.11**

A machine-checked proof, in **Isabelle/HOL**, that **Bashicu's Primitive Sequence
System** (原始数列システム) always terminates.

The strategy is the classical one: map every primitive sequence to an ordinal
below $\varepsilon_0$ and show that each `expand` step strictly decreases this
ordinal. Since the ordinals below $\varepsilon_0$ are well-founded, no infinite
expansion is possible.

## Two independent developments

The same theorem is proved twice, with two different representations of the
ordinals below $\varepsilon_0$. Each directory is self-contained.

| | [`with-multiset/`](with-multiset/proof.md) | [`without-multiset/`](without-multiset/proof.md) |
|---|---|---|
| Write-up | [proof.md](with-multiset/proof.md) ([ja](with-multiset/proof-ja.md)) | [proof.md](without-multiset/proof.md) ([ja](without-multiset/proof-ja.md)) |
| Ordinal representation | hereditarily finite multisets | Cantor normal forms |
| Datatype | `hord = H "hord multiset"` | `ord = Z \| E ord ord` |
| Order | multiset extension `hlt` | lexicographic `olt` (`<o`) |
| Well-foundedness | `wfP_hlt`, via library `wfp_multp` | `wfP_R`, hand-rolled accessibility |
| Imports | `HOL-Library.Multiset` | `Main` only |
| Size | shorter | ~890 lines |

**Which to read.** `with-multiset/` is the recommended version: a forest's
children are unordered by nature, so a multiset is the honest representation, and
the Dershowitz–Manna well-foundedness of the multiset order comes for free from
`HOL-Library.Multiset`. `without-multiset/` demonstrates that the multiset notion
is *avoidable*: Cantor normal forms are sequences of exponents, so the
development must carry a sortedness invariant (`cnf`) through every lemma and
prove the well-foundedness of $\varepsilon_0$ from scratch. That makes it
considerably longer, which is precisely the point — it measures what the multiset
library was buying.

Neither development imports an ordinal library. Both only build a datatype with a
well-founded order; "ordinal" is the reading, not a formal ingredient.

## What is proved

In both versions, the expansion relation `step` on primitive sequences is
well-founded (`m_termination`); equivalently there is no infinite expansion
sequence (`m_no_infinite_expansion`). Both follow from the fact that every step
strictly decreases the ordinal map `omap`.

## File layout

```
with-multiset/
  prss_ordinal.thy       ordinals below ε₀ as hereditarily finite multisets, wfP_hlt
  prss_defs.thy          primitive sequences, step, bad root, omap
  prss_paper.thy         statements of the propositions and main theorem (all sorry)
  prss_mechanized.thy    the machine-checked proofs discharging them
  proof.md / proof-ja.md human-readable mathematical proof
without-multiset/
  prss_nomultiset.thy    the whole development, imports Main only
  proof.md / proof-ja.md human-readable mathematical proof
ROOT                     Isabelle session PRSS (builds both)
task.md                  per-fact progress
```

Naming: in `with-multiset/`, paper statements are `p_*` and mechanized proofs
`m_*`.

## Build

```
isbman build -d . -v PRSS
```

The `PRSS` session builds both developments. (`isbman` wraps `isabelle build`
with per-directory heap isolation. `quick_and_dirty` is set because
`with-multiset/prss_paper.thy` uses `sorry` for the statements.)

## Progress

Per-fact status is tracked in [`task.md`](task.md).

## References

- Koteitan, *Purely mathematical definition of BMS*, Googology Wiki user blog.
- Bashicu, *BASIC言語による巨大数のまとめ*, Googology Wiki user blog, 2015.
