[English](README.md) | [Japanese](README-ja.md)

# prss-proof

Version: **v0.1.7**

A machine-checked proof, in **Isabelle/HOL**, that **Bashicu's Primitive Sequence
System** (原始数列システム) always terminates.

The strategy is the classical one: map every primitive sequence to an ordinal
below $\varepsilon_0$ and show that each `expand` step strictly decreases this
ordinal. Since the ordinals below $\varepsilon_0$ are well-founded, no infinite
expansion is possible.

See [proof.md](proof.md) for the mathematical write-up (also as
[`proof.html`](proof.html) / [`index-ja.html`](index-ja.html), MathJax + dark mode).

## What is proved

The expansion relation `step` on primitive sequences is well-founded
(`m_termination`); equivalently there is no infinite expansion sequence
(`m_no_infinite_expansion`). Both follow from `m_step_decreases`: every step
strictly decreases the ordinal map `omap`.

## File layout

| File | Role |
|---|---|
| `prss_ordinal.thy` | Ordinals below $\varepsilon_0$ as hereditarily finite multisets `hord`, with the well-founded order `hlt` (`wfP_hlt`). |
| `prss_defs.thy` | The primitive sequence, the `expand` step relation `step`, the bad root, and the forest ordinal map `omap`. |
| `prss_paper.thy` | Statements of the propositions and the main theorem (all `sorry`). |
| `prss_mechanized.thy` | The machine-checked proofs discharging them. |
| [`proof.md`](proof.md) | Human-readable mathematical proof (also `proof.html`). |

Naming: paper statements are `p_*`, mechanized proofs `m_*`.

## The ordinal kernel

Ordinals below $\varepsilon_0$ are modelled by the nested-multiset datatype

```isabelle
datatype hord = H "hord multiset"
```

where `H M` denotes the natural sum $\bigoplus_{x\in M}\omega^{x}$ and the order is
the multiset extension of itself. Well-foundedness (`wfP_hlt`) is proved from
`HOL-Library.Multiset` alone — no AFP entry is required.

## Build

```
isbman build -d . -v PRSS
```

(`isbman` wraps `isabelle build` with per-directory heap isolation; the session is
defined in `ROOT` as `PRSS = HOL` with `HOL-Library`. `quick_and_dirty` is set
because `prss_paper.thy` uses `sorry` for the statements.)

## Progress

Per-fact status is tracked in [`task.md`](task.md).

## References

- Koteitan, *Purely mathematical definition of BMS*, Googology Wiki user blog.
- Bashicu, *BASIC言語による巨大数のまとめ*, Googology Wiki user blog, 2015.
