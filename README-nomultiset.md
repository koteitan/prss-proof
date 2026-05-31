[← Back](README.md) | [English](README-nomultiset.md) | [Japanese](README-nomultiset-ja.md)

# Multiset-free termination proof (branch `without-multiset`)

`prss_nomultiset.thy` is a **self-contained** proof of the same termination
result as the `main` branch, but **without `HOL-Library.Multiset`** — it imports
only `Main`.

## What it does

Ordinals below ε₀ are represented as **Cantor normal forms** by the binary
datatype

```isabelle
datatype ord = Z | E ord ord        (* E a b  =  ω^a + b *)
```

with a `cnf` predicate (exponents non-increasing, hereditarily). The order
`olt` (`<o`) is the lexicographic CNF order. The file proves, with no external
library beyond `Main`:

| Result | Statement |
|---|---|
| `wfP_R` | `olt` restricted to CNF terms is well-founded (built by a hand-rolled accessibility argument — no `wfp_multp`) |
| `omap` | measure `nat list ⇒ ord` via single-term insertion `ins` (= ω^e into a CNF) |
| `cnf_omap` | `omap` always yields a CNF |
| `m_drop0` / `m_bad` | each expansion step strictly decreases `omap` |
| `m_termination` | `wf {(T, S). step S T}` |
| `m_no_infinite_expansion` | no infinite expansion sequence |

## Why this is *more* work than the multiset version

Any ordered CNF encoding is **not** well-founded without the sortedness
invariant (e.g. `[1] ≻ [0,1] ≻ [0,0,1] ≻ …` are all "ascending" non-CNF terms),
so this proof must:

- prove ε₀ well-foundedness from scratch (the `accp` argument that `main` gets
  for free from `wfp_multp`);
- define the natural sum as the insertion `ins` and prove `ins_comm`, `cnf_ins`,
  and the **monotonicity** `ins_mono2` by hand (`main` gets these from the
  one-step multiset-order lemmas);
- carry CNF/sortedness through every lemma.

The result (~890 lines) is considerably longer than `main`'s multiset version,
confirming that multisets are the cheaper representation for this problem: the
forest children are naturally unordered, so quotienting order away (multisets)
avoids all of the above. This branch exists to demonstrate the alternative is
*possible*, not preferable.

## Build

```
isbman build -d . -v PRSS
```
(`prss_nomultiset` is listed in `ROOT`; it is independent of the other theories.)
