[← Back](README.md) | [English](proof.md) | [Japanese](proof-ja.md)

# Termination of Bashicu's Primitive Sequence System

A self-contained mathematical proof, formalised in Isabelle/HOL
(`prss_ordinal.thy`, `prss_defs.thy`, `prss_paper.thy`, `prss_mechanized.thy`).
The strategy is to map each primitive sequence to an ordinal below $\varepsilon_0$
and show that every expansion step strictly decreases this ordinal.

## 1. The Primitive Sequence System

A **primitive sequence** is a finite list of natural numbers
$\mathbf{S}=(S_0,S_1,\dots,S_{X-1})$, where $X$ is its length. Together with a
counter $n\in\mathbb{N}$ and an activation function $f$ (Bashicu uses $f(n)=n^2$),
the expansion function $\mathrm{expand}$ is defined by:

- $\mathrm{expand}([n]) = n$ &nbsp; (empty sequence: return the counter);
- if $S_{X-1}=0$: &nbsp; $\mathrm{expand}(\mathbf{S}[n]) = \mathrm{expand}\big((S_0,\dots,S_{X-2}) [f(n)]\big)$ &nbsp; (**drop the trailing 0**);
- otherwise, let the **bad root** be $r=\max\lbrace  p \mid S_p < S_{X-1} \wedge p<X-1 \rbrace $, the **good part** $\mathbf{G}=(S_0,\dots,S_{r-1})$ and the **bad part** $\mathbf{B}=(S_r,\dots,S_{X-2})$; then

$$\mathrm{expand}(\mathbf{S}[n]) = \mathrm{expand}\big(\mathbf{G} \underbrace{\mathbf{B} \mathbf{B}\cdots\mathbf{B}}_{f(n)+1} [f(n)]\big).$$

The number $\mathrm{Primitive}(n)=\mathrm{expand}\big((0,1,\dots,n{+}1)[n]\big)$
has size $f_{\psi(\varepsilon_0)+1}(10)$ in the fast-growing hierarchy.
**Termination** means that, started from any sequence, the process reaches the
empty sequence after finitely many steps. This is independent of the counter $n$
and of $f$: it holds iff the *sequence part* always shrinks to $[ ]$. We
therefore study the rewriting of the sequence part alone, with the number
$k=f(n)$ of extra copies left arbitrary.

## 2. The forest reading of a primitive sequence

Read each index $i$ as a node of a forest, where the **parent** of $i$ is

$$\mathrm{parent}(i)=\max\lbrace  j \mid j<i \wedge S_j<S_i \rbrace ,$$

the nearest earlier index with a strictly smaller value (and $i$ is a **root**
when no such $j$ exists). This is exactly the rule that defines the bad root:
when $\mathrm{expand}$ removes the last element $S_{X-1}$, that element's parent
is the bad root $r$.

For example `(0,1,2,0,1)` reads as two trees:

```
  index:  0  1  2  3  4              0(idx0)        0(idx3)
  value:  0  1  2  0  1              └ 1(idx1)      └ 1(idx4)
                                       └ 2(idx2)
```

## 3. The ordinal map

**Definition (ordinal of a forest).** Using the natural (Hessenberg) sum
$\oplus$,

$$o(\text{node } i)=\bigoplus_{c\ \text{child of}\ i}\omega^{ o(c)}, \qquad o(\mathbf{S})=\bigoplus_{r\ \text{root}}\omega^{ o(r)} .$$

A leaf has $o=0$, so $\omega^0=1$.

In the formalisation an ordinal below $\varepsilon_0$ is a **hereditarily finite
multiset** `datatype hord = H "hord multiset"`: $H M$ denotes
$\bigoplus_{x\in M}\omega^{x}$, with $H \lbrace \rbrace =0$. The order is the multiset
extension of itself,

$$H M \prec H N \iff M \prec_{\mathrm{mult}} N,$$

which is precisely the comparison of Cantor normal forms below $\varepsilon_0$,
and is **well-founded** (theorem `wfP_hlt`; proved from the well-foundedness of
the multiset order restricted to the accessible part).

The map is computed left-to-right by splitting off the first element as a root:
its descendants are the maximal following block of strictly larger values, and
the rest continues the forest. In Isabelle (`omap`):

```
omap [] = H {}
omap (a # rest) = H ( {| omap (takeWhile (<a<) rest) |}
                      ⊕ omap (dropWhile (<a<) rest) )
```

where `takeWhile (λx. a<x) rest` is $a$'s descendant forest. Sanity checks
(machine-checked): $o(0,1)=\omega$, $o(0,1,1)=\omega^2$, $o(0,1,2)=\omega^{\omega}$,
and a run of $k$ zeros is $k$. The order type of all primitive sequences is
$\varepsilon_0$.

## 4. Each step strictly decreases the ordinal

### 4.1 Auxiliary fact (★): appending one element strictly increases $o$

**Lemma (★, `omap_snoc_increases`).** For every sequence $C$ and every $m$,
&nbsp; $o(C) \prec o(C \mathbin{++} [m])$.

Adding a node to a forest can only enlarge it: $m$ becomes a new root (adding a
term $\omega^0$) or an extra child somewhere along the right spine (enlarging
one exponent). Proved by induction following the recursion of `omap`.

### 4.2 Drop-zero case

**Proposition (`m_drop0_decreases`).** If $S\neq[ ]$ and $\mathrm{last} S=0$
then $o(\mathrm{butlast} S)\prec o(S)$.

A trailing $0$ is minimal, hence a root, and being last it is a leaf. Removing
it deletes exactly one top-level term $\omega^0$:
$o(S)=H\big(\lbrace H\lbrace \rbrace \rbrace +M\big)$ and $o(\mathrm{butlast} S)=H M$, so the removal
is a multiset (hence ordinal) decrease.

### 4.3 Bad-part case

Write $S=\mathbf{G} \mathbf{B} [m]$ with $m=\mathrm{last} S>0$,
$\mathbf{B}=v\#\mathbf{B}_t$ where $v=S_r$ is the bad-root value. By maximality
of $r$, every element of $\mathbf{B}_t$ is $\ge m$, hence $>v$. The step rewrites
$S$ to $\mathbf{G} \mathbf{B}^{ k+1}$ ($k=f(n)$ extra copies).

**Lemma (core, `omap_core`).** Under the above conditions,

$$o\big(\mathbf{B}^{ k+1}\big)\ \prec\ o\big(\mathbf{B} [m]\big).$$

Two computations make this transparent. First, $k$ consecutive copies of
$\mathbf{B}=v\#\mathbf{B}_t$ form $k$ sibling trees each rooted at $v$ with
descendant forest $\mathbf{B}_t$, so

$$o\big(\mathbf{B}^{ k+1}\big)=H\big( (k{+}1)\cdot\lbrace  o(\mathbf{B}_t) \rbrace  \big)$$

(lemma `omap_rep`).

Second, in $\mathbf{B} [m]=v\#(\mathbf{B}_t [m])$ the new $m$ is a child of $v$
(all of $\mathbf{B}_t$ exceeds $v$ and $m>v$), so

$$o\big(\mathbf{B} [m]\big)=H\big(\lbrace  o(\mathbf{B}_t [m]) \rbrace \big)$$

(lemma `omap_BfM`).

The decrease is therefore a single multiset step: replace the one element
$o(\mathbf{B}_t [m])$ by $k{+}1$ copies of $o(\mathbf{B}_t)$, each strictly
smaller by (★).

**Lemma (with context, `omap_BADCTX`).** For every good part $\mathbf{G}$,

$$o\big(\mathbf{G} \mathbf{B}^{ k+1}\big)\ \prec\ o\big(\mathbf{G} \mathbf{B} [m]\big).$$

By strong induction on the length of $\mathbf{G}$. Peeling the first element
$g$, the recursion of `omap` either keeps the comparison inside $\mathbf{G}$
(reducing to a shorter context via the congruence `hlt_under_H`), or — once $g$
falls below the bad part — reduces directly to the context-free core. The base
case $\mathbf{G}=[ ]$ is the core.

**Proposition (`m_bad_decreases`).** If $S\neq[ ]$, $\mathrm{last} S>0$ and a
bad root exists, then for every $k$,
$o\big(\mathbf{G} \mathbf{B}^{ k+1}\big)\ \prec\ o(S)$.

Wiring: the bad set $\lbrace p<X{-}1 \mid S_p<\mathrm{last} S\rbrace $ is finite and
nonempty, so $r=\max$ is a genuine bad root; $S=\mathbf{G} (v\#\mathbf{B}_t) [m]$
and the maximality of $r$ gives $\mathbf{B}_t\ge m$. The claim is then
`omap_BADCTX`.

## 5. Main theorem

**Theorem (`m_step_decreases`).** If $S \to T$ is one expansion step, then
$o(T) \prec o(S)$.

**Theorem (termination, `m_termination`).** The expansion relation
$\lbrace (T,S)\mid S\to T\rbrace $ is well-founded. Equivalently
(`m_no_infinite_expansion`) there is no infinite expansion sequence:
$\mathrm{expand}$ always halts.

Since $o$ strictly decreases at every step and $\prec$ is well-founded on the
ordinals below $\varepsilon_0$, the expansion relation is the inverse image of a
well-founded relation under $o$, hence well-founded. $\qquad\blacksquare$

## 6. Correspondence with the Isabelle formalisation

| Notion in this document | Isabelle | File |
|---|---|---|
| ordinal below $\varepsilon_0$, $H\,M$ | `datatype hord = H "hord multiset"` | `prss_ordinal.thy` |
| order $\prec$ | `hlt` (`hlt (H M) (H N) ⟷ multp hlt M N`) | `prss_ordinal.thy` |
| $\prec$ is well-founded | `wfP_hlt` | `prss_ordinal.thy` |
| primitive sequence | `nat list` | `prss_defs.thy` |
| ordinal map $o$ | `omap :: nat list ⇒ hord` | `prss_defs.thy` |
| bad set / bad root $r$ | `badset` / `badroot` | `prss_defs.thy` |
| one expansion step $S \to T$ | `step :: nat list ⇒ nat list ⇒ bool` (`drop0`, `bad`) | `prss_defs.thy` |
| (★) append increases $o$ | `omap_snoc_increases` | `prss_mechanized.thy` |
| §4.2 drop-zero decrease | `m_drop0_decreases` | `prss_mechanized.thy` |
| §4.3 $o(\mathbf{B}^{k+1})=H((k{+}1)\cdot\lbrace o(\mathbf{B}_t)\rbrace)$ | `omap_rep` | `prss_mechanized.thy` |
| §4.3 core decrease | `omap_core` | `prss_mechanized.thy` |
| §4.3 with context $\mathbf{G}$ | `omap_BADCTX` | `prss_mechanized.thy` |
| §4.3 bad-part decrease | `m_bad_decreases` | `prss_mechanized.thy` |
| §5 step decreases $o$ | `m_step_decreases` | `prss_mechanized.thy` |
| §5 termination | `m_termination`, `m_no_infinite_expansion` | `prss_mechanized.thy` |

The statements live in `prss_paper.thy` (as `p_*`, kept `sorry`); the proofs are
the `m_*` facts in `prss_mechanized.thy`. Build with `isbman build -d . -v PRSS`.

---

Source: Koteitan, "Purely mathematical definition of BMS" (Googology Wiki);
Bashicu, "BASIC言語による巨大数のまとめ". The ordinal kernel reuses only
`HOL-Library.Multiset`; no AFP entry is required.
