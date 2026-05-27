[← Back](README.md) | [English](proof.md) | [Japanese](proof-ja.md)

# Termination of Bashicu's Primitive Sequence System

We prove that Bashicu's *Primitive Sequence System* terminates: every expansion
is finite. To each finite sequence of natural numbers we assign an element of a
well-founded order — concretely, a finite tree ordered by a recursively defined
multiset order — and we show that every expansion step strictly decreases this
element. Well-foundedness then excludes any infinite expansion. The argument is
formalised in Isabelle/HOL; the correspondence with the mechanised statements is
given in §6. The development is elementary: every object is a concrete finite
structure, and no prior theory of ordinals is assumed.

## 1. The system

A *sequence* is a finite list of natural numbers $S = (S_0, S_1, \dots, S_{X-1})$;
positions are counted from $0$, so $S_0$ is the first entry and $X$ the length.
We write `last S` $= S_{X-1}$ for the final entry and `butlast S`
$= (S_0, \dots, S_{X-2})$ for the list with its final entry removed.

The system acts on a sequence paired with a counter $n \in \mathbb{N}$, written
$S[n]$, relative to a fixed *activation function* $f$ (Bashicu takes
$f(n) = n^2$). One expansion step is defined by cases on the final entry:

- $([])[n] = n$: the empty sequence returns the counter, and the process halts;
- if $S_{X-1} = 0$, the final $0$ is deleted:
  $$S[n] \longrightarrow (S_0, \dots, S_{X-2})[f(n)];$$
- if $m := S_{X-1} > 0$, let the *bad root* be the largest position $p < X-1$
  with $S_p < m$, and split the sequence into the *good part*
  $G = (S_0, \dots, S_{r-1})$ and the *bad part* $B = (S_r, \dots, S_{X-2})$;
  then
  $$S[n] \longrightarrow \big(G,\ \underbrace{B, B, \dots, B}_{f(n)+1 \text{ copies}}\big)[f(n)].$$

The counter $n$ and the function $f$ determine only the number of copies of $B$
and the returned value; they do not affect whether the process halts.
Termination is therefore a property of the *sequence part* alone, with the number
of additional copies $k = f(n)$ left as an arbitrary natural number. Write
$S \to T$ when one step (deletion of a final $0$, or a bad-part copy for some
$k$) sends $S$ to $T$. The theorem to be proved is that there is no infinite
chain

$$S^{(0)} \to S^{(1)} \to S^{(2)} \to \cdots.$$

## 2. The order of values

The measure assigned to sequences takes values in a set of finite trees, ordered
by a multiset order. We first recall multisets.

A *multiset* over a set is a finite collection in which multiplicity is counted
but order is disregarded; thus $\lbrace 0, 0, 1\rbrace = \lbrace 0, 1, 0\rbrace
\neq \lbrace 0, 1\rbrace$. We write $\uplus$ for multiset sum (addition of
multiplicities), so $\lbrace 0\rbrace \uplus \lbrace 0, 1\rbrace = \lbrace 0, 0,
1\rbrace$.

**Definition 2.1 (value).** A *value* is a multiset of values. The recursion is
grounded at the empty multiset; we write $H(M)$ for the value with multiset of
children $M$, and put $\mathbf{0} := H(\lbrace\rbrace)$. Equivalently, a value is
a finite tree: the node $H(M)$ has one child subtree for each element of $M$,
with repetitions permitted. In Isabelle this is the datatype
`datatype hord = H "hord multiset"`.

**Definition 2.2 (order).** Values are ordered by the multiset extension of their
own order, applied to children. For multisets $M, N$ of values, write
$M \prec_{\mathrm{ms}} N$ if $M$ is obtained from $N$ by removing one element $x$
and adjoining finitely many elements, each strictly smaller than $x$ (adjoining
none is permitted). For values, set

$$H(M) \prec H(N) \iff M \prec_{\mathrm{ms}} N.$$

The elements compared are children, hence strictly smaller trees, so the
recursion is well defined.

**Example 2.3.** With $\mathbf{1} := H(\lbrace \mathbf{0}\rbrace)$,
$\mathbf{2} := H(\lbrace \mathbf{0}, \mathbf{0}\rbrace)$ and
$\boldsymbol{\omega} := H(\lbrace \mathbf{1}\rbrace)$ one has
$\mathbf{2} \prec \boldsymbol{\omega}$: from the children $\lbrace
\mathbf{1}\rbrace$ of $\boldsymbol{\omega}$, remove $\mathbf{1}$ and adjoin two
copies of $\mathbf{0}$ (each below $\mathbf{1}$) to obtain $\lbrace \mathbf{0},
\mathbf{0}\rbrace$.

**Proposition 2.4 (well-foundedness).** The order $\prec$ admits no infinite
strictly decreasing chain $v_0 \succ v_1 \succ v_2 \succ \cdots$; equivalently,
every non-empty set of values has a $\prec$-minimal element.

*Proof.* By structural induction on values, using the fact that the multiset
extension of a well-founded order is well-founded. This is the theorem `wfP_hlt`,
formalised over `HOL-Library.Multiset` alone. $\square$

**Remark 2.5.** Reading $H(M)$ as the ordinal $\omega^{a_1} \oplus \cdots \oplus
\omega^{a_k}$, where $a_1, \dots, a_k$ are the children and $\oplus$ is the
natural sum, identifies the values with the ordinals below $\varepsilon_0$ and
$\prec$ with the ordinal order. This reading is not used below.

## 3. The measure on sequences

To each sequence $S$ we attach a value $o(S)$.

**Definition 3.1 (forest of a sequence).** For a position $i$ of $S$, its
*parent* is the largest $j < i$ with $S_j < S_i$; if no earlier entry is smaller,
$i$ is a *root*. (This is the rule defining the bad root: when a step deletes the
final entry, its parent is the bad root.) The parent relation presents $S$ as a
forest.

For instance `(0,1,2,0,1)` is the forest of two trees

```
  position:  0  1  2  3  4            0 (pos 0)        0 (pos 3)
  entry:     0  1  2  0  1            └ 1 (pos 1)      └ 1 (pos 4)
                                        └ 2 (pos 2)
```

**Definition 3.2 (the measure $o$).** Assign to each tree the value
$H(\text{children})$ and combine the trees of a forest by $\uplus$. Read from the
left, this is the recursion

$$o([]) = H(\lbrace\rbrace), \qquad
  o(a \# \mathit{rest}) = H\big(\ \lbrace o(\mathit{inside})\rbrace \ \uplus\ C\ \big),$$

where $\mathit{inside}$ is the longest prefix of $\mathit{rest}$ all of whose
entries exceed $a$ (the descendants of the first node), $\mathit{outside}$ is the
remaining suffix, and $C$ is the multiset of children of $o(\mathit{outside})$
(that is, $o(\mathit{outside}) = H(C)$). This is the Isabelle function `omap`.

The measure takes the following values, verified in Isabelle:
$o(0) = \mathbf{1}$, a run of $k$ zeros has value $\mathbf{k}$, $o(0,1) =
\boldsymbol{\omega}$, $o(0,1,1) = \boldsymbol{\omega}^2$, and $o(0,1,2) =
\boldsymbol{\omega}^{\boldsymbol{\omega}}$ (the displayed ordinals are by
Remark 2.5; each is concretely a finite tree).

## 4. Each step decreases the measure

We prove $o(T) \prec o(S)$ whenever $S \to T$, treating the two cases separately
after an auxiliary monotonicity lemma.

**Lemma 4.1 (`omap_snoc_increases`).** For every sequence $C$ and every $m$,
$$o(C) \prec o(C, m).$$

*Proof.* Appending an entry adds one node to the forest: either a new root,
adjoining one further top-level child $\mathbf{0}$, or an additional descendant
of an existing node, enlarging that node. In either case the value strictly
increases. The formal proof is by induction following the recursion of $o$.
$\square$

**Proposition 4.2 (deletion of a final $0$, `m_drop0_decreases`).** If $S$ is
non-empty and `last S` $= 0$, then $o(\texttt{butlast } S) \prec o(S)$.

*Proof.* A final $0$ is below every entry, hence a root, and being last it has no
descendants; it is an isolated leaf. Thus $o(S)$ is $o(\texttt{butlast } S)$ with
one additional top-level child $\mathbf{0}$, and deletion of a single element of
a multiset is a $\prec_{\mathrm{ms}}$-decrease. $\square$

We now treat the bad-part step
$S = (G, B, m) \to (G, \underbrace{B, \dots, B}_{k+1})$, where $m =$ `last S`
$> 0$ and $B = (v, B_t)$ with $v = S_r$ the entry at the bad root $r$. Since $r$
is the *last* earlier position with entry below $m$, every entry of $B_t$ is at
least $m$, hence exceeds $v$.

**Lemma 4.3 (`omap_rep`, `omap_BfM`, `omap_core`).** Under these hypotheses,
$$o\big(\underbrace{B, \dots, B}_{k+1}\big) \prec o(B, m).$$

*Proof.* The $k+1$ copies of $B = (v, B_t)$ form $k+1$ adjacent trees, each a root
$v$ with descendant forest $B_t$; hence (lemma `omap_rep`)
$$o\big(\underbrace{B, \dots, B}_{k+1}\big) = H\big(\underbrace{o(B_t), \dots, o(B_t)}_{k+1}\big).$$
In $(B, m) = (v, B_t, m)$ the appended $m$ exceeds $v$ and every entry of $B_t$,
so its parent is $v$; it becomes one further descendant of the single root $v$,
whence (lemma `omap_BfM`)
$$o(B, m) = H\big(\lbrace o(B_t, m)\rbrace\big).$$
The right-hand multiset has the single element $o(B_t, m)$, the left-hand one has
$k+1$ copies of $o(B_t)$, and $o(B_t) \prec o(B_t, m)$ by Lemma 4.1. Replacing one
element by finitely many strictly smaller ones is, by definition, a
$\prec_{\mathrm{ms}}$-decrease. $\square$

**Lemma 4.4 (`omap_BADCTX`).** For every good part $G$,
$$o\big(G, \underbrace{B, \dots, B}_{k+1}\big) \prec o(G, B, m).$$

*Proof.* By induction on the length of $G$. Removing the first entry $g$, the
recursion of $o$ either confines the comparison to the interior of $G$, reducing
it to a shorter good part with an identical surrounding context on both sides, or,
once $g$ lies below the bad part, reduces it to Lemma 4.3. The base case
($G$ empty) is Lemma 4.3 itself. $\square$

**Proposition 4.5 (bad-part step, `m_bad_decreases`).** If $S$ is non-empty,
`last S` $> 0$, and a bad root exists, then
$o\big(G, \underbrace{B, \dots, B}_{k+1}\big) \prec o(S)$ for every $k$.

*Proof.* The candidate positions for the bad root form a finite set, non-empty
because $S_0 = 0 < m$ in any reachable sequence, so the bad root is well defined;
the claim is Lemma 4.4. $\square$

## 5. Termination

**Theorem 5.1 (`m_step_decreases`).** If $S \to T$, then $o(T) \prec o(S)$.

*Proof.* The two cases are Propositions 4.2 and 4.5. $\square$

**Theorem 5.2 (termination, `m_termination`).** There is no infinite chain
$S^{(0)} \to S^{(1)} \to \cdots$; equivalently (`m_no_infinite_expansion`), every
expansion is finite.

*Proof.* An infinite chain would, by Theorem 5.1, induce an infinite strictly
decreasing chain $o(S^{(0)}) \succ o(S^{(1)}) \succ \cdots$ of values,
contradicting Proposition 2.4. $\square$

## 6. Correspondence with the Isabelle development

The statements are transcribed in `prss_paper.thy` (prefix `p_`, left as `sorry`)
and discharged by the `m_*` facts in `prss_mechanized.thy`. The session is built
with `isbman build -d . -v PRSS`.

| Object | Isabelle | source |
|---|---|---|
| value $H(M)$ | `datatype hord = H "hord multiset"` | [prss_ordinal.thy:16](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L16) |
| order $\prec$ | `hlt` | [prss_ordinal.thy:20](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L20) |
| Proposition 2.4 | `wfP_hlt` | [prss_ordinal.thy:199](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L199) |
| sequence | `nat list` | [prss_defs.thy](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy) |
| measure $o$ (Def. 3.2) | `omap` | [prss_defs.thy:40](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L40) |
| bad root (Def. 3.1) | `badset` / `badroot` | [prss_defs.thy:67](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L67), [70](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L70) |
| step $S \to T$ | `step` (`drop0`, `bad`) | [prss_defs.thy:76](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L76) |
| Lemma 4.1 | `omap_snoc_increases` | [prss_mechanized.thy:106](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L106) |
| Proposition 4.2 | `m_drop0_decreases` | [prss_mechanized.thy:161](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L161) |
| Lemma 4.3 | `omap_rep`, `omap_BfM`, `omap_core` | [prss_mechanized.thy:204](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L204) |
| Lemma 4.4 | `omap_BADCTX` | [prss_mechanized.thy:303](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L303) |
| Proposition 4.5 | `m_bad_decreases` | [prss_mechanized.thy:426](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L426) |
| Theorem 5.1 | `m_step_decreases` | [prss_mechanized.thy:494](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L494) |
| Theorem 5.2 | `m_termination`, `m_no_infinite_expansion` | [prss_mechanized.thy:506](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L506), [515](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L515) |

---

Source: Koteitan, "Purely mathematical definition of BMS" (Googology Wiki);
Bashicu, "BASIC言語による巨大数のまとめ" (Googology Wiki, 2015).
