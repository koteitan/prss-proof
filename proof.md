[← Back](README.md) | [English](proof.md) | [Japanese](proof-ja.md)

# Termination of Bashicu's Primitive Sequence System

We prove termination of Bashicu's *Primitive Sequence System*. Each sequence
$S \in \mathsf{list}(\mathbb{N})$ is mapped to a value $o(S)$ in a well-founded
order $(\mathsf{hord}, \prec)$, and each expansion step strictly decreases $o$;
well-foundedness then forbids any infinite expansion. The argument is formalised
in Isabelle/HOL (correspondence in §7). Notation follows Isabelle: lists $[]$,
cons $a \mathbin{::} xs$, append $xs \mathbin{@} ys$, $\mathrm{last}$,
$\mathrm{butlast}$, $\mathrm{take}\ r\ xs$, $\mathrm{drop}\ r\ xs$,
$\mathrm{takeWhile}\ P\ xs$, $\mathrm{dropWhile}\ P\ xs$, $\mathrm{concat}$,
$\mathrm{replicate}\ k\ x$, indexing $S \mathbin{!} p$.

A relation $R$ is *well-founded* when there is no infinite chain
$x_0\,R^{-1}\,x_1\,R^{-1}\,x_2\,\cdots$ (no infinite descent).

## 1. The expansion step

For a counter $n \in \mathbb{N}$ and activation function $f$ (Bashicu:
$f(n)=n^2$), with $X = \mathrm{length}\ S$ and $m = \mathrm{last}\ S$,

$$\mathrm{expand}([][n]) = n, \qquad
\mathrm{expand}(S[n]) =
\begin{cases}
\mathrm{expand}((\mathrm{butlast}\ S)[f(n)]) & m = 0,\\[2pt]
\mathrm{expand}((G \mathbin{@} \underbrace{B \mathbin{@} \cdots \mathbin{@} B}_{f(n)+1})[f(n)]) & m > 0,
\end{cases}$$

$$r = \max\lbrace p \mid p < X-1 \ \wedge\ S \mathbin{!} p < m\rbrace, \qquad
G = \mathrm{take}\ r\ S, \qquad
B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S).$$

**Definition 1.1 (step relation, `step`).** Drop the counter and $f$, and let the
copy count $k \in \mathbb{N}$ be arbitrary. Define $S \to T$ inductively by

$$\frac{S \neq []\quad m = 0}{S \to \mathrm{butlast}\ S}\ (\mathrm{drop0}),
\qquad
\frac{S \neq []\quad 0 < m \quad \mathrm{badset}\ S \neq \emptyset}
{S \to (\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k+1)\ B)}\ (\mathrm{bad}),$$

with $r = \mathrm{badroot}\ S$, $B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$ and

$$\mathrm{badset}\ S = \lbrace p \mid p < \mathrm{length}\ S - 1 \ \wedge\ S \mathbin{!} p < m\rbrace,
\qquad \mathrm{badroot}\ S = \max(\mathrm{badset}\ S).$$

Termination of $\mathrm{expand}$ for any $f, n$ reduces to nonexistence of an
infinite chain $S^{(0)} \to S^{(1)} \to \cdots$, since the sequence part of any
expansion run is such a chain.

## 2. Multisets

A multiset is like a set but counts repetitions and ignores order; we write it
with double braces. For example $\lbrace\lbrace 1, 1, 4 \rbrace\rbrace$ has two
$1$'s and one $4$, equals $\lbrace\lbrace 4, 1, 1 \rbrace\rbrace$, and differs
from $\lbrace\lbrace 1, 4 \rbrace\rbrace$ (one $1$). The empty one is
$\lbrace\lbrace\rbrace\rbrace$.

**Definition 2.1 (finite multisets).** A *multiset* over a set $A$ is a map
$\mu : A \to \mathbb{N}$, with $\mu(a)$ the *multiplicity* of $a$. It is *finite*
when only finitely many multiplicities are nonzero:

$$\mathcal{M}_{\mathrm{fin}}(A) = \lbrace \mu : A \to \mathbb{N} \ \mid\ \lvert \lbrace a \in A : \mu(a) > 0\rbrace \rvert < \infty \rbrace.$$

Membership, the empty and singleton multisets, and the sum $\uplus$ are

$$a \in \mu \iff \mu(a) > 0, \qquad
\lbrace\lbrace\rbrace\rbrace(a) = 0, \qquad
\lbrace\lbrace x \rbrace\rbrace(a) = \begin{cases} 1 & a = x \\ 0 & a \neq x \end{cases}, \qquad
(\mu \uplus \nu)(a) = \mu(a) + \nu(a).$$

**Definition 2.2 (multiset extension, `multp`).** For a relation $R$ on $A$, the
relation $\mathrm{multp}\ R$ on $\mathcal{M}_{\mathrm{fin}}(A)$ relates $(M, N)$
iff

$$\exists I, J, K.\ \ N = I \uplus J \ \wedge\ M = I \uplus K \ \wedge\ J \neq \lbrace\lbrace\rbrace\rbrace \ \wedge\ (\forall k \in K.\ \exists j \in J.\ R(k, j)).$$

That is: $M$ arises from $N$ by removing a nonempty sub-multiset $J$ and inserting
$K$, every element of which is $R$-below some element of $J$.

**Proposition 2.3 (`wfp_multp`).** If $R$ is well-founded then so is
$\mathrm{multp}\ R$.

This is a library fact (`HOL-Library.Multiset`); it is the only property of
multisets the proof needs beyond the definitions.

## 3. The value order $(\mathsf{hord}, \prec)$

**Definition 3.1 (values, `hord`).** $\mathsf{hord}$ is the least set with

$$M \in \mathcal{M}_{\mathrm{fin}}(\mathsf{hord}) \implies H(M) \in \mathsf{hord},$$

where $H$ is the constructor. Put $\mathbf{0} = H(\lbrace\lbrace\rbrace\rbrace)$.
Each value equals $H(M)$ for a unique $M$; its elements are the *children*.

**Definition 3.2 (order, `hlt`).** On $\mathsf{hord}$,

$$H(M) \prec H(N) \iff \mathrm{multp}\ (\prec)\ M\ N.$$

(The elements compared by $\mathrm{multp}\ (\prec)$ are children, hence strictly
smaller values, so the recursion is well defined.)

**Proposition 3.3 (`wfP_hlt`).** $\prec$ is well-founded.

*Proof.* By structural induction on $\mathsf{hord}$, with Proposition 2.3 at the
inductive step. $\square$

**Example 3.4.** With $\mathbf{1} = H(\lbrace\lbrace \mathbf{0} \rbrace\rbrace)$,
$\mathbf{2} = H(\lbrace\lbrace \mathbf{0}, \mathbf{0} \rbrace\rbrace)$,
$\boldsymbol{\omega} = H(\lbrace\lbrace \mathbf{1} \rbrace\rbrace)$: take
$I = \lbrace\lbrace\rbrace\rbrace$, $J = \lbrace\lbrace \mathbf{1} \rbrace\rbrace$,
$K = \lbrace\lbrace \mathbf{0}, \mathbf{0} \rbrace\rbrace$ to get
$\mathbf{2} \prec \boldsymbol{\omega}$.

**Remark 3.5.** Under $H(\lbrace\lbrace a_1, \dots, a_k \rbrace\rbrace) \mapsto
\omega^{a_1} \oplus \cdots \oplus \omega^{a_k}$ (natural sum),
$(\mathsf{hord}, \prec) \cong (\varepsilon_0, <)$. Not used below.

## 4. The measure $o$ (`omap`)

**Definition 4.1 (`omap`).** With $\mathit{tw} = \mathrm{takeWhile}\ (\lambda x.\
a < x)\ \mathit{rest}$ and $\mathit{dw} = \mathrm{dropWhile}\ (\lambda x.\ a < x)\
\mathit{rest}$, and writing $o(\mathit{dw}) = H(D)$,

$$o([]) = H(\lbrace\lbrace\rbrace\rbrace), \qquad
o(a \mathbin{::} \mathit{rest}) = H\big(\lbrace\lbrace o(\mathit{tw}) \rbrace\rbrace \uplus D\big).$$

Equivalently $o$ is the *forest value*: position $i$ has parent
$\max\lbrace j \mid j < i \wedge S \mathbin{!} j < S \mathbin{!} i\rbrace$ (a root
if none); each tree contributes $H(\text{children})$ and a forest is combined by
$\uplus$. This parent rule coincides with the bad root.

**Computed values** (Isabelle): $o([0]) = H(\lbrace\lbrace \mathbf{0} \rbrace\rbrace) =
\mathbf{1}$; $o(\underbrace{[0, \dots, 0]}_{k}) = \mathbf{k}$; $o([0,1]) =
\boldsymbol{\omega}$; $o([0,1,1]) = \boldsymbol{\omega}^2$; $o([0,1,2]) =
\boldsymbol{\omega}^{\boldsymbol{\omega}}$.

## 5. Each step decreases $o$

**Lemma 5.1 (`omap_snoc_increases`).** $\quad o(C) \prec o(C \mathbin{@} [m]).$

*Proof.* Induction along the recursion of $o$: appending $m$ either adjoins a
top-level child $\mathbf{0}$ or enlarges one child; both are $\prec$-increases.
$\square$

**Proposition 5.2 (`m_drop0_decreases`).** $\quad S \neq [] \ \wedge\
\mathrm{last}\ S = 0 \implies o(\mathrm{butlast}\ S) \prec o(S).$

*Proof.* Write $o(\mathrm{butlast}\ S) = H(D)$. By `omap_snoc0`,
$$o(S) = o((\mathrm{butlast}\ S) \mathbin{@} [0]) = H(\lbrace\lbrace \mathbf{0} \rbrace\rbrace \uplus D),$$
and removing the single element $\mathbf{0}$ is a $\mathrm{multp}$-step. $\square$

For the bad step set $r = \mathrm{badroot}\ S$, $v = S \mathbin{!} r$,
$m = \mathrm{last}\ S$, $B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$. Then
$B = v \mathbin{::} B_t$ with $\forall x \in B_t.\ v < x$ (indeed $m \le x$), and
$S = (\mathrm{take}\ r\ S) \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$.

**Lemma 5.3 (`omap_rep`).** $\ \forall x \in B_t.\ v < x \implies$
$$o(\mathrm{concat}(\mathrm{replicate}\ k\ (v \mathbin{::} B_t))) = H\big(\underbrace{\lbrace\lbrace o(B_t), \dots, o(B_t) \rbrace\rbrace}_{k}\big).$$

**Lemma 5.4 (`omap_BfM`).** $\ \forall x \in B_t.\ v < x,\ \ v < m \implies$
$$o((v \mathbin{::} B_t) \mathbin{@} [m]) = H(\lbrace\lbrace o(B_t \mathbin{@} [m]) \rbrace\rbrace).$$

**Lemma 5.5 (`omap_core`).** $\ \forall x \in B_t.\ v < x,\ \ v < m \implies$
$$o(\mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))) \prec o((v \mathbin{::} B_t) \mathbin{@} [m]).$$

*Proof.* By Lemma 5.3 the left side is $H(\underbrace{\lbrace\lbrace o(B_t), \dots,
o(B_t) \rbrace\rbrace}_{k+1})$; by Lemma 5.4 the right side is $H(\lbrace\lbrace o(B_t
\mathbin{@} [m]) \rbrace\rbrace)$. Since $o(B_t) \prec o(B_t \mathbin{@} [m])$ (Lemma
5.1), one element is replaced by $k{+}1$ strictly smaller ones — a
$\mathrm{multp}$-step. $\square$

**Lemma 5.6 (`omap_BADCTX`).** For all $G$, under the hypotheses on $B_t$,
$$o(G \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))) \prec o(G \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]).$$

*Proof.* Induction on $\mathrm{length}\ G$. Peeling $G = g \mathbin{::} G'$, the
$o$-recursion splits $G' \mathbin{@} (\cdots)$ by $\mathrm{takeWhile} /
\mathrm{dropWhile}$ at $g$: either it recurses on a shorter context (congruence
under $H$), or, when $g$ sits below the bad part, it reduces to Lemma 5.5. Base
$G = []$ is Lemma 5.5. $\square$

**Proposition 5.7 (`m_bad_decreases`).** $\ S \neq [] \ \wedge\ 0 <
\mathrm{last}\ S \ \wedge\ \mathrm{badset}\ S \neq \emptyset \implies$
$$o((\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (\mathrm{drop}\ r\ (\mathrm{butlast}\ S)))) \prec o(S).$$

*Proof.* $\mathrm{badset}\ S$ is finite and nonempty, so $r$ is defined; rewriting
$S = (\mathrm{take}\ r\ S) \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$ reduces
the goal to Lemma 5.6. $\square$

## 6. Termination

**Theorem 6.1 (`m_step_decreases`).** $\quad S \to T \implies o(T) \prec o(S).$

*Proof.* Cases drop0 / bad are Propositions 5.2 / 5.7. $\square$

**Theorem 6.2 (`m_termination`).** $\quad \mathrm{wf}\ \lbrace (T, S) \mid S \to T\rbrace.$
Equivalently (`m_no_infinite_expansion`), no $\mathrm{Seq}$ has $\mathrm{Seq}(i)
\to \mathrm{Seq}(i{+}1)$ for all $i$.

*Proof.* $\lbrace (T, S) \mid S \to T\rbrace \subseteq o^{-1}(\prec)$ by Theorem
6.1, and $o^{-1}(\prec)$ is well-founded by Proposition 3.3 (inverse image of a
well-founded relation). $\square$

## 7. Correspondence with the Isabelle development

Statements: `prss_paper.thy` (`p_*`, `sorry`); proofs: `m_*` in
`prss_mechanized.thy`. Build: `isbman build -d . -v PRSS`.

| Object | Isabelle | source |
|---|---|---|
| $\mathrm{multp}$ (Def. 2.2) | `multp` | `HOL-Library.Multiset` |
| Prop. 2.3 | `wfp_multp` | `HOL-Library.Multiset` |
| $\mathsf{hord}$, $H$ | `datatype hord = H "hord multiset"` | [prss_ordinal.thy:16](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L16) |
| $\prec$ | `hlt` | [prss_ordinal.thy:20](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L20) |
| Prop. 3.3 | `wfP_hlt` | [prss_ordinal.thy:199](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L199) |
| $o$ (Def. 4.1) | `omap` | [prss_defs.thy:40](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L40) |
| $\mathrm{badset}$ / $\mathrm{badroot}$ | `badset` / `badroot` | [prss_defs.thy:67](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L67), [70](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L70) |
| $\to$ (Def. 1.1) | `step` (`drop0`, `bad`) | [prss_defs.thy:76](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L76) |
| Lemma 5.1 | `omap_snoc_increases` | [prss_mechanized.thy:106](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L106) |
| Prop. 5.2 | `m_drop0_decreases` | [prss_mechanized.thy:161](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L161) |
| Lemma 5.3 | `omap_rep` | [prss_mechanized.thy:204](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L204) |
| Lemma 5.4 | `omap_BfM` | [prss_mechanized.thy:228](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L228) |
| Lemma 5.5 | `omap_core` | [prss_mechanized.thy:246](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L246) |
| Lemma 5.6 | `omap_BADCTX` | [prss_mechanized.thy:303](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L303) |
| Prop. 5.7 | `m_bad_decreases` | [prss_mechanized.thy:426](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L426) |
| Thm. 6.1 | `m_step_decreases` | [prss_mechanized.thy:494](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L494) |
| Thm. 6.2 | `m_termination`, `m_no_infinite_expansion` | [prss_mechanized.thy:506](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L506), [515](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L515) |

---

Source: Koteitan, "Purely mathematical definition of BMS" (Googology Wiki);
Bashicu, "BASIC言語による巨大数のまとめ" (Googology Wiki, 2015).
