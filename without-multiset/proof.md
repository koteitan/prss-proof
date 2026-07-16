[← Back](../README.md) | [English](proof.md) | [Japanese](proof-ja.md)

# Termination of Primitive Sequence System (multiset-free)

We prove termination of Bashicu's *Primitive Sequence System*. Each sequence
$S \in \mathsf{list}(\mathbb{N})$ is mapped to a value $o(S)$ in a well-founded
order — concretely, a *Cantor normal form* term below $\varepsilon_0$ ordered
lexicographically — and each expansion step strictly decreases $o$.
Well-foundedness then forbids any infinite expansion. This is the
**multiset-free** development `prss_nomultiset.thy` (imports `Main` only;
§7 lists the correspondence). The companion
[with-multiset/proof.md](../with-multiset/proof.md) uses hereditarily finite
multisets instead; see the [README](../README.md) for why that version is
shorter.

A relation $R$ is *well-founded* when there is no infinite descending chain, i.e.
no $x_0, x_1, x_2, \dots$ with $R(x_{i+1}, x_i)$ for all $i$.

## 1. List operations

Finite lists over a set (here $\mathbb{N}$) are built from two *constructors*:
the empty list $[]$ and $\mathrm{cons}$ $a \mathbin{::} xs$ (prepend $a$ to
$xs$); every list is uniquely $[a_1, \dots, a_n] = a_1 \mathbin{::} \cdots
\mathbin{::} a_n \mathbin{::} []$. The operations used below, by recursion (the
conditional $P\ x$ in $\mathrm{takeWhile}/\mathrm{dropWhile}$ tests the head):

$\mathrm{length}$, append $xs \mathbin{@} ys$, $\mathrm{last}$ (final entry),
$\mathrm{butlast}$ (drop the final entry), $\mathrm{take}\ n$ / $\mathrm{drop}\ n$
(first $n$ / all but the first $n$), indexing $xs \mathbin{!} n$, and:

$$\mathrm{takeWhile}\ P\ (x \mathbin{::} xs) = \begin{cases} x \mathbin{::} \mathrm{takeWhile}\ P\ xs & P\ x \\ [] & \neg P\ x \end{cases}, \qquad
\mathrm{dropWhile}\ P\ (x \mathbin{::} xs) = \begin{cases} \mathrm{dropWhile}\ P\ xs & P\ x \\ x \mathbin{::} xs & \neg P\ x \end{cases},$$

$$\mathrm{concat}\ (xs \mathbin{::} xss) = xs \mathbin{@} \mathrm{concat}\ xss, \qquad
\mathrm{replicate}\ (n{+}1)\ x = x \mathbin{::} \mathrm{replicate}\ n\ x.$$

## 2. The expansion step

For a counter $n \in \mathbb{N}$ and activation function $f$ (Bashicu:
$f(n)=n^2$), with $X = \mathrm{length}\ S$ and $m = \mathrm{last}\ S$,

$$\mathrm{expand}([][n]) = n, \qquad
\mathrm{expand}(S[n]) =
\begin{cases}
\mathrm{expand}((\mathrm{butlast}\ S)[f(n)]) & m = 0,\\
\mathrm{expand}((G \mathbin{@} \underbrace{B \mathbin{@} \cdots \mathbin{@} B}_{f(n)+1})[f(n)]) & m > 0,
\end{cases}$$

$$r = \max\lbrace p \mid p < X-1 \ \wedge\ S \mathbin{!} p < m\rbrace, \qquad
G = \mathrm{take}\ r\ S, \qquad
B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S).$$

**Definition 2.1 (step relation, `step`).** Drop the counter and $f$, and let the
copy count $k \in \mathbb{N}$ be arbitrary. Define $S \to T$ inductively by

$$\frac{S \neq []\quad m = 0}{S \to \mathrm{butlast}\ S}\ (\mathrm{drop0}),
\qquad
\frac{S \neq []\quad 0 < m \quad \mathrm{badset}\ S \neq \emptyset}
{S \to (\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k+1)\ B)}\ (\mathrm{bad}),$$

with $r = \mathrm{badroot}\ S$, $B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$ and

$$\mathrm{badset}\ S = \lbrace p \mid p < \mathrm{length}\ S - 1 \ \wedge\ S \mathbin{!} p < m\rbrace,
\qquad \mathrm{badroot}\ S = \max(\mathrm{badset}\ S).$$

Rule $\mathrm{drop0}$ is the $m = 0$ branch of $\mathrm{expand}$, rule
$\mathrm{bad}$ (for $k = f(n)$) is the $m > 0$ branch; $\to$ is the sequence part
of one $\mathrm{expand}$ step. Termination of $\mathrm{expand}$ for any $f, n$
reduces to nonexistence of an infinite chain $S^{(0)} \to S^{(1)} \to \cdots$.

## 3. Cantor normal forms and their order

**Definition 3.1 (terms, `ord`).** Ordinals below $\varepsilon_0$ are the binary
trees

$$\mathsf{ord} ::= Z \ \mid\ E\ a\ b \qquad (a, b \in \mathsf{ord}),$$

read as $Z = 0$ and $E\ a\ b = \omega^{a} + b$. The *leading exponent*
$\mathrm{lead}$ returns the exponent of the leading (largest) power of a term:

$$\mathrm{lead}\ Z = Z, \qquad \mathrm{lead}\ (E\ a\ b) = a.$$

E.g. for $\omega^{\omega} + \omega^{3} + 5 = E\ \omega\ (\omega^{3}+5)$ we have
$\mathrm{lead} = \omega$, and for its tail $\omega^{3}+5$ we have $\mathrm{lead} = 3$.

**Definition 3.2 (order, `olt` / $\prec$).** The recursive lexicographic order:

$$Z \prec E\ a\ b, \qquad
E\ a\ b \prec E\ c\ d \iff a \prec c \ \vee\ (a = c \ \wedge\ b \prec d),$$

and nothing is $\prec Z$. Write $x \preceq y$ for $x \prec y \vee x = y$. This is
a linear order (`olt_trans`, `olt_total`).

**Definition 3.3 (normal form, `cnf`).** A term is in *Cantor normal form* when
the exponents are non-increasing left to right and hereditarily normal:

$$\mathrm{cnf}\ Z, \qquad \mathrm{cnf}\ (E\ a\ b) \iff \mathrm{cnf}\ a \ \wedge\ \mathrm{cnf}\ b \ \wedge\ (b = Z \ \vee\ \mathrm{lead}\ b \preceq a).$$

The last condition $\mathrm{lead}\ b \preceq a$ says "the leading exponent of the
tail $b$ does not exceed the current exponent $a$", i.e. it enforces the
exponents being non-increasing left to right, one step at a time.

(Some ordering is essential: on *non*-CNF terms $\prec$ is **not** well-founded —
e.g. $E (E Z Z) Z \succ E Z (E (E Z Z) Z) \succ \cdots$ is an infinite descent of
"ascending-exponent" terms. CNF rules this out.)

**Proposition 3.4 (`wfP_R`).** $\prec$ is well-founded on CNF terms; i.e. the
relation

$$R\ x\ y \iff \mathrm{cnf}\ x \ \wedge\ \mathrm{cnf}\ y \ \wedge\ x \prec y$$

is well-founded.

*Proof.* Let $\mathrm{Acc}\ x$ denote $R$-accessibility (`accp R`): the **least**
predicate satisfying

$$\mathrm{Acc}\ x \iff (\forall y.\ R\ y\ x \Rightarrow \mathrm{Acc}\ y).$$

Since $\mathrm{wfP}\ R$ is equivalent to "$\mathrm{Acc}\ x$ for all $x$"
(`accp_wfpI`), it suffices to prove **$\mathrm{Acc}\ x$ for every $x$**. We
proceed in four steps.

**Lemma A (`accp_R_Z`).** $\mathrm{Acc}\ Z$.
No $x$ satisfies $x \prec Z$ (`not_olt_Z`), hence none satisfies $R\ x\ Z$; the
accessibility condition holds vacuously, so $\mathrm{Acc}\ Z$.

**Lemma B (`accp_R_E`).** If $\mathrm{Acc}\ a$ and $\mathrm{cnf}\ a$, then for
every $b$ with $\mathrm{cnf}\ (E\ a\ b)$ and $\mathrm{Acc}\ b$ we have
$\mathrm{Acc}\ (E\ a\ b)$.

By well-founded induction on $\mathrm{Acc}\ a$. The induction hypothesis
$\mathrm{IH}_a$: the claim holds for every $a'$ with $R\ a'\ a$ (i.e.
$\mathrm{cnf}\ a'$, $\mathrm{cnf}\ a$, $a' \prec a$). First an auxiliary fact:

$$\text{(tail)}\qquad \mathrm{cnf}\ d \ \wedge\ \mathrm{lead}\ d \prec a \ \Longrightarrow\ \mathrm{Acc}\ d.$$

By structural induction on $d$.
If $d = Z$, use Lemma A.
If $d = E\ e\ d'$, then $\mathrm{cnf}$ gives $\mathrm{cnf}\ e$, $\mathrm{cnf}\ d'$,
$(d' = Z \vee \mathrm{lead}\ d' \preceq e)$. From $\mathrm{lead}\ d = e \prec a$ we
get $R\ e\ a$. Also $\mathrm{lead}\ d' \prec a$: if $d' = Z$ then
$\mathrm{lead}\ d' = Z \prec a$ (here $a \neq Z$ since $e \prec a$); otherwise
$\mathrm{lead}\ d' \preceq e \prec a$ by transitivity (`ole_olt_trans`). The
structural IH on $d'$ gives $\mathrm{Acc}\ d'$. Applying $\mathrm{IH}_a$ to
$R\ e\ a$ yields "Lemma B for $e$", so $\mathrm{cnf}\ (E\ e\ d')$ and
$\mathrm{Acc}\ d'$ give $\mathrm{Acc}\ (E\ e\ d') = \mathrm{Acc}\ d$.

Now the body, by well-founded induction on $\mathrm{Acc}\ b$. The induction
hypothesis $\mathrm{IH}_b$: $\mathrm{Acc}\ (E\ a\ b')$ for every $b'$ with
$R\ b'\ b$. By the definition of accessibility, $\mathrm{Acc}\ (E\ a\ b)$ follows
once $\mathrm{Acc}\ z$ is shown for every $z$ with $R\ z\ (E\ a\ b)$. If
$z = Z$, use Lemma A. If $z = E\ c\ d$, then $\mathrm{cnf}\ c$, $\mathrm{cnf}\ d$,
$(d = Z \vee \mathrm{lead}\ d \preceq c)$, and $z \prec E\ a\ b$ means

$$c \prec a \qquad\vee\qquad (c = a \ \wedge\ d \prec b).$$

- If $c \prec a$: as in (tail), $\mathrm{lead}\ d \prec a$, so (tail) gives
  $\mathrm{Acc}\ d$. Also $R\ c\ a$, so $\mathrm{IH}_a$ yields "Lemma B for $c$";
  with $\mathrm{cnf}\ (E\ c\ d)$ and $\mathrm{Acc}\ d$ this gives
  $\mathrm{Acc}\ (E\ c\ d) = \mathrm{Acc}\ z$.
- If $c = a \ \wedge\ d \prec b$: then $R\ d\ b$, so $\mathrm{IH}_b$ gives
  $\mathrm{Acc}\ (E\ a\ d) = \mathrm{Acc}\ z$.

Hence $\mathrm{Acc}\ (E\ a\ b)$, proving Lemma B.

**Lemma C (`accp_R_all`).** $\mathrm{cnf}\ x \Rightarrow \mathrm{Acc}\ x$.
By structural induction on $x$. For $x = Z$, Lemma A. For $x = E\ a\ b$, the IH
gives $\mathrm{Acc}\ a$, $\mathrm{Acc}\ b$ from $\mathrm{cnf}\ a$, $\mathrm{cnf}\ b$,
and Lemma B (for exponent $a$) gives $\mathrm{Acc}\ (E\ a\ b)$.

**Lemma D (`accp_R_any`).** $\mathrm{Acc}\ x$ for every $x$.
If $\mathrm{cnf}\ x$, use Lemma C. If $\neg \mathrm{cnf}\ x$, then $R\ z\ x$
requires $\mathrm{cnf}\ x$, so $x$ has no $R$-predecessor and is vacuously
accessible.

By Lemma D, $\mathrm{Acc}\ x$ holds for all $x$, so $\mathrm{wfP}\ R$ by
`accp_wfpI`. $\square$

## 4. The measure $o$ (`omap`)

**Definition 4.1 (insertion, `ins`).** $\mathrm{ins}\ e\ y$ inserts the single
term $\omega^{e}$ into a CNF $y$ at its sorted position:

$$\mathrm{ins}\ e\ Z = E\ e\ Z, \qquad
\mathrm{ins}\ e\ (E\ a\ b) = \begin{cases} E\ e\ (E\ a\ b) & a \prec e \\ E\ a\ (\mathrm{ins}\ e\ b) & \neg (a \prec e). \end{cases}$$

It preserves normal form (`cnf_ins`) and commutes (`ins_comm`:
$\mathrm{ins}\ e\ (\mathrm{ins}\ f\ y) = \mathrm{ins}\ f\ (\mathrm{ins}\ e\ y)$).

**Definition 4.2 (measure, `omap`).** Read the sequence from the left; the first
entry $a$ contributes the term $\omega^{o(\mathit{inside})}$ where
$\mathit{inside}$ is the maximal following run of entries $> a$ (its descendant
forest), inserted into the value of the rest:

$$o([]) = Z, \qquad o(a \mathbin{::} \mathit{rest}) = \mathrm{ins}\ \big(o(\mathit{tw})\big)\ \big(o(\mathit{dw})\big),$$
$$\mathit{tw} = \mathrm{takeWhile}\ (\lambda x.\ a < x)\ \mathit{rest}, \qquad \mathit{dw} = \mathrm{dropWhile}\ (\lambda x.\ a < x)\ \mathit{rest}.$$

**Proposition 4.3 (`cnf_omap`).** $\mathrm{cnf}\ (o(S))$ for every $S$. (So $o$
always lands in the well-founded domain of Proposition 3.4.)

*Proof.* Induction following $o$, using `cnf_ins`. $\square$

## 5. Each step decreases the measure

**Lemma 5.1 (`olt_ins_self`).** $\quad y \prec \mathrm{ins}\ e\ y.$ Inserting a
term strictly increases the value.

**Lemma 5.2 (`omap_snoc0`).** $\quad o(P \mathbin{@} [0]) = \mathrm{ins}\ Z\ (o(P)).$
A trailing $0$ inserts the least term $\omega^{0}$. (Proof by induction, using
`ins_comm`.)

**Proposition 5.3 (drop-zero, `m_drop0`).** If $S \neq []$ and
$\mathrm{last}\ S = 0$, then $o(\mathrm{butlast}\ S) \prec o(S)$.

*Proof.* $S = \mathrm{butlast}\ S \mathbin{@} [0]$, so $o(S) = \mathrm{ins}\ Z\ (o(\mathrm{butlast}\ S))$
by 5.2, and $o(\mathrm{butlast}\ S) \prec o(S)$ by 5.1. $\square$

**Lemma 5.4 (`ins_mono2`).** If $\mathrm{cnf}\ y$, $\mathrm{cnf}\ y'$ and
$y \prec y'$, then $\mathrm{ins}\ e\ y \prec \mathrm{ins}\ e\ y'$.

**Lemma 5.5 (`omap_snoc_increase`).** $\quad o(C) \prec o(C \mathbin{@} [m])$ for
every $m$. (Induction on $o$; the recursive case uses Lemma 5.4.)

For the bad step, write $S = G \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$
where $r = \mathrm{badroot}\ S$, $v = S \mathbin{!} r$, $m = \mathrm{last}\ S$,
$B = v \mathbin{::} B_t = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$. Maximality of
$r$ gives $\forall x \in B_t.\ m \le x$, hence $v < x$, and $v < m$.

**Lemma 5.6 (`omap_rep`).** If $\forall x \in B_t.\ v < x$, then $k$ copies of
$B$ give $k$ equal terms:
$$o\big(\mathrm{concat}(\mathrm{replicate}\ k\ (v \mathbin{::} B_t))\big) = (\mathrm{ins}\ (o(B_t)))^{k}\ Z.$$

**Lemma 5.7 (`omap_BfM`).** If $\forall x \in B_t.\ v < x$ and $v < m$, the
appended $m$ falls inside $v$'s subtree, giving a single term:
$$o\big((v \mathbin{::} B_t) \mathbin{@} [m]\big) = E\ \big(o(B_t \mathbin{@} [m])\big)\ Z.$$

**Lemma 5.8 (core decrease, `omap_core`).** Under the same hypotheses,
$$o\big(\mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))\big) \prec o\big((v \mathbin{::} B_t) \mathbin{@} [m]\big).$$

*Proof.* The left side is $(\mathrm{ins}\ \beta)^{k+1} Z$ with $\beta = o(B_t)$
(5.6) — a CNF all of whose exponents equal $\beta$; the right side is
$E\ \gamma\ Z$ with $\gamma = o(B_t \mathbin{@} [m])$ (5.7). Since
$\beta \prec \gamma$ (5.5), every such left-hand term has leading exponent
$\beta \prec \gamma$, so it is $\prec E\ \gamma\ Z$ (`funpow_ins_lt`). $\square$

**Lemma 5.9 (with context, `omap_BADCTX`).** For every good part $G$,
$$o\big(G \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))\big) \prec o\big(G \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]\big).$$

*Proof.* Induction on $\mathrm{length}\ G$. Peeling $G = g \mathbin{::} G'$, the
recursion of $o$ either confines the comparison inside $G$ (reducing to a shorter
context, congruence via Lemma 5.4) or, once $g$ sits below the bad part, reduces
to the core (Lemma 5.8). Base $G = []$ is Lemma 5.8. $\square$

**Proposition 5.10 (bad step, `m_bad`).** If $S \neq []$, $\mathrm{last}\ S > 0$
and $\mathrm{badset}\ S \neq \emptyset$, then for every $k$
$$o\big((\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (\mathrm{drop}\ r\ (\mathrm{butlast}\ S)))\big) \prec o(S).$$

*Proof.* $\mathrm{badset}\ S$ is finite and nonempty, so $r$ is well defined;
rewriting $S = (\mathrm{take}\ r\ S) \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$
reduces the goal to Lemma 5.9. $\square$

## 6. Termination

**Theorem 6.1 (`m_step_decreases`).** $\quad S \to T \implies o(T) \prec o(S).$

*Proof.* The two cases are Propositions 5.3 and 5.10. $\square$

**Theorem 6.2 (`m_termination`).** $\quad \mathrm{wf}\ \lbrace (T, S) \mid S \to T\rbrace.$
Equivalently (`m_no_infinite_expansion`), no $\mathrm{Seq}$ has $\mathrm{Seq}(i)
\to \mathrm{Seq}(i{+}1)$ for all $i$.

*Proof.* By Theorem 6.1 and $\mathrm{cnf}\ (o(\cdot))$ (Prop. 4.3),
$\lbrace (T, S) \mid S \to T\rbrace \subseteq o^{-1}(R)$; and $o^{-1}(R)$ is
well-founded by Proposition 3.4 (inverse image of a well-founded relation).
$\square$

## 7. Correspondence with the Isabelle development

All facts are in [`prss_nomultiset.thy`](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy)
(`imports Main`; no `HOL-Library.Multiset`). Build with `isbman build -d . -v PRSS`.

| Object | Isabelle | source |
|---|---|---|
| $\mathsf{ord}$ ($Z$, $E\ a\ b$) | `datatype ord = Z \| E ord ord` | [prss_nomultiset.thy:14](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L14) |
| $\prec$ | `olt` (`<o`) | [prss_nomultiset.thy:18](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L18) |
| Def. 3.3 | `cnf` | [prss_nomultiset.thy:34](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L34) |
| Prop. 3.4 | `wfP_R` | [prss_nomultiset.thy:235](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L235) |
| Def. 4.1 | `ins` | [prss_nomultiset.thy:240](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L240) |
| $o$ (Def. 4.2) | `omap` | [prss_nomultiset.thy:332](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L332) |
| Prop. 4.3 | `cnf_omap` | [prss_nomultiset.thy:342](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L342) |
| $\mathrm{badset}$ / $\mathrm{badroot}$ | `badset` / `badroot` | [prss_nomultiset.thy:780](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L780), [783](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L783) |
| $\to$ (Def. 2.1) | `step` (`drop0`, `bad`) | [prss_nomultiset.thy:844](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L844) |
| Lemma 5.1 | `olt_ins_self` | [prss_nomultiset.thy:353](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L353) |
| Lemma 5.2 | `omap_snoc0` | [prss_nomultiset.thy:368](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L368) |
| Prop. 5.3 | `m_drop0` | [prss_nomultiset.thy:392](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L392) |
| Lemma 5.4 | `ins_mono2` | [prss_nomultiset.thy:415](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L415) |
| Lemma 5.5 | `omap_snoc_increase` | [prss_nomultiset.thy:494](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L494) |
| Lemma 5.6 | `omap_rep` | [prss_nomultiset.thy:562](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L562) |
| Lemma 5.7 | `omap_BfM` | [prss_nomultiset.thy:584](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L584) |
| Lemma 5.8 | `omap_core` | [prss_nomultiset.thy:625](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L625) |
| Lemma 5.9 | `omap_BADCTX` | [prss_nomultiset.thy:661](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L661) |
| Prop. 5.10 | `m_bad` | [prss_nomultiset.thy:786](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L786) |
| Thm. 6.1 | `m_step_decreases` | [prss_nomultiset.thy:851](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L851) |
| Thm. 6.2 | `m_termination`, `m_no_infinite_expansion` | [prss_nomultiset.thy:863](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L863), [878](https://github.com/koteitan/prss-proof/blob/main/without-multiset/prss_nomultiset.thy#L878) |

---

Source: Koteitan, "[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)" (Googology Wiki); Bashicu, "[BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81)" (Googology Wiki, 2015).
