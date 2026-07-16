[← 戻る](../README-ja.md) | [English](proof.md) | [Japanese](proof-ja.md)

# 原始数列システムの停止性

バシク氏の*原始数列システム*の停止性を証明する。各数列 $S \in \mathsf{list}(\mathbb{N})$ を
整礎順序 $(\mathsf{hord}, \prec)$ の値 $o(S)$ に写し、展開の各ステップが $o$ を真に減少させる
ことを示す。整礎性により無限展開は排除される。Isabelle/HOL で形式化している（対応は §8）。
これは**多重集合**版で、$\mathsf{hord}$ は $\varepsilon_0$ 未満の順序数を遺伝的有限多重集合で
表したもの。対になる [without-multiset/proof-ja.md](../without-multiset/proof-ja.md) は
カントール標準形と `imports Main` のみで同じ定理を証明している。

関係 $R$ が*整礎*とは、無限の下降列が存在しないこと、すなわち、すべての $i$ で
$R(x_{i+1}, x_i)$ となる $x_0, x_1, x_2, \dots$ が存在しないことをいう。

## 1. リスト操作

ある集合（ここでは $\mathbb{N}$）上の有限リストは、2つの*構成子*から作られる：空リスト $[]$ と
cons $a \mathbin{::} xs$（$xs$ の先頭に $a$ を付ける）。どのリストもこの形で一意に表され、
例えば $[a, b, c] = a \mathbin{::} (b \mathbin{::} (c \mathbin{::} []))$、$[x] = x \mathbin{::} []$。
§4 の $H$ と同様、$[]$ と $\mathbin{::}$ は基本（構成子）であって方程式では定義しない。以下の操作は
これらを用いて再帰で定める（$\mathrm{takeWhile}/\mathrm{dropWhile}$ の条件 $P\ x$ は先頭を判定する）。

$\mathrm{length}\ xs$ — 要素の個数：
$$\mathrm{length}\ [] = 0, \qquad \mathrm{length}\ (x \mathbin{::} xs) = 1 + \mathrm{length}\ xs.$$

$xs \mathbin{@} ys$ — *append*（連結）：$xs$ の後ろに $ys$ をつなぐ：
$$[] \mathbin{@} ys = ys, \qquad (x \mathbin{::} xs) \mathbin{@} ys = x \mathbin{::} (xs \mathbin{@} ys).$$

$\mathrm{last}\ xs$ — 末尾の要素：
$$\mathrm{last}\ [x] = x, \qquad \mathrm{last}\ (x \mathbin{::} y \mathbin{::} ys) = \mathrm{last}\ (y \mathbin{::} ys).$$

$\mathrm{butlast}\ xs$ — 末尾の要素を除いたリスト（$xs \neq []$ なら $xs = \mathrm{butlast}\ xs \mathbin{@} [\mathrm{last}\ xs]$）：
$$\mathrm{butlast}\ [] = [], \quad \mathrm{butlast}\ [x] = [], \quad \mathrm{butlast}\ (x \mathbin{::} y \mathbin{::} ys) = x \mathbin{::} \mathrm{butlast}\ (y \mathbin{::} ys).$$

$\mathrm{take}\ n\ xs$ — 先頭 $n$ 要素：
$$\mathrm{take}\ 0\ xs = [], \quad \mathrm{take}\ n\ [] = [], \quad \mathrm{take}\ (n{+}1)\ (x \mathbin{::} xs) = x \mathbin{::} \mathrm{take}\ n\ xs.$$

$\mathrm{drop}\ n\ xs$ — 先頭 $n$ 要素を除いたリスト（$\mathrm{take}\ n\ xs \mathbin{@} \mathrm{drop}\ n\ xs = xs$）：
$$\mathrm{drop}\ 0\ xs = xs, \quad \mathrm{drop}\ n\ [] = [], \quad \mathrm{drop}\ (n{+}1)\ (x \mathbin{::} xs) = \mathrm{drop}\ n\ xs.$$

$xs \mathbin{!} n$ — 第 $n$ 要素（$0$ から数える）：
$$(x \mathbin{::} xs) \mathbin{!} 0 = x, \qquad (x \mathbin{::} xs) \mathbin{!} (n{+}1) = xs \mathbin{!} n.$$

$\mathrm{takeWhile}\ P\ xs$ — 要素がすべて $P$ をみたす最長の先頭部分：
$$\mathrm{takeWhile}\ P\ [] = [], \qquad \mathrm{takeWhile}\ P\ (x \mathbin{::} xs) = \begin{cases} x \mathbin{::} \mathrm{takeWhile}\ P\ xs & P\ x \\ [] & \neg P\ x \end{cases}.$$

$\mathrm{dropWhile}\ P\ xs$ — その先頭部分の後ろの残り：
$$\mathrm{dropWhile}\ P\ [] = [], \qquad \mathrm{dropWhile}\ P\ (x \mathbin{::} xs) = \begin{cases} \mathrm{dropWhile}\ P\ xs & P\ x \\ x \mathbin{::} xs & \neg P\ x \end{cases}.$$

$\mathrm{concat}\ xss$ — リストのリストを1本のリストに平坦化：
$$\mathrm{concat}\ [] = [], \qquad \mathrm{concat}\ (xs \mathbin{::} xss) = xs \mathbin{@} \mathrm{concat}\ xss.$$

$\mathrm{replicate}\ n\ x$ — $x$ を $n$ 個並べたリスト：
$$\mathrm{replicate}\ 0\ x = [], \qquad \mathrm{replicate}\ (n{+}1)\ x = x \mathbin{::} \mathrm{replicate}\ n\ x.$$

## 2. 多重集合

多重集合は集合に似ているが、重複を数え、順序を無視する。二重波括弧で書く。例えば
$\lbrace\lbrace 1, 1, 4 \rbrace\rbrace$ は $1$ を2個、$4$ を1個もち、
$\lbrace\lbrace 4, 1, 1 \rbrace\rbrace$ に等しく、$\lbrace\lbrace 1, 4 \rbrace\rbrace$（$1$ は
1個）とは異なる。空のものは $\lbrace\lbrace\rbrace\rbrace$ である。集合が指示関数
$\chi : A \to \lbrace 0, 1\rbrace$ で与えられるのに対し、多重集合はその値域を $\mathbb{N}$ に
拡げ、所属の有無の代わりに重複度を記録したものである。形式的な定義は下記である。

**定義 2.1（有限多重集合）。** 集合 $A$ 上の*多重集合*とは写像 $\mu : A \to \mathbb{N}$ で、
$\mu(a)$ を $a$ の*重複度*という。非零の重複度が有限個のとき*有限*といい、

$$\mathcal{M}_{\mathrm{fin}}(A) = \lbrace \mu : A \to \mathbb{N} \ \mid\ \lvert \lbrace a \in A : \mu(a) > 0\rbrace \rvert < \infty \rbrace.$$

所属・空多重集合・単元多重集合・和 $\uplus$ は

$$a \in \mu \iff \mu(a) > 0, \qquad
\lbrace\lbrace\rbrace\rbrace(a) = 0, \qquad
\lbrace\lbrace x \rbrace\rbrace(a) = \begin{cases} 1 & a = x \\ 0 & a \neq x \end{cases}, \qquad
(\mu \uplus \nu)(a) = \mu(a) + \nu(a).$$

**定義 2.2（多重集合拡大, `multp`）。** $A$ 上の関係 $R$ に対し、
$\mathcal{M}_{\mathrm{fin}}(A)$ 上の関係 $\mathrm{multp}\ R$ を、$(M, N)$ について

$$\exists I, J, K.\ \ N = I \uplus J \ \wedge\ M = I \uplus K \ \wedge\ J \neq \lbrace\lbrace\rbrace\rbrace \ \wedge\ (\forall k \in K.\ \exists j \in J.\ R(k, j))$$

のとき成り立つと定める。すなわち $M$ は $N$ から空でない部分多重集合 $J$ を除き、$J$ の
いずれかの元より $R$-小な元からなる $K$ を加えて得られる。

**命題 2.3（`wfp_multp`）。** $R$ が整礎ならば $\mathrm{multp}\ R$ も整礎である。

これはライブラリの事実（`HOL-Library.Multiset`）であり、本証明が定義以外に必要とする
多重集合の唯一の性質である。

## 3. 展開ステップ

カウンタ $n \in \mathbb{N}$ と活性化関数 $f$（バシク氏は $f(n)=n^2$）に対し、
$X = \mathrm{length}\ S$、$m = \mathrm{last}\ S$ とおくと、

$$\mathrm{expand}([][n]) = n, \qquad
\mathrm{expand}(S[n]) =
\begin{cases}
\mathrm{expand}((\mathrm{butlast}\ S)[f(n)]) & m = 0,\\[2pt]
\mathrm{expand}((G \mathbin{@} \underbrace{B \mathbin{@} \cdots \mathbin{@} B}_{f(n)+1})[f(n)]) & m > 0,
\end{cases}$$

$$r = \max\lbrace p \mid p < X-1 \ \wedge\ S \mathbin{!} p < m\rbrace, \qquad
G = \mathrm{take}\ r\ S, \qquad
B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S).$$

**定義 3.1（ステップ関係, `step`）。** カウンタと $f$ を除き、コピー数 $k \in \mathbb{N}$ を
任意とする。$S \to T$ を次の帰納規則で定める。

$$\frac{S \neq []\quad m = 0}{S \to \mathrm{butlast}\ S}\ (\mathrm{drop0}),
\qquad
\frac{S \neq []\quad 0 < m \quad \mathrm{badset}\ S \neq \emptyset}
{S \to (\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k+1)\ B)}\ (\mathrm{bad}),$$

$r = \mathrm{badroot}\ S$、$B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$、

$$\mathrm{badset}\ S = \lbrace p \mid p < \mathrm{length}\ S - 1 \ \wedge\ S \mathbin{!} p < m\rbrace,
\qquad \mathrm{badroot}\ S = \max(\mathrm{badset}\ S).$$

規則 $\mathrm{drop0}$ は $\mathrm{expand}$ の $m = 0$ の分岐、規則 $\mathrm{bad}$（$k = f(n)$ の場合）は
$m > 0$ の分岐に対応する。$\to$ は $\mathrm{expand}$ の1ステップの数列部分である。

任意の $f, n$ に対する $\mathrm{expand}$ の停止性は、無限連鎖 $S^{(0)} \to S^{(1)} \to \cdots$
が存在しないことに帰着する。展開実行の数列部分はそのような連鎖だからである。

## 4. 値の順序 $(\mathsf{hord}, \prec)$

**定義 4.1（値, `hord`）。** $\mathsf{hord}$ を、全単射

$$H : \mathcal{M}_{\mathrm{fin}}(\mathsf{hord}) \to \mathsf{hord}$$

を備えた集合とする。その逆を $H^{-1} : \mathsf{hord} \to \mathcal{M}_{\mathrm{fin}}(\mathsf{hord})$（Isabelle の `un_H`）と書く。すなわち

$$H^{-1}(H(M)) = M \qquad\text{かつ}\qquad H(H^{-1}(v)) = v.$$

（このような集合は $X \mapsto \mathcal{M}_{\mathrm{fin}}(X)$ の始代数として存在し、同型を除いて
一意である。これが Isabelle の `datatype`。）$\mathbf{0} = H(\lbrace\lbrace\rbrace\rbrace)$ とおく。
$v$ の*子*とは $H^{-1}(v)$ の要素である。

**定義 4.2（順序, `hlt`）。** $\mathsf{hord}$ 上で

$$H(M) \prec H(N) \iff \mathrm{multp}\ (\prec)\ M\ N.$$

（$\mathrm{multp}\ (\prec)$ が比較する元は子、すなわちより小さい値なので、この再帰は整合的に
定まる。）

**命題 4.3（`wfP_hlt`）。** $\prec$ は整礎である。

*証明.* $\mathsf{hord}$ に関する構造帰納法。帰納段で命題 2.3 を用いる。$\square$

**例 4.4.** $\mathbf{1} = H(\lbrace\lbrace \mathbf{0} \rbrace\rbrace)$、
$\mathbf{2} = H(\lbrace\lbrace \mathbf{0}, \mathbf{0} \rbrace\rbrace)$、
$\boldsymbol{\omega} = H(\lbrace\lbrace \mathbf{1} \rbrace\rbrace)$ とおくと、$I = \lbrace\lbrace\rbrace\rbrace$、
$J = \lbrace\lbrace \mathbf{1} \rbrace\rbrace$、$K = \lbrace\lbrace \mathbf{0}, \mathbf{0} \rbrace\rbrace$ により
$\mathbf{2} \prec \boldsymbol{\omega}$。

**注意 4.5.** $H(\lbrace\lbrace a_1, \dots, a_k \rbrace\rbrace) \mapsto \omega^{a_1} \oplus \cdots \oplus
\omega^{a_k}$（自然和）により $(\mathsf{hord}, \prec) \cong (\varepsilon_0, <)$。以下では
用いない。

## 5. 測度 $o$ (`omap`)

**定義 5.1（`omap`）。** $\mathit{tw} = \mathrm{takeWhile}\ (\lambda x.\ a < x)\ \mathit{rest}$、
$\mathit{dw} = \mathrm{dropWhile}\ (\lambda x.\ a < x)\ \mathit{rest}$ とし、
$o(\mathit{dw}) = H(D)$ と書くと、

$$o([]) = H(\lbrace\lbrace\rbrace\rbrace), \qquad
o(a \mathbin{::} \mathit{rest}) = H\big(\lbrace\lbrace o(\mathit{tw}) \rbrace\rbrace \uplus D\big).$$

同値に $o$ は*森の値*である：位置 $i$ の親は
$\max\lbrace j \mid j < i \wedge S \mathbin{!} j < S \mathbin{!} i\rbrace$（無ければ根）、各木は
$H(\text{子たち})$ を与え、森は $\uplus$ で合わせる。この親の規則は bad root と一致する。

**計算値**（Isabelle）：$o([0]) = H(\lbrace\lbrace \mathbf{0} \rbrace\rbrace) = \mathbf{1}$；
$o(\underbrace{[0, \dots, 0]}_{k}) = \mathbf{k}$；$o([0,1]) = \boldsymbol{\omega}$；
$o([0,1,1]) = \boldsymbol{\omega}^2$；$o([0,1,2]) = \boldsymbol{\omega}^{\boldsymbol{\omega}}$。

## 6. 各ステップは $o$ を減少させる

**補題 6.1（`omap_snoc_increases`）。** $\quad o(C) \prec o(C \mathbin{@} [m]).$

*証明.* $o$ の再帰に沿う帰納法。末尾に $m$ を加えると、トップレベルの子 $\mathbf{0}$ が増えるか、
ある子が大きくなるかのいずれかで、どちらも $\prec$-増加。$\square$

**命題 6.2（`m_drop0_decreases`）。** $\quad S \neq [] \ \wedge\ \mathrm{last}\ S = 0 \implies
o(\mathrm{butlast}\ S) \prec o(S).$

*証明.* $o(\mathrm{butlast}\ S) = H(D)$ と書く。`omap_snoc0` により
$$o(S) = o((\mathrm{butlast}\ S) \mathbin{@} [0]) = H(\lbrace\lbrace \mathbf{0} \rbrace\rbrace \uplus D),$$
1元 $\mathbf{0}$ の削除は $\mathrm{multp}$-ステップ。$\square$

bad ステップでは $r = \mathrm{badroot}\ S$、$v = S \mathbin{!} r$、$m = \mathrm{last}\ S$、
$B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$ とおく。すると $B = v \mathbin{::} B_t$ で
$\forall x \in B_t.\ v < x$（実際 $m \le x$）、かつ
$S = (\mathrm{take}\ r\ S) \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$。

**補題 6.3（`omap_rep`）。** $\ \forall x \in B_t.\ v < x \implies$
$$o(\mathrm{concat}(\mathrm{replicate}\ k\ (v \mathbin{::} B_t))) = H\big(\underbrace{\lbrace\lbrace o(B_t), \dots, o(B_t) \rbrace\rbrace}_{k}\big).$$

**補題 6.4（`omap_BfM`）。** $\ \forall x \in B_t.\ v < x,\ \ v < m \implies$
$$o((v \mathbin{::} B_t) \mathbin{@} [m]) = H(\lbrace\lbrace o(B_t \mathbin{@} [m]) \rbrace\rbrace).$$

**補題 6.5（`omap_core`）。** $\ \forall x \in B_t.\ v < x,\ \ v < m \implies$
$$o(\mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))) \prec o((v \mathbin{::} B_t) \mathbin{@} [m]).$$

*証明.* 補題 6.3 より左辺は $H(\underbrace{\lbrace\lbrace o(B_t), \dots, o(B_t) \rbrace\rbrace}_{k+1})$、
補題 6.4 より右辺は $H(\lbrace\lbrace o(B_t \mathbin{@} [m]) \rbrace\rbrace)$。$o(B_t) \prec o(B_t \mathbin{@} [m])$
（補題 6.1）なので、1元を真に小さい $k{+}1$ 元で置き換える $\mathrm{multp}$-ステップ。$\square$

**補題 6.6（`omap_BADCTX`）。** $B_t$ への仮定の下、任意の $G$ について
$$o(G \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))) \prec o(G \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]).$$

*証明.* $\mathrm{length}\ G$ に関する帰納法。$G = g \mathbin{::} G'$ を剥がすと、$o$ の再帰は
$G' \mathbin{@} (\cdots)$ を $g$ における $\mathrm{takeWhile} / \mathrm{dropWhile}$ で分割する：
より短い文脈に帰着する（$H$ 下の合同）か、$g$ が bad part より下に来た時点で補題 6.5 に
帰着する。基底 $G = []$ が補題 6.5。$\square$

**命題 6.7（`m_bad_decreases`）。** $\ S \neq [] \ \wedge\ 0 < \mathrm{last}\ S \ \wedge\
\mathrm{badset}\ S \neq \emptyset \implies$
$$o((\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (\mathrm{drop}\ r\ (\mathrm{butlast}\ S)))) \prec o(S).$$

*証明.* $\mathrm{badset}\ S$ は有限かつ非空なので $r$ は定まる。
$S = (\mathrm{take}\ r\ S) \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$ と書き換えれば補題 6.6 に帰着。$\square$

## 7. 停止性

**定理 7.1（`m_step_decreases`）。** $\quad S \to T \implies o(T) \prec o(S).$

*証明.* drop0 / bad の場合は命題 6.2 / 6.7。$\square$

**定理 7.2（`m_termination`）。** $\quad \mathrm{wf}\ \lbrace (T, S) \mid S \to T\rbrace.$
同値に（`m_no_infinite_expansion`）、すべての $i$ で $\mathrm{Seq}(i) \to \mathrm{Seq}(i{+}1)$ と
なる $\mathrm{Seq}$ は存在しない。

*証明.* 定理 7.1 より $\lbrace (T, S) \mid S \to T\rbrace \subseteq o^{-1}(\prec)$、命題 4.3 より
$o^{-1}(\prec)$ は整礎（整礎関係の逆像）。$\square$

## 8. Isabelle 形式化との対応

ステートメント：`prss_paper.thy`（`p_*`、`sorry`）、証明：`prss_mechanized.thy` の `m_*`。
ビルド：`isbman build -d . -v PRSS`。

| 対象 | Isabelle | ソース |
|---|---|---|
| $\mathrm{multp}$（定義 2.2） | `multp` | `HOL-Library.Multiset` |
| 命題 2.3 | `wfp_multp` | `HOL-Library.Multiset` |
| $\to$（定義 3.1） | `step`（`drop0`, `bad`） | [prss_defs.thy:76](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_defs.thy#L76) |
| $\mathrm{badset}$ / $\mathrm{badroot}$ | `badset` / `badroot` | [prss_defs.thy:67](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_defs.thy#L67), [70](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_defs.thy#L70) |
| $\mathsf{hord}$, $H$ | `datatype hord = H "hord multiset"` | [prss_ordinal.thy:16](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_ordinal.thy#L16) |
| $\prec$ | `hlt` | [prss_ordinal.thy:20](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_ordinal.thy#L20) |
| 命題 4.3 | `wfP_hlt` | [prss_ordinal.thy:199](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_ordinal.thy#L199) |
| $o$（定義 5.1） | `omap` | [prss_defs.thy:40](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_defs.thy#L40) |
| 補題 6.1 | `omap_snoc_increases` | [prss_mechanized.thy:106](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L106) |
| 命題 6.2 | `m_drop0_decreases` | [prss_mechanized.thy:161](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L161) |
| 補題 6.3 | `omap_rep` | [prss_mechanized.thy:204](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L204) |
| 補題 6.4 | `omap_BfM` | [prss_mechanized.thy:228](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L228) |
| 補題 6.5 | `omap_core` | [prss_mechanized.thy:246](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L246) |
| 補題 6.6 | `omap_BADCTX` | [prss_mechanized.thy:303](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L303) |
| 命題 6.7 | `m_bad_decreases` | [prss_mechanized.thy:426](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L426) |
| 定理 7.1 | `m_step_decreases` | [prss_mechanized.thy:494](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L494) |
| 定理 7.2 | `m_termination`, `m_no_infinite_expansion` | [prss_mechanized.thy:506](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L506), [515](https://github.com/koteitan/prss-proof/blob/main/with-multiset/prss_mechanized.thy#L515) |

---

出典：Koteitan「[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)」（巨大数研究 Wiki）；バシク「[BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81)」（巨大数研究 Wiki, 2015）。
