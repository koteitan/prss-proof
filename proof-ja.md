[← 戻る](README-ja.md) | [English](proof.md) | [Japanese](proof-ja.md)

# バシク氏の原始数列システムの停止性（多重集合なし版）

バシク氏の*原始数列システム*の停止性を証明する。各数列 $S \in \mathsf{list}(\mathbb{N})$ を
整礎順序の値 $o(S)$——具体的には $\varepsilon_0$ 未満の*カントール標準形*項を辞書式順序で——に
写し、展開の各ステップで $o$ が真に減少することを示す。整礎性により無限展開は排除される。
これは**多重集合を使わない**実装 `prss_nomultiset.thy`（`imports Main` のみ。対応は §7）。
対になる [`main` の proof.md](https://github.com/koteitan/prss-proof/blob/main/proof-ja.md)
は遺伝的有限多重集合を使う版で、なぜそちらが短いかは
[README-nomultiset-ja.md](README-nomultiset-ja.md) を参照。

関係 $R$ が*整礎*とは、無限下降列が存在しないこと、すなわち、すべての $i$ で
$R(x_{i+1}, x_i)$ となる $x_0, x_1, x_2, \dots$ が存在しないことをいう。

## 1. リスト操作

ある集合（ここでは $\mathbb{N}$）上の有限リストは2つの*構成子*から作られる：空リスト $[]$ と
cons $a \mathbin{::} xs$（$xs$ の先頭に $a$ を付ける）。どのリストも一意に
$[a_1, \dots, a_n] = a_1 \mathbin{::} \cdots \mathbin{::} a_n \mathbin{::} []$。以下で使う操作を
再帰で定める（$\mathrm{takeWhile}/\mathrm{dropWhile}$ の条件 $P\ x$ は先頭を判定）：

$\mathrm{length}$、append $xs \mathbin{@} ys$、$\mathrm{last}$（末尾要素）、$\mathrm{butlast}$
（末尾を除く）、$\mathrm{take}\ n$ / $\mathrm{drop}\ n$（先頭 $n$ / それ以外）、添字
$xs \mathbin{!} n$、および：

$$\mathrm{takeWhile}\ P\ (x \mathbin{::} xs) = \begin{cases} x \mathbin{::} \mathrm{takeWhile}\ P\ xs & P\ x \\ [] & \neg P\ x \end{cases}, \qquad
\mathrm{dropWhile}\ P\ (x \mathbin{::} xs) = \begin{cases} \mathrm{dropWhile}\ P\ xs & P\ x \\ x \mathbin{::} xs & \neg P\ x \end{cases},$$

$$\mathrm{concat}\ (xs \mathbin{::} xss) = xs \mathbin{@} \mathrm{concat}\ xss, \qquad
\mathrm{replicate}\ (n{+}1)\ x = x \mathbin{::} \mathrm{replicate}\ n\ x.$$

## 2. 展開ステップ

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

**定義 2.1（ステップ関係, `step`）。** カウンタと $f$ を除き、コピー数 $k \in \mathbb{N}$ を
任意とする。$S \to T$ を次の帰納規則で定める。

$$\frac{S \neq []\quad m = 0}{S \to \mathrm{butlast}\ S}\ (\mathrm{drop0}),
\qquad
\frac{S \neq []\quad 0 < m \quad \mathrm{badset}\ S \neq \emptyset}
{S \to (\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k+1)\ B)}\ (\mathrm{bad}),$$

$r = \mathrm{badroot}\ S$、$B = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$、

$$\mathrm{badset}\ S = \lbrace p \mid p < \mathrm{length}\ S - 1 \ \wedge\ S \mathbin{!} p < m\rbrace,
\qquad \mathrm{badroot}\ S = \max(\mathrm{badset}\ S).$$

規則 $\mathrm{drop0}$ は $\mathrm{expand}$ の $m = 0$ の分岐、規則 $\mathrm{bad}$（$k = f(n)$）は
$m > 0$ の分岐に対応。$\to$ は $\mathrm{expand}$ の1ステップの数列部分。任意の $f, n$ に対する
$\mathrm{expand}$ の停止性は、無限連鎖 $S^{(0)} \to S^{(1)} \to \cdots$ の非存在に帰着する。

## 3. カントール標準形とその順序

**定義 3.1（項, `ord`）。** $\varepsilon_0$ 未満の順序数を二分木

$$\mathsf{ord} ::= Z \ \mid\ E\ a\ b \qquad (a, b \in \mathsf{ord})$$

で表す。$Z = 0$、$E\ a\ b = \omega^{a} + b$ と読む。*先頭指数*は $\mathrm{lead}\ Z = Z$、
$\mathrm{lead}\ (E\ a\ b) = a$。

**定義 3.2（順序, `olt` / $\prec$）。** 再帰的な辞書式順序：

$$Z \prec E\ a\ b, \qquad
E\ a\ b \prec E\ c\ d \iff a \prec c \ \vee\ (a = c \ \wedge\ b \prec d),$$

$Z$ より小さいものは無い。$x \preceq y$ は $x \prec y \vee x = y$。これは線形順序
（`olt_trans`, `olt_total`）。

**定義 3.3（標準形, `cnf`）。** 指数が左から非増加で遺伝的に正規なとき*カントール標準形*：

$$\mathrm{cnf}\ Z, \qquad \mathrm{cnf}\ (E\ a\ b) \iff \mathrm{cnf}\ a \ \wedge\ \mathrm{cnf}\ b \ \wedge\ (b = Z \ \vee\ \mathrm{lead}\ b \preceq a).$$

（順序の制約は本質的：*非* CNF 項の上では $\prec$ は整礎でない——例えば
$E (E Z Z) Z \succ E Z (E (E Z Z) Z) \succ \cdots$ という「指数昇順」項の無限下降が作れる。
CNF はこれを排除する。）

**命題 3.4（`wfP_R`）。** $\prec$ は CNF 項の上で整礎。すなわち
$R\ x\ y \iff \mathrm{cnf}\ x \wedge \mathrm{cnf}\ y \wedge x \prec y$ は整礎。

*証明.* $R$-accessibility を `accp R` とする。全 CNF 項が accessible であることを**二重帰納**で
示す（多重集合ライブラリは不使用）：補助補題 `accp_R_E` は、指数 $a$ の accessibility による
帰納と末尾 $b$ の入れ子帰納で、$a, b$ が accessible なら $E\ a\ b$ も accessible を示す。
`accp_R_all` が構造帰納で全 CNF 項を覆い、非 CNF 項は空虚に accessible。$\square$

## 4. 測度 $o$ (`omap`)

**定義 4.1（挿入, `ins`）。** $\mathrm{ins}\ e\ y$ は単一項 $\omega^{e}$ を CNF $y$ の整列位置に
挿入する：

$$\mathrm{ins}\ e\ Z = E\ e\ Z, \qquad
\mathrm{ins}\ e\ (E\ a\ b) = \begin{cases} E\ e\ (E\ a\ b) & a \prec e \\ E\ a\ (\mathrm{ins}\ e\ b) & \neg (a \prec e). \end{cases}$$

標準形を保ち（`cnf_ins`）、交換する（`ins_comm`:
$\mathrm{ins}\ e\ (\mathrm{ins}\ f\ y) = \mathrm{ins}\ f\ (\mathrm{ins}\ e\ y)$）。

**定義 4.2（測度, `omap`）。** 数列を左から読む。先頭 $a$ は、直後の「$a$ より大きい」最長の
並び $\mathit{inside}$（子孫の森）に対する項 $\omega^{o(\mathit{inside})}$ を寄与し、それを残りの
値に挿入する：

$$o([]) = Z, \qquad o(a \mathbin{::} \mathit{rest}) = \mathrm{ins}\ \big(o(\mathit{tw})\big)\ \big(o(\mathit{dw})\big),$$
$$\mathit{tw} = \mathrm{takeWhile}\ (\lambda x.\ a < x)\ \mathit{rest}, \qquad \mathit{dw} = \mathrm{dropWhile}\ (\lambda x.\ a < x)\ \mathit{rest}.$$

**命題 4.3（`cnf_omap`）。** 任意の $S$ で $\mathrm{cnf}\ (o(S))$。（よって $o$ は常に命題 3.4 の
整礎な定義域に入る。）

*証明.* $o$ の再帰に沿う帰納法、`cnf_ins` を用いる。$\square$

## 5. 各ステップは測度を減少させる

**補題 5.1（`olt_ins_self`）。** $\quad y \prec \mathrm{ins}\ e\ y.$ 項を挿入すると値は真に
増加する。

**補題 5.2（`omap_snoc0`）。** $\quad o(P \mathbin{@} [0]) = \mathrm{ins}\ Z\ (o(P)).$
末尾の $0$ は最小項 $\omega^{0}$ を挿入する。（`ins_comm` を用いた帰納法。）

**命題 5.3（末尾0削除, `m_drop0`）。** $S \neq []$ かつ $\mathrm{last}\ S = 0$ ならば
$o(\mathrm{butlast}\ S) \prec o(S)$。

*証明.* $S = \mathrm{butlast}\ S \mathbin{@} [0]$ より 5.2 で
$o(S) = \mathrm{ins}\ Z\ (o(\mathrm{butlast}\ S))$、5.1 で $o(\mathrm{butlast}\ S) \prec o(S)$。$\square$

**補題 5.4（`ins_mono2`）。** $\mathrm{cnf}\ y$, $\mathrm{cnf}\ y'$, $y \prec y'$ ならば
$\mathrm{ins}\ e\ y \prec \mathrm{ins}\ e\ y'$。

**補題 5.5（`omap_snoc_increase`）。** $\quad o(C) \prec o(C \mathbin{@} [m])$（任意の $m$）。
（$o$ の帰納法。再帰段で補題 5.4 を用いる。）

bad ステップでは $S = G \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$ と書く。
$r = \mathrm{badroot}\ S$、$v = S \mathbin{!} r$、$m = \mathrm{last}\ S$、
$B = v \mathbin{::} B_t = \mathrm{drop}\ r\ (\mathrm{butlast}\ S)$。$r$ の最大性より
$\forall x \in B_t.\ m \le x$、ゆえに $v < x$、かつ $v < m$。

**補題 5.6（`omap_rep`）。** $\forall x \in B_t.\ v < x$ ならば、$B$ の $k$ 個コピーは $k$ 個の
等しい項になる：
$$o\big(\mathrm{concat}(\mathrm{replicate}\ k\ (v \mathbin{::} B_t))\big) = (\mathrm{ins}\ (o(B_t)))^{k}\ Z.$$

**補題 5.7（`omap_BfM`）。** $\forall x \in B_t.\ v < x$ かつ $v < m$ ならば、末尾の $m$ は
$v$ の部分木に入り、単一項になる：
$$o\big((v \mathbin{::} B_t) \mathbin{@} [m]\big) = E\ \big(o(B_t \mathbin{@} [m])\big)\ Z.$$

**補題 5.8（コア減少, `omap_core`）。** 同じ仮定の下、
$$o\big(\mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))\big) \prec o\big((v \mathbin{::} B_t) \mathbin{@} [m]\big).$$

*証明.* 左辺は $\beta = o(B_t)$ として $(\mathrm{ins}\ \beta)^{k+1} Z$（5.6）——指数がすべて $\beta$ の
CNF。右辺は $\gamma = o(B_t \mathbin{@} [m])$ として $E\ \gamma\ Z$（5.7）。$\beta \prec \gamma$（5.5）
なので、左辺の各項は先頭指数 $\beta \prec \gamma$ をもち、$E\ \gamma\ Z$ より小さい
（`funpow_ins_lt`）。$\square$

**補題 5.9（文脈つき, `omap_BADCTX`）。** 任意の good part $G$ について、
$$o\big(G \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (v \mathbin{::} B_t))\big) \prec o\big(G \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]\big).$$

*証明.* $\mathrm{length}\ G$ に関する帰納法。$G = g \mathbin{::} G'$ を剥がすと、$o$ の再帰は比較を
$G$ の内側に閉じ込める（より短い文脈へ帰着、補題 5.4 の合同）か、$g$ が bad part より下に
来た時点でコア（補題 5.8）に帰着する。基底 $G = []$ がコア。$\square$

**命題 5.10（bad ステップ, `m_bad`）。** $S \neq []$, $\mathrm{last}\ S > 0$,
$\mathrm{badset}\ S \neq \emptyset$ ならば、任意の $k$ について
$$o\big((\mathrm{take}\ r\ S) \mathbin{@} \mathrm{concat}(\mathrm{replicate}\ (k{+}1)\ (\mathrm{drop}\ r\ (\mathrm{butlast}\ S)))\big) \prec o(S).$$

*証明.* $\mathrm{badset}\ S$ は有限かつ非空なので $r$ は定まる。
$S = (\mathrm{take}\ r\ S) \mathbin{@} (v \mathbin{::} B_t) \mathbin{@} [m]$ と書き換えれば補題 5.9 に帰着。$\square$

## 6. 停止性

**定理 6.1（`m_step_decreases`）。** $\quad S \to T \implies o(T) \prec o(S).$

*証明.* 2つの場合は命題 5.3 と 5.10。$\square$

**定理 6.2（`m_termination`）。** $\quad \mathrm{wf}\ \lbrace (T, S) \mid S \to T\rbrace.$
同値に（`m_no_infinite_expansion`）、すべての $i$ で $\mathrm{Seq}(i) \to \mathrm{Seq}(i{+}1)$ と
なる $\mathrm{Seq}$ は存在しない。

*証明.* 定理 6.1 と $\mathrm{cnf}\ (o(\cdot))$（命題 4.3）より
$\lbrace (T, S) \mid S \to T\rbrace \subseteq o^{-1}(R)$。命題 3.4 より $o^{-1}(R)$ は整礎
（整礎関係の逆像）。$\square$

## 7. Isabelle 形式化との対応

すべての事実は [`prss_nomultiset.thy`](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy)
（`imports Main`、`HOL-Library.Multiset` 不使用）にある。ビルドは `isbman build -d . -v PRSS`。

| 対象 | Isabelle | ソース |
|---|---|---|
| $\mathsf{ord}$（$Z$, $E\ a\ b$） | `datatype ord = Z \| E ord ord` | [prss_nomultiset.thy:14](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L14) |
| $\prec$ | `olt`（`<o`） | [prss_nomultiset.thy:18](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L18) |
| 定義 3.3 | `cnf` | [prss_nomultiset.thy:34](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L34) |
| 命題 3.4 | `wfP_R` | [prss_nomultiset.thy:235](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L235) |
| 定義 4.1 | `ins` | [prss_nomultiset.thy:240](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L240) |
| $o$（定義 4.2） | `omap` | [prss_nomultiset.thy:332](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L332) |
| 命題 4.3 | `cnf_omap` | [prss_nomultiset.thy:342](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L342) |
| $\mathrm{badset}$ / $\mathrm{badroot}$ | `badset` / `badroot` | [prss_nomultiset.thy:780](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L780), [783](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L783) |
| $\to$（定義 2.1） | `step`（`drop0`, `bad`） | [prss_nomultiset.thy:844](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L844) |
| 補題 5.1 | `olt_ins_self` | [prss_nomultiset.thy:353](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L353) |
| 補題 5.2 | `omap_snoc0` | [prss_nomultiset.thy:368](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L368) |
| 命題 5.3 | `m_drop0` | [prss_nomultiset.thy:392](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L392) |
| 補題 5.4 | `ins_mono2` | [prss_nomultiset.thy:415](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L415) |
| 補題 5.5 | `omap_snoc_increase` | [prss_nomultiset.thy:494](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L494) |
| 補題 5.6 | `omap_rep` | [prss_nomultiset.thy:562](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L562) |
| 補題 5.7 | `omap_BfM` | [prss_nomultiset.thy:584](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L584) |
| 補題 5.8 | `omap_core` | [prss_nomultiset.thy:625](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L625) |
| 補題 5.9 | `omap_BADCTX` | [prss_nomultiset.thy:661](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L661) |
| 命題 5.10 | `m_bad` | [prss_nomultiset.thy:786](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L786) |
| 定理 6.1 | `m_step_decreases` | [prss_nomultiset.thy:851](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L851) |
| 定理 6.2 | `m_termination`, `m_no_infinite_expansion` | [prss_nomultiset.thy:863](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L863), [878](https://github.com/koteitan/prss-proof/blob/without-multiset/prss_nomultiset.thy#L878) |

---

出典：Koteitan「[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)」（巨大数研究 Wiki）；バシク「[BASIC言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81)」（巨大数研究 Wiki, 2015）。
