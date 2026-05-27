[← 戻る](README-ja.md) | [English](proof.md) | [Japanese](proof-ja.md)

# バシク氏の原始数列システムの停止性

バシク氏の*原始数列システム*が停止すること、すなわちあらゆる展開が有限で終わることを
証明する。各自然数有限列に整礎順序の元——具体的には、再帰的に定めた多重集合順序を入れた
有限木——を割り当て、展開の各ステップでこの元が真に減少することを示す。整礎性により無限
展開は排除される。本論の議論は Isabelle/HOL で形式化されており、機械化された主張との対応は
§6 に与える。展開は初等的であり、現れる対象はすべて具体的な有限構造で、順序数論の前提を
必要としない。

## 1. システム

*数列*とは自然数の有限リスト $S = (S_0, S_1, \dots, S_{X-1})$ をいう。位置は $0$ から数え、
$S_0$ を先頭、$X$ を長さとする。末尾の要素を `last S` $= S_{X-1}$、末尾を除いたリストを
`butlast S` $= (S_0, \dots, S_{X-2})$ と書く。

システムは数列とカウンタ $n \in \mathbb{N}$ の組 $S[n]$ に作用し、固定の*活性化関数* $f$
（バシク氏は $f(n) = n^2$）に依存する。1回の展開ステップは末尾要素による場合分けで定める。

- $([])[n] = n$：空列はカウンタを返し、処理は停止する；
- $S_{X-1} = 0$ のとき、末尾の $0$ を削除する：
  $$S[n] \longrightarrow (S_0, \dots, S_{X-2})[f(n)];$$
- $m := S_{X-1} > 0$ のとき、*bad root* を $S_p < m$ をみたす最大の位置 $p < X-1$ とし、
  数列を*good part* $G = (S_0, \dots, S_{r-1})$ と *bad part* $B = (S_r, \dots, S_{X-2})$ に
  分割して
  $$S[n] \longrightarrow \big(G,\ \underbrace{B, B, \dots, B}_{f(n)+1 \text{ 個}}\big)[f(n)].$$

カウンタ $n$ と関数 $f$ は $B$ の複製個数と返り値のみを定め、処理が停止するか否かには影響
しない。したがって停止性は*数列部分*だけの性質であり、追加コピー数 $k = f(n)$ を任意の
自然数としてよい。1ステップ（末尾 $0$ の削除、またはある $k$ による bad-part 複製）が $S$ を
$T$ に送るとき $S \to T$ と書く。証明すべき定理は、無限連鎖

$$S^{(0)} \to S^{(1)} \to S^{(2)} \to \cdots$$

が存在しないことである。

## 2. 値の順序

数列に割り当てる測度は、多重集合順序を入れた有限木の集合に値をとる。まず多重集合を確認する。

集合上の*多重集合*とは、重複度は数えるが順序は無視する有限の集まりであり、
$\lbrace 0, 0, 1\rbrace = \lbrace 0, 1, 0\rbrace \neq \lbrace 0, 1\rbrace$ である。多重集合
の和（重複度の加法）を $\uplus$ と書き、$\lbrace 0\rbrace \uplus \lbrace 0, 1\rbrace =
\lbrace 0, 0, 1\rbrace$ とする。

**定義 2.1（値）。** *値*とは値の多重集合である。この再帰は空の多重集合を基底とする。子の
多重集合が $M$ である値を $H(M)$ と書き、$\mathbf{0} := H(\lbrace\rbrace)$ とおく。同値に、
値は有限木である：ノード $H(M)$ は $M$ の各要素ごとに1本の部分木を子にもち、重複を許す。
Isabelle ではこれがデータ型 `datatype hord = H "hord multiset"` である。

**定義 2.2（順序）。** 値の順序を、子に適用した自分自身の順序の多重集合拡大で定める。値の
多重集合 $M, N$ について、$N$ から1個の要素 $x$ を取り除き、$x$ より真に小さい要素を有限個
（$0$ 個でもよい）付け加えて $M$ が得られるとき $M \prec_{\mathrm{ms}} N$ と書く。値については

$$H(M) \prec H(N) \iff M \prec_{\mathrm{ms}} N$$

と定める。比較される要素は常に子、すなわちより小さい木なので、この再帰は整合的に定まる。

**例 2.3.** $\mathbf{1} := H(\lbrace \mathbf{0}\rbrace)$、
$\mathbf{2} := H(\lbrace \mathbf{0}, \mathbf{0}\rbrace)$、
$\boldsymbol{\omega} := H(\lbrace \mathbf{1}\rbrace)$ とおくと
$\mathbf{2} \prec \boldsymbol{\omega}$ である：$\boldsymbol{\omega}$ の子
$\lbrace \mathbf{1}\rbrace$ から $\mathbf{1}$ を除き、$\mathbf{1}$ より小さい $\mathbf{0}$ を
2個加えると $\lbrace \mathbf{0}, \mathbf{0}\rbrace$ が得られる。

**命題 2.4（整礎性）。** 順序 $\prec$ は無限の真に減少する連鎖
$v_0 \succ v_1 \succ v_2 \succ \cdots$ をもたない。同値に、値の空でない任意の集合は $\prec$
について極小な元をもつ。

*証明.* 値に関する構造帰納法による。整礎順序の多重集合拡大が整礎であるという事実を用いる。
これが定理 `wfP_hlt` であり、`HOL-Library.Multiset` のみの上で形式化されている。$\square$

**注意 2.5.** $H(M)$ を順序数 $\omega^{a_1} \oplus \cdots \oplus \omega^{a_k}$（$a_1, \dots,
a_k$ は子、$\oplus$ は自然和）と読めば、値は $\varepsilon_0$ 未満の順序数全体と、$\prec$ は
順序数の順序と同一視される。以下ではこの読み方は用いない。

## 3. 数列上の測度

各数列 $S$ に値 $o(S)$ を割り当てる。

**定義 3.1（数列の森）。** $S$ の位置 $i$ に対し、その*親*を $S_j < S_i$ をみたす最大の
$j < i$ とし、直前に小さい要素がなければ $i$ を*根*とする。（これは bad root を定める規則
そのものであり、ステップが末尾要素を削除するとき、その親が bad root になる。）親関係により
$S$ は森として表される。

例えば `(0,1,2,0,1)` は2本の木からなる森である。

```
  位置:  0  1  2  3  4              0 (位置0)        0 (位置3)
  要素:  0  1  2  0  1              └ 1 (位置1)      └ 1 (位置4)
                                      └ 2 (位置2)
```

**定義 3.2（測度 $o$）。** 各木に値 $H(\text{子たち})$ を与え、森の木たちを $\uplus$ で
合わせる。左から読めばこれは次の再帰である。

$$o([]) = H(\lbrace\rbrace), \qquad
  o(a \# \mathit{rest}) = H\big(\ \lbrace o(\mathit{inside})\rbrace \ \uplus\ C\ \big),$$

ここで $\mathit{inside}$ は $\mathit{rest}$ の先頭からの、要素がすべて $a$ を超える最長の
部分（先頭ノードの子孫）、$\mathit{outside}$ は残りの接尾辞、$C$ は $o(\mathit{outside})$ の
子の多重集合（すなわち $o(\mathit{outside}) = H(C)$）である。これが Isabelle の関数
`omap` である。

この測度は Isabelle で検証された次の値をとる：$o(0) = \mathbf{1}$、$k$ 個の $0$ の列の値は
$\mathbf{k}$、$o(0,1) = \boldsymbol{\omega}$、$o(0,1,1) = \boldsymbol{\omega}^2$、
$o(0,1,2) = \boldsymbol{\omega}^{\boldsymbol{\omega}}$（順序数表記は注意 2.5 による。各々は
具体的には有限木である）。

## 4. 各ステップは測度を減少させる

$S \to T$ のとき $o(T) \prec o(S)$ を示す。補助的な単調性補題ののち、2つの場合を扱う。

**補題 4.1（`omap_snoc_increases`）。** 任意の数列 $C$ と任意の $m$ について
$$o(C) \prec o(C, m).$$

*証明.* 末尾に要素を加えると森にノードが1つ増える：新しい根となってトップレベルの子
$\mathbf{0}$ が1つ増えるか、既存ノードの子孫が1つ増えてそのノードが大きくなるかのいずれか
である。どちらでも値は真に増加する。形式的証明は $o$ の再帰に沿う帰納法による。$\square$

**命題 4.2（末尾 $0$ の削除, `m_drop0_decreases`）。** $S$ が空でなく `last S` $= 0$ ならば
$o(\texttt{butlast } S) \prec o(S)$。

*証明.* 末尾の $0$ はどの要素より小さいので根であり、最後尾なので子孫をもたない孤立した葉
である。よって $o(S)$ は $o(\texttt{butlast } S)$ にトップレベルの子 $\mathbf{0}$ を1つ加えた
もので、多重集合から1要素を削除するのは $\prec_{\mathrm{ms}}$ の減少である。$\square$

次に bad-part のステップ
$S = (G, B, m) \to (G, \underbrace{B, \dots, B}_{k+1})$ を扱う。ここで $m =$ `last S` $> 0$、
$B = (v, B_t)$ で $v = S_r$ は bad root $r$ の要素である。$r$ は要素が $m$ 未満となる*最後の*
前方位置なので、$B_t$ の各要素は $m$ 以上、したがって $v$ を超える。

**補題 4.3（`omap_rep`, `omap_BfM`, `omap_core`）。** これらの仮定の下で
$$o\big(\underbrace{B, \dots, B}_{k+1}\big) \prec o(B, m).$$

*証明.* $B = (v, B_t)$ の $k+1$ 個のコピーは隣り合う $k+1$ 本の木をなし、各々根 $v$ で子孫の
森が $B_t$ である。ゆえに（補題 `omap_rep`）
$$o\big(\underbrace{B, \dots, B}_{k+1}\big) = H\big(\underbrace{o(B_t), \dots, o(B_t)}_{k+1}\big).$$
$(B, m) = (v, B_t, m)$ では末尾の $m$ は $v$ および $B_t$ の各要素を超えるので、その親は $v$ で
あり、唯一の根 $v$ の子孫が1つ増える。ゆえに（補題 `omap_BfM`）
$$o(B, m) = H\big(\lbrace o(B_t, m)\rbrace\big).$$
右辺の多重集合は元 $o(B_t, m)$ を1個もち、左辺は $o(B_t)$ を $k+1$ 個もつ。補題 4.1 により
$o(B_t) \prec o(B_t, m)$ なので、1個の元を真に小さい有限個の元で置き換えることは、定義により
$\prec_{\mathrm{ms}}$ の減少である。$\square$

**補題 4.4（`omap_BADCTX`）。** 任意の good part $G$ について
$$o\big(G, \underbrace{B, \dots, B}_{k+1}\big) \prec o(G, B, m).$$

*証明.* $G$ の長さに関する帰納法による。先頭要素 $g$ を除くと、$o$ の再帰は比較を $G$ の内部
に閉じ込めて、両辺で同一の周辺文脈をもつより短い good part に帰着させるか、あるいは $g$ が
bad part より下に来た時点で補題 4.3 に帰着させる。基底（$G$ が空）は補題 4.3 そのものである。
$\square$

**命題 4.5（bad-part ステップ, `m_bad_decreases`）。** $S$ が空でなく `last S` $> 0$ で
bad root が存在するならば、任意の $k$ について
$o\big(G, \underbrace{B, \dots, B}_{k+1}\big) \prec o(S)$。

*証明.* bad root の候補位置は有限集合をなし、到達しうる数列では $S_0 = 0 < m$ ゆえ空でないので
bad root はちゃんと定まる。主張は補題 4.4 である。$\square$

## 5. 停止性

**定理 5.1（`m_step_decreases`）。** $S \to T$ ならば $o(T) \prec o(S)$。

*証明.* 2つの場合は命題 4.2 と 4.5 である。$\square$

**定理 5.2（停止性, `m_termination`）。** 無限連鎖 $S^{(0)} \to S^{(1)} \to \cdots$ は
存在しない。同値に（`m_no_infinite_expansion`）あらゆる展開は有限である。

*証明.* 無限連鎖があれば、定理 5.1 により値の無限に真に減少する連鎖
$o(S^{(0)}) \succ o(S^{(1)}) \succ \cdots$ が生じ、命題 2.4 に反する。$\square$

## 6. Isabelle 形式化との対応

ステートメントは `prss_paper.thy`（接頭辞 `p_`、`sorry` のまま）に転記され、
`prss_mechanized.thy` の `m_*` で解消される。セッションは `isbman build -d . -v PRSS` で
ビルドする。

| 対象 | Isabelle | ソース |
|---|---|---|
| 値 $H(M)$ | `datatype hord = H "hord multiset"` | [prss_ordinal.thy:16](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L16) |
| 順序 $\prec$ | `hlt` | [prss_ordinal.thy:20](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L20) |
| 命題 2.4 | `wfP_hlt` | [prss_ordinal.thy:199](https://github.com/koteitan/prss-proof/blob/main/prss_ordinal.thy#L199) |
| 数列 | `nat list` | [prss_defs.thy](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy) |
| 測度 $o$（定義 3.2） | `omap` | [prss_defs.thy:40](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L40) |
| bad root（定義 3.1） | `badset` / `badroot` | [prss_defs.thy:67](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L67), [70](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L70) |
| ステップ $S \to T$ | `step`（`drop0`, `bad`） | [prss_defs.thy:76](https://github.com/koteitan/prss-proof/blob/main/prss_defs.thy#L76) |
| 補題 4.1 | `omap_snoc_increases` | [prss_mechanized.thy:106](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L106) |
| 命題 4.2 | `m_drop0_decreases` | [prss_mechanized.thy:161](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L161) |
| 補題 4.3 | `omap_rep`, `omap_BfM`, `omap_core` | [prss_mechanized.thy:204](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L204) |
| 補題 4.4 | `omap_BADCTX` | [prss_mechanized.thy:303](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L303) |
| 命題 4.5 | `m_bad_decreases` | [prss_mechanized.thy:426](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L426) |
| 定理 5.1 | `m_step_decreases` | [prss_mechanized.thy:494](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L494) |
| 定理 5.2 | `m_termination`, `m_no_infinite_expansion` | [prss_mechanized.thy:506](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L506), [515](https://github.com/koteitan/prss-proof/blob/main/prss_mechanized.thy#L515) |

---

出典：Koteitan「Purely mathematical definition of BMS」（巨大数研究 Wiki）；
バシク「BASIC言語による巨大数のまとめ」（巨大数研究 Wiki, 2015）。
