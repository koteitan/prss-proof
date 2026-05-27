[← 戻る](README-ja.md) | [English](proof.md) | [Japanese](proof-ja.md)

# ぶしくし氏の原始数列システムの停止性

自己完結な数学的証明で、Isabelle/HOL により形式検証したもの
（`prss_ordinal.thy`, `prss_defs.thy`, `prss_paper.thy`, `prss_mechanized.thy`）。
方針は、各原始数列を $\varepsilon_0$ 未満の順序数に写し、展開（expand）の各ステップで
その順序数が真に減少することを示すことである。

## 1. 原始数列システム

**原始数列**とは自然数の有限列 $\mathbf{S}=(S_0,S_1,\dots,S_{X-1})$（長さ $X$）である。
カウンタ $n\in\mathbb{N}$ と活性化関数 $f$（ぶしくし氏は $f(n)=n^2$）を伴い、展開関数
$\mathrm{expand}$ を次で定める。

- $\mathrm{expand}([n]) = n$ &nbsp;（空列：カウンタを返す）；
- $S_{X-1}=0$ のとき：&nbsp; $\mathrm{expand}(\mathbf{S}[n]) = \mathrm{expand}\big((S_0,\dots,S_{X-2}) [f(n)]\big)$ &nbsp;（**末尾の 0 を削除**）；
- そうでないとき、**bad root** を $r=\max\lbrace  p \mid S_p < S_{X-1} \wedge p<X-1 \rbrace $、**good part** を $\mathbf{G}=(S_0,\dots,S_{r-1})$、**bad part** を $\mathbf{B}=(S_r,\dots,S_{X-2})$ として

$$\mathrm{expand}(\mathbf{S}[n]) = \mathrm{expand}\big(\mathbf{G} \underbrace{\mathbf{B} \mathbf{B}\cdots\mathbf{B}}_{f(n)+1} [f(n)]\big).$$

数 $\mathrm{Primitive}(n)=\mathrm{expand}\big((0,1,\dots,n{+}1)[n]\big)$ の大きさは
急増加関数階層で $f_{\psi(\varepsilon_0)+1}(10)$ である。**停止性**とは、任意の列から
始めて有限ステップで空列に到達することをいう。これはカウンタ $n$ にも $f$ にも依らず、
*列の部分*が常に $[ ]$ へ縮むことと同値である。よって列の部分だけの書き換えを、追加
コピー数 $k=f(n)$ を任意としたまま調べる。

## 2. 原始数列の森（forest）解釈

各インデックス $i$ を森のノードと読む。ここで $i$ の**親**を

$$\mathrm{parent}(i)=\max\lbrace  j \mid j<i \wedge S_j<S_i \rbrace $$

（直前で値が真に小さい最も近いインデックス。無ければ $i$ は**根**）とする。これは
bad root を定める規則そのものであり、$\mathrm{expand}$ が末尾要素 $S_{X-1}$ を削除する
とき、その要素の親はちょうど bad root $r$ になる。

例えば `(0,1,2,0,1)` は2本の木として読める。

```
  index:  0  1  2  3  4              0(idx0)        0(idx3)
  value:  0  1  2  0  1              └ 1(idx1)      └ 1(idx4)
                                       └ 2(idx2)
```

## 3. 順序数写像

**定義（森の順序数）。** 自然和（Hessenberg 和）$\oplus$ を用いて

$$o(\text{ノード } i)=\bigoplus_{c:\ i\text{の子}}\omega^{ o(c)}, \qquad o(\mathbf{S})=\bigoplus_{r:\ \text{根}}\omega^{ o(r)} .$$

葉は $o=0$ なので $\omega^0=1$。

形式化では $\varepsilon_0$ 未満の順序数を**遺伝的有限マルチセット**
`datatype hord = H "hord multiset"` で表す。$H M$ は $\bigoplus_{x\in M}\omega^{x}$
を、$H \lbrace \rbrace $ は $0$ を表す。順序は自分自身のマルチセット拡大

$$H M \prec H N \iff M \prec_{\mathrm{mult}} N$$

であり、これはちょうど $\varepsilon_0$ 未満のカントール標準形の比較で、**整礎**である
（定理 `wfP_hlt`。accessible 部分に制限したマルチセット順序の整礎性から証明）。

写像は左から右へ、先頭要素を根として切り出して計算する。すなわち根の子孫は直後の
「値がより大きい極大ブロック」であり、残りの接尾辞が森の続きとなる。Isabelle では
（`omap`）：

```
omap [] = H {}
omap (a # rest) = H ( {| omap (takeWhile (<a<) rest) |}
                      ⊕ omap (dropWhile (<a<) rest) )
```

ここで `takeWhile (λx. a<x) rest` が $a$ の子孫の森である。検算（機械検証済）：
$o(0,1)=\omega$、$o(0,1,1)=\omega^2$、$o(0,1,2)=\omega^{\omega}$、$k$ 個の 0 の列は $k$。
原始数列全体の順序型は $\varepsilon_0$ である。

## 4. 各ステップで順序数が真に減少する

### 4.1 補助事実（★）：末尾追加で $o$ は真に増加

**補題（★, `omap_snoc_increases`）。** 任意の列 $C$ と任意の $m$ について
&nbsp; $o(C) \prec o(C \mathbin{++} [m])$。

森にノードを足すと必ず大きくなる。$m$ は新たな根（項 $\omega^0$ が増える）になるか、
右脊柱（right spine）のどこかに子として加わり（ある指数が増える）。`omap` の再帰に
沿った帰納法で証明。

### 4.2 末尾0削除のケース

**命題（`m_drop0_decreases`）。** $S\neq[ ]$ かつ $\mathrm{last} S=0$ ならば
$o(\mathrm{butlast} S)\prec o(S)$。

末尾の $0$ は最小値なので根であり、最後尾なので葉である。これを除くと top-level の項
$\omega^0$ がちょうど1つ消える。$o(S)=H\big(\lbrace H\lbrace \rbrace \rbrace +M\big)$、
$o(\mathrm{butlast} S)=H M$ なので、削除はマルチセット（したがって順序数）の減少。

### 4.3 bad-part のケース

$S=\mathbf{G} \mathbf{B} [m]$（$m=\mathrm{last} S>0$）とし、$\mathbf{B}=v\#\mathbf{B}_t$、
$v=S_r$ は bad root の値とする。$r$ の最大性より $\mathbf{B}_t$ の全要素は $\ge m$、
したがって $>v$。ステップは $S$ を $\mathbf{G} \mathbf{B}^{ k+1}$（$k=f(n)$ 個の追加
コピー）へ書き換える。

**補題（コア, `omap_core`）。** 上記の条件下で

$$o\big(\mathbf{B}^{ k+1}\big)\ \prec\ o\big(\mathbf{B} [m]\big).$$

2つの計算で明快になる。第一に、$\mathbf{B}=v\#\mathbf{B}_t$ の $k$ 個連続コピーは、
それぞれ $v$ を根とし子孫の森が $\mathbf{B}_t$ である $k$ 本の兄弟の木をなすので、

$$o\big(\mathbf{B}^{ k+1}\big)=H\big( (k{+}1)\cdot\lbrace  o(\mathbf{B}_t) \rbrace  \big) \qquad(\text{補題 } \texttt{omap\_rep}).$$

第二に、$\mathbf{B} [m]=v\#(\mathbf{B}_t [m])$ では新しい $m$ は $v$ の子になる
（$\mathbf{B}_t$ の全要素は $v$ を超え、$m>v$）ので、

$$o\big(\mathbf{B} [m]\big)=H\big(\lbrace  o(\mathbf{B}_t [m]) \rbrace \big) \qquad(\text{補題 } \texttt{omap\_BfM}).$$

よって減少は1回のマルチセットステップとなる。すなわち1個の要素 $o(\mathbf{B}_t [m])$
を、(★) により真に小さい $o(\mathbf{B}_t)$ の $k{+}1$ 個のコピーで置き換える。

**補題（文脈つき, `omap_BADCTX`）。** 任意の good part $\mathbf{G}$ について

$$o\big(\mathbf{G} \mathbf{B}^{ k+1}\big)\ \prec\ o\big(\mathbf{G} \mathbf{B} [m]\big).$$

$\mathbf{G}$ の長さに関する強帰納法による。先頭要素 $g$ を剥がすと、`omap` の再帰は
比較を $\mathbf{G}$ の内側に保つ（合同 `hlt_under_H` でより短い文脈へ帰着）か、あるいは
$g$ が bad part より下に落ちた時点でコアへ直接帰着する。基底 $\mathbf{G}=[ ]$ がコア
である。

**命題（`m_bad_decreases`）。** $S\neq[ ]$、$\mathrm{last} S>0$、bad root が存在する
ならば、任意の $k$ について
$o\big(\mathbf{G} \mathbf{B}^{ k+1}\big)\ \prec\ o(S)$。

配線：bad set $\lbrace p<X{-}1 \mid S_p<\mathrm{last} S\rbrace $ は有限かつ非空なので $r=\max$ は
真の bad root であり、$S=\mathbf{G} (v\#\mathbf{B}_t) [m]$、$r$ の最大性から
$\mathbf{B}_t\ge m$。あとは `omap_BADCTX`。

## 5. 主定理

**定理（`m_step_decreases`）。** $S \to T$ が展開の1ステップならば $o(T) \prec o(S)$。

**定理（停止性, `m_termination`）。** 展開関係 $\lbrace (T,S)\mid S\to T\rbrace $ は整礎である。
同値に（`m_no_infinite_expansion`）無限展開列は存在せず、$\mathrm{expand}$ は必ず停止
する。

$o$ は各ステップで真に減少し、$\prec$ は $\varepsilon_0$ 未満の順序数上で整礎なので、
展開関係は $o$ による整礎関係の逆像となり、整礎である。$\qquad\blacksquare$

## 6. Isabelle 形式化との対応

| 本文書の概念 | Isabelle | ファイル |
|---|---|---|
| $\varepsilon_0$ 未満の順序数、$H\,M$ | `datatype hord = H "hord multiset"` | `prss_ordinal.thy` |
| 順序 $\prec$ | `hlt`（`hlt (H M) (H N) ⟷ multp hlt M N`） | `prss_ordinal.thy` |
| $\prec$ の整礎性 | `wfP_hlt` | `prss_ordinal.thy` |
| 原始数列 | `nat list` | `prss_defs.thy` |
| 順序数写像 $o$ | `omap :: nat list ⇒ hord` | `prss_defs.thy` |
| bad set / bad root $r$ | `badset` / `badroot` | `prss_defs.thy` |
| 展開1ステップ $S \to T$ | `step :: nat list ⇒ nat list ⇒ bool`（`drop0`, `bad`） | `prss_defs.thy` |
| (★) 末尾追加で $o$ 増加 | `omap_snoc_increases` | `prss_mechanized.thy` |
| §4.2 末尾0削除の減少 | `m_drop0_decreases` | `prss_mechanized.thy` |
| §4.3 $o(\mathbf{B}^{k+1})=H((k{+}1)\cdot\lbrace o(\mathbf{B}_t)\rbrace)$ | `omap_rep` | `prss_mechanized.thy` |
| §4.3 コア減少 | `omap_core` | `prss_mechanized.thy` |
| §4.3 文脈 $\mathbf{G}$ つき | `omap_BADCTX` | `prss_mechanized.thy` |
| §4.3 bad-part 減少 | `m_bad_decreases` | `prss_mechanized.thy` |
| §5 ステップで $o$ 減少 | `m_step_decreases` | `prss_mechanized.thy` |
| §5 停止性 | `m_termination`, `m_no_infinite_expansion` | `prss_mechanized.thy` |

ステートメントは `prss_paper.thy`（`p_*`、`sorry` のまま）に、証明は
`prss_mechanized.thy` の `m_*` にある。ビルドは `isbman build -d . -v PRSS`。

---

出典：Koteitan「Purely mathematical definition of BMS」（巨大数研究 Wiki）；
ぶしくし「BASIC言語による巨大数のまとめ」。順序数の核は `HOL-Library.Multiset` のみを
用い、AFP のエントリは不要である。
