[English](README.md) | [Japanese](README-ja.md)

# prss-proof

Version: **v0.1.2**

ぶしくし氏の **原始数列システム（Primitive Sequence System）** が必ず停止する
ことを、**Isabelle/HOL** で機械的に検証したものです。

方針は古典的です。各原始数列を $\varepsilon_0$ 未満の順序数に写し、`expand` の各
ステップでその順序数が真に減少することを示します。$\varepsilon_0$ 未満の順序数は
整礎なので、無限に展開が続くことはありません。

数式での証明は [proof-ja.md](proof-ja.md)（[`index-ja.html`](index-ja.html) /
英語 [`proof.html`](proof.html) もあり、MathJax・ダークモード）を参照してください。

## 証明した内容

原始数列上の展開関係 `step` は整礎である（`m_termination`）。同値に、無限展開列は
存在しない（`m_no_infinite_expansion`）。いずれも `m_step_decreases`（各ステップで
順序数写像 `omap` が真に減少する）から従います。

## ファイル構成

| ファイル | 役割 |
|---|---|
| `prss_ordinal.thy` | $\varepsilon_0$ 未満の順序数を入れ子マルチセット型 `hord` で構成し、整礎順序 `hlt`（`wfP_hlt`）を証明。 |
| `prss_defs.thy` | 原始数列、`expand` の1ステップ関係 `step`、bad root、森の順序数写像 `omap`。 |
| `prss_paper.thy` | 命題・主定理のステートメント（すべて `sorry`）。 |
| `prss_mechanized.thy` | それらを解消する機械化証明。 |
| [`proof-ja.md`](proof-ja.md) | 人間向けの数式証明（`index-ja.html` もあり）。 |

命名規則：論文側の主張は `p_*`、機械化証明は `m_*`。

## 順序数の核

$\varepsilon_0$ 未満の順序数を、入れ子マルチセットのデータ型

```isabelle
datatype hord = H "hord multiset"
```

でモデル化します。`H M` は自然和 $\bigoplus_{x\in M}\omega^{x}$ を表し、順序は自分
自身のマルチセット拡大です。整礎性（`wfP_hlt`）は `HOL-Library.Multiset` のみから
証明しており、AFP のエントリは不要です。

## 森（forest）解釈

各インデックス $i$ を森のノードとみなし、親を
$\mathrm{parent}(i)=\max\{\,j \mid j<i \wedge S_j<S_i\,\}$（直前で値が真に小さい
最も近いインデックス、なければ根）とします。これは bad root の定義と同じ規則で、
`expand` が末尾要素を削除するとき、その要素の親がちょうど bad root になります。
順序数は自然和で $o(\text{ノード})=\bigoplus_{c:\text{子}}\omega^{o(c)}$ と与えます。

## ビルド

```
isbman build -d . -v PRSS
```

（`isbman` は `isabelle build` をディレクトリ単位の heap 分離つきでラップします。
セッションは `ROOT` に `PRSS = HOL`（`HOL-Library` 使用）として定義。`prss_paper.thy`
が `sorry` を使うため `quick_and_dirty` を設定しています。）

## 進捗

各事実の証明状況は [`task.md`](task.md) を参照。

## 出典

- Koteitan, *Purely mathematical definition of BMS*, 巨大数研究 Wiki ユーザーブログ.
- ぶしくし, *BASIC言語による巨大数のまとめ*, 巨大数研究 Wiki ユーザーブログ, 2015.
