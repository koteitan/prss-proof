[English](README.md) | [Japanese](README-ja.md)

# prss-proof

Version: **v0.1.12**

バシク氏の **原始数列システム（Primitive Sequence System）** が必ず停止する
ことを、**Isabelle/HOL** で機械的に検証したものです。

方針は古典的です。各原始数列を $\varepsilon_0$ 未満の順序数に写し、`expand` の各
ステップでその順序数が真に減少することを示します。 $\varepsilon_0$ 未満の順序数は
整礎なので、無限に展開が続くことはありません。

## 2つの独立した証明

同じ定理を、 $\varepsilon_0$ 未満の順序数の**2通りの表現**で証明しています。
各ディレクトリは自己完結しています。

| | [`with-multiset/`](with-multiset/proof-ja.md) | [`without-multiset/`](without-multiset/proof-ja.md) |
|---|---|---|
| 証明文書 | [proof-ja.md](with-multiset/proof-ja.md) ([en](with-multiset/proof.md)) | [proof-ja.md](without-multiset/proof-ja.md) ([en](without-multiset/proof.md)) |
| 順序数の表現 | 遺伝的有限多重集合 | カントール標準形 |
| データ型 | `hord = H "hord multiset"` | `ord = Z \| E ord ord` |
| 順序 | 多重集合拡大 `hlt` | 辞書式 `olt`（`<o`） |
| 整礎性 | `wfP_hlt`（ライブラリ `wfp_multp` 経由） | `wfP_R`（自前の accessibility 論法） |
| import | `HOL-Library.Multiset` | `Main` のみ |
| 規模 | 短い | 約890行 |

**どちらを読むか。** 推奨は `with-multiset/` です。森の子は本来**無順序**なので
多重集合が素直な表現であり、多重集合順序の整礎性（Dershowitz–Manna）は
`HOL-Library.Multiset` からタダで手に入ります。`without-multiset/` は
多重集合の概念が**回避可能**であることの実証です。カントール標準形は指数の**列**なので、
全補題にソート不変条件（`cnf`）を持ち回り、 $\varepsilon_0$ の整礎性を一から証明する
必要があります。結果としてかなり長くなりますが、それこそが要点で、
多重集合ライブラリが何を買ってくれていたのかを測っています。

どちらの証明も**順序数ライブラリを import していません**。作っているのは整礎順序を持つ
データ型だけで、「順序数」は読み方であって形式的な材料ではありません。

## 証明した内容

どちらの版でも、原始数列上の展開関係 `step` は整礎である（`m_termination`）。
同値に、無限展開列は存在しない（`m_no_infinite_expansion`）。いずれも各ステップで
順序数写像 `omap` が真に減少することから従います。

## ファイル構成

```
with-multiset/
  prss_ordinal.thy       ε₀ 未満の順序数を遺伝的有限多重集合で構成、wfP_hlt
  prss_defs.thy          原始数列、step、bad root、omap
  prss_paper.thy         命題・主定理のステートメント（すべて sorry）
  prss_mechanized.thy    それらを解消する機械化証明
  proof.md / proof-ja.md 人間向けの数式証明
without-multiset/
  prss_nomultiset.thy    証明全体。imports Main のみ
  proof.md / proof-ja.md 人間向けの数式証明
ROOT                     Isabelle セッション PRSS（両方をビルド）
task.md                  各事実の証明状況
```

命名規則：`with-multiset/` では論文側の主張は `p_*`、機械化証明は `m_*`。

## 森（forest）解釈

各インデックス $i$ を森のノードとみなし、親を
$\mathrm{parent}(i)=\max\lbrace j \mid j<i \wedge S_j<S_i \rbrace$（直前で値が真に小さい
最も近いインデックス、なければ根）とします。これは bad root の定義と同じ規則で、
`expand` が末尾要素を削除するとき、その要素の親がちょうど bad root になります。
順序数は自然和で $o(\text{ノード})=\bigoplus_{c:\text{子}}\omega^{o(c)}$ と与えます。

## ビルド

```
isbman build -d . -v PRSS
```

`PRSS` セッションが両方の証明をビルドします。（`isbman` は `isabelle build` を
ディレクトリ単位の heap 分離つきでラップします。`with-multiset/prss_paper.thy` が
`sorry` を使うため `quick_and_dirty` を設定しています。）

## 進捗

各事実の証明状況は [`task.md`](task.md) を参照。

## 出典

- Koteitan, *Purely mathematical definition of BMS*, 巨大数研究 Wiki ユーザーブログ.
- バシク, *BASIC言語による巨大数のまとめ*, 巨大数研究 Wiki ユーザーブログ, 2015.
