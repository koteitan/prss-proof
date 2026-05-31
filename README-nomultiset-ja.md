[← 戻る](README-ja.md) | [English](README-nomultiset.md) | [Japanese](README-nomultiset-ja.md)

# 多重集合を使わない停止性証明（ブランチ `without-multiset`）

`prss_nomultiset.thy` は、`main` ブランチと**同じ停止性**を、`HOL-Library.Multiset`
を**一切使わずに**証明したものです（`imports Main` のみ）。

## 何をしているか

ε₀ 未満の順序数を、二分データ型による**カントール標準形 (CNF)** で表す:

```isabelle
datatype ord = Z | E ord ord        (* E a b  =  ω^a + b *)
```

`cnf` 述語(指数が降順・遺伝的に CNF)を伴う。順序 `olt`（`<o`）は CNF の辞書式順序。
本ファイルは `Main` 以外の外部ライブラリなしで次を証明する。

| 結果 | 主張 |
|---|---|
| `wfP_R` | CNF 項に制限した `olt` の整礎性（`wfp_multp` を使わず、自前の accessibility 論法で構築） |
| `omap` | 測度 `nat list ⇒ ord`。単一項挿入 `ins`（ω^e を CNF に挿入）で定義 |
| `cnf_omap` | `omap` は常に CNF を返す |
| `m_drop0` / `m_bad` | 各展開ステップが `omap` を真に減少させる |
| `m_termination` | `wf {(T, S). step S T}` |
| `m_no_infinite_expansion` | 無限展開列は存在しない |

## なぜ多重集合版より大変か

順序付きの CNF 表現は、ソート不変条件なしには整礎になりません
（例えば `[1] ≻ [0,1] ≻ [0,0,1] ≻ …` という昇順=非CNF項で無限下降が作れる）。
そのため本証明は次を要する:

- ε₀ の整礎性を一から証明（`main` が `wfp_multp` からタダで得る `accp` 論法を自前で実装）；
- 自然和を挿入 `ins` として定義し、`ins_comm`・`cnf_ins`・**単調性** `ins_mono2` を手で証明
  （`main` はこれらをマルチセット順序の one-step 補題から得る）；
- 全補題に CNF/ソート性を持ち回る。

結果（約890行）は `main` の多重集合版よりかなり長く、この問題には多重集合の方が安い表現
であることを裏づける。森の子は本来無順序なので、順序を商で消す（多重集合）と上記がすべて
不要になる。本ブランチは「多重集合なしでも**可能**である」ことの実証であり、推奨ではない。

## ビルド

```
isbman build -d . -v PRSS
```
（`prss_nomultiset` は `ROOT` に登録済み。他の theory とは独立。）
