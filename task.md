# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- 下記の凡例以外のマークを増やさない。
  - 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。/ 🚫＝証明不可（偽）/ 🚨🤖＝ agent 作業中

## 進捗ツリー
- ✅ 定理（原始数列システムの停止性）[主結果: `expand` は常に有限ステップで停止する＝`m_termination`]
  - ✅ with-multiset/: 多重集合版（`HOL-Library.Multiset` 使用）
  - ✅ with-multiset/prss_ordinal.thy: ε₀ 未満の順序数核（入れ子マルチセット `hord`）
    - ✅ 順序 `hlt`（マルチセット拡大）の定義と `hlt_iff`
    - ✅ 要素サイズ補題 `size_hord_mem`
    - ✅ `hlt` の推移律 `transp_hlt`（`size` 帰納 + `transp_on_multp`）
    - ✅ `rA`（accessible 制限）の整礎性 `wfp_rA` / `wfp_multp_rA`
    - ✅ `accp_multp_hlt`（要素が accessible ⟹ マルチセットも accessible）
    - ✅ `accp_H_of_accp_multp`（構成子が accessible を保つ）
    - ✅ 整礎性 `wfP_hlt`
  - ✅ with-multiset/prss_defs.thy: PSS の定義
    - ✅ 順序数写像 `omap : nat list ⇒ hord`（森分解、takeWhile/dropWhile 左再帰、終端済）
    - ✅ サニティチェック（`omap[0,1]=ω`, `[0,1,1]=ω²`, `[0,1,2]=ω^ω`）
    - ✅ bad set `badset`, bad root `badroot` の定義
    - ✅ `expand` の1ステップ関係 `step`（drop0 / bad、コピー数 `k` 一般）
  - ✅ with-multiset/prss_paper.thy: 停止性のステートメント（sorry）
    - ✅ 命題（drop-zero 減少）/ 命題（bad-part 減少）/ 定理（step 減少）
    - ✅ 定理（停止性 = step 関係の整礎性）/ 系（無限展開列の非存在）
  - ✅ with-multiset/prss_mechanized.thy: 機械化証明（sorry なし）
    - ✅ omap 基礎補題（`hlt_subset`/`hlt_remove1`/`hlt_singleton`/`multp_add_mset_mono`/`hlt_under_H`、`omap_snoc0`）
    - ✅ (★)末尾追加で omap 真増加 `omap_snoc_increases`（`omap.induct`）
    - ✅ drop-zero 減少 `m_drop0_decreases`
    - ✅ bad-part 補助：`omap_rep`（k コピー＝k 兄弟）/ `omap_BfM` / コア減少 `omap_core`
    - ✅ append ヘルパー（`takeWhile_append_notall`/`_all` 等、`omap_cons_append`）
    - ✅ bad-part 減少 `m_bad_decreases`（`omap_BADCTX` を good part の長さ強帰納で）
    - ✅ step 減少 `m_step_decreases`
    - ✅ 停止性 `m_termination`（`wfP_hlt` + inv_image + `wf_subset`）
    - ✅ 系 `m_no_infinite_expansion`
  - ✅ without-multiset/: 多重集合なし版（`imports Main` のみ、同じ定理の再証明）
  - ✅ without-multiset/prss_nomultiset.thy: CNF 版（sorry なし）
    - ✅ カントール標準形 `datatype ord = Z | E ord ord`、順序 `olt`（`<o`）、`cnf` 述語
    - ✅ 順序の基本性質 `olt_irrefl` / `olt_trans` / `olt_total` / `ole_olt_trans`
    - ✅ 整礎性 `wfP_R`（`accp_R_Z` / `accp_R_E`（二重帰納）/ `accp_R_all` / `accp_R_any`）
    - ✅ 単一項挿入 `ins` と `cnf_ins` / `ins_comm` / 単調性 `ins_mono2`
    - ✅ 順序数写像 `omap : nat list ⇒ ord` と `cnf_omap`
    - ✅ drop-zero 減少 `m_drop0`（`olt_ins_self` / `omap_snoc0`）
    - ✅ bad-part 補助：`omap_snoc_increase` / `omap_rep` / `omap_BfM` / `omap_core`
    - ✅ bad-part 減少 `m_bad`（`omap_BADCTX`）
    - ✅ step 減少 `m_step_decreases` / 停止性 `m_termination` / 系 `m_no_infinite_expansion`
  - ✅ ドキュメント: README.md / README-ja.md（両版へのリンク）、各版の proof.md / proof-ja.md
