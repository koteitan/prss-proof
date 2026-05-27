theory prss_defs
  imports prss_ordinal
begin

section \<open>The Primitive Sequence System and its ordinal map\<close>

text \<open>
  A primitive sequence is a finite list of natural numbers \<open>S = (S\<^sub>0,\<dots>,S\<^bsub>X-1\<^esub>)\<close>.
  The expansion rule (Bashicu, BM-restricted to a single row) is, with a counter
  \<open>n\<close> and activation function \<open>f\<close>:
  \<^item> \<open>expand([n]) = n\<close>;
  \<^item> if \<open>S\<^bsub>X-1\<^esub> = 0\<close>: \<open>expand(S[n]) = expand((S\<^sub>0,\<dots>,S\<^bsub>X-2\<^esub>)[f n])\<close>;
  \<^item> otherwise, with bad root \<open>r = max {p | S\<^sub>p < S\<^bsub>X-1\<^esub> \<and> p < X-1}\<close>,
    good part \<open>G = (S\<^sub>0,\<dots>,S\<^bsub>r-1\<^esub>)\<close> and bad part \<open>B = (S\<^sub>r,\<dots>,S\<^bsub>X-2\<^esub>)\<close>:
    \<open>expand(S[n]) = expand(G B B\<cdots>B [f n])\<close> with \<open>f n + 1\<close> copies of \<open>B\<close>.

  Termination of \<open>expand\<close> is independent of the counter and of \<open>f\<close>: it holds iff
  the sequence part always reaches the empty list. We therefore study the rewriting
  of the sequence part alone, parametrised by the number of copies.
\<close>

subsection \<open>The ordinal map (forest ordinal)\<close>

text \<open>Selector for the ordinal datatype.\<close>

fun un_H :: "hord \<Rightarrow> hord multiset" where
  "un_H (H M) = M"

lemma H_un_H[simp]: "H (un_H x) = x"
  by (cases x) simp

text \<open>
  Each primitive sequence denotes a forest: index \<open>i\<close> is a child of the nearest
  earlier index with a strictly smaller value, and a root otherwise. The ordinal
  is the natural sum \<open>\<Oplus> \<omega>\<^bsup>o(subtree)\<^esup>\<close> over the trees. The forest decomposes
  by reading the first element \<open>a\<close> as a root: its descendants are the maximal
  following block of values \<open>> a\<close>, and the remaining suffix continues the forest.
\<close>

function omap :: "nat list \<Rightarrow> hord" where
  "omap [] = H {#}"
| "omap (a # rest) =
     H (add_mset (omap (takeWhile (\<lambda>x. a < x) rest))
                 (un_H (omap (dropWhile (\<lambda>x. a < x) rest))))"
  by pat_completeness auto
termination
  by (relation "measure length")
     (auto simp: le_imp_less_Suc length_takeWhile_le
            intro: le_less_trans[OF length_dropWhile_le])

subsection \<open>Sanity checks (small values)\<close>

lemma omap_single: "omap [a] = H {# H {#} #}"
  by simp

lemma "omap [0,1] = H {# H {# H {#} #} #}"  \<comment> \<open>\<open>\<omega>\<close>\<close>
  by simp

lemma "omap [0,1,1] = H {# H {# H {#}, H {#} #} #}"  \<comment> \<open>\<open>\<omega>\<^sup>2\<close>\<close>
  by (simp add: numeral_2_eq_2)

lemma "omap [0,1,2] = H {# H {# H {# H {#} #} #} #}"  \<comment> \<open>\<open>\<omega>\<^bsup>\<omega>\<^esup>\<close>\<close>
  by simp

subsection \<open>The expansion step\<close>

definition badset :: "nat list \<Rightarrow> nat set" where
  "badset S = {p. p < length S - 1 \<and> S ! p < last S}"

definition badroot :: "nat list \<Rightarrow> nat" where
  "badroot S = Max (badset S)"

text \<open>One expansion step on the sequence part. The number \<open>k\<close> of extra copies
  of the bad part (\<open>= f n\<close>) is arbitrary, so the relation captures every counter.\<close>

inductive step :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  drop0: "S \<noteq> [] \<Longrightarrow> last S = 0 \<Longrightarrow> step S (butlast S)"
| bad:   "S \<noteq> [] \<Longrightarrow> 0 < last S \<Longrightarrow> badset S \<noteq> {} \<Longrightarrow>
            T = take (badroot S) S
                @ concat (replicate (Suc k) (drop (badroot S) (butlast S))) \<Longrightarrow>
            step S T"

end
