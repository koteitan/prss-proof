theory prss_ordinal
  imports "HOL-Library.Multiset"
begin

section \<open>Ordinals below \<open>\<epsilon>\<^sub>0\<close> as hereditarily finite multisets\<close>

text \<open>
  We model the ordinals below \<open>\<epsilon>\<^sub>0\<close> by hereditarily finite multisets.
  Intuitively, \<^term>\<open>H M\<close> denotes the natural (Hessenberg) sum
  \<open>\<Oplus>\<^bsub>x \<in> M\<^esub> \<omega>\<^bsup>val x\<^esup>\<close>, so \<^term>\<open>H {#}\<close> is the ordinal \<open>0\<close>.
  Comparison is the multiset extension of the same order on the exponents:
  this is exactly the ordering of Cantor normal forms below \<open>\<epsilon>\<^sub>0\<close>, and it is
  well-founded.
\<close>

datatype hord = H "hord multiset"

subsection \<open>The order\<close>

inductive hlt :: "hord \<Rightarrow> hord \<Rightarrow> bool" where
  hltI: "multp hlt M N \<Longrightarrow> hlt (H M) (H N)"

lemma hlt_iff: "hlt a b \<longleftrightarrow> (\<exists>M N. a = H M \<and> b = H N \<and> multp hlt M N)"
  by (cases a; cases b) (auto intro: hltI elim: hlt.cases)

subsection \<open>Transitivity\<close>

text \<open>The size of an element is smaller than the size of the multiset that
  contains it, which lets us prove transitivity by induction on \<^term>\<open>size\<close>.\<close>

lemma size_hord_lt_add: "size (H M) < size (H (add_mset y M))"
  by simp

lemma size_hord_mem: "x \<in># M \<Longrightarrow> size x < size (H M)"
proof (induction M)
  case empty
  then show ?case by simp
next
  case (add y M)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis by simp
  next
    case False
    with add.prems have "x \<in># M" by simp
    with add.IH have "size x < size (H M)" .
    also have "size (H M) < size (H (add_mset y M))" by (rule size_hord_lt_add)
    finally show ?thesis .
  qed
qed

lemma transp_on_size_hlt: "transp_on {x. size x \<le> k} hlt"
proof (induction k rule: less_induct)
  case (less k)
  show ?case
  proof (rule transp_onI)
    fix a b c
    assume mem: "a \<in> {x. size x \<le> k}" "b \<in> {x. size x \<le> k}" "c \<in> {x. size x \<le> k}"
      and ab: "hlt a b" and bc: "hlt b c"
    from ab obtain A B where aA: "a = H A" and bB: "b = H B" and AB: "multp hlt A B"
      by (auto simp: hlt_iff)
    from bc bB obtain C where cC: "c = H C" and BC: "multp hlt B C"
      by (auto simp: hlt_iff)
    \<comment> \<open>elements of \<open>A,B,C\<close> have strictly smaller size, hence size \<open>\<le> k-1\<close>\<close>
    have elem_small: "size x \<le> k - 1" if "x \<in># A \<or> x \<in># B \<or> x \<in># C" for x
    proof -
      from that have "size x < size a \<or> size x < size b \<or> size x < size c"
        using size_hord_mem[of x A] size_hord_mem[of x B] size_hord_mem[of x C]
        by (auto simp: aA bB cC)
      with mem show ?thesis by auto
    qed
    have klt: "k - 1 < k"
    proof -
      have "0 < size a" by (simp add: aA)
      with mem show ?thesis by auto
    qed
    have tr: "transp_on {x. size x \<le> k - 1} hlt" using less.IH[OF klt] .
    have setsub: "set_mset X \<subseteq> {x. size x \<le> k - 1}"
      if "X = A \<or> X = B \<or> X = C" for X
      using elem_small that by auto
    have "transp_on {A, B, C} (multp hlt)"
      by (rule transp_on_multp[OF tr]) (use setsub in auto)
    hence "multp hlt A C"
      using AB BC by (auto dest: transp_onD)
    thus "hlt a c" by (simp add: aA cC hltI)
  qed
qed

lemma transp_hlt: "transp hlt"
proof (rule transpI)
  fix a b c assume ab: "hlt a b" and bc: "hlt b c"
  let ?k = "max (size a) (max (size b) (size c))"
  have tr: "transp_on {x. size x \<le> ?k} hlt" by (rule transp_on_size_hlt)
  have "a \<in> {x. size x \<le> ?k}" "b \<in> {x. size x \<le> ?k}" "c \<in> {x. size x \<le> ?k}"
    by auto
  with tr ab bc show "hlt a c" by (meson transp_onD)
qed

subsection \<open>Well-foundedness\<close>

text \<open>The relation \<^term>\<open>rA\<close> is \<^term>\<open>hlt\<close> restricted to an accessible source.
  Every element is accessible under \<^term>\<open>rA\<close>, so \<^term>\<open>rA\<close> is well-founded, and
  hence so is its multiset extension.\<close>

definition rA :: "hord \<Rightarrow> hord \<Rightarrow> bool" where
  "rA x y \<longleftrightarrow> hlt x y \<and> Wellfounded.accp hlt x"

lemma rA_le_hlt: "rA \<le> hlt"
  by (auto simp: rA_def)

lemma wfp_rA: "wfp rA"
proof (rule accp_wfpI, rule allI)
  fix x
  have acc_imp: "Wellfounded.accp hlt z \<Longrightarrow> Wellfounded.accp rA z" for z
    using accp_subset[OF rA_le_hlt] by (auto simp: le_fun_def)
  show "Wellfounded.accp rA x"
  proof (rule accp.accI)
    fix y assume "rA y x"
    hence "Wellfounded.accp hlt y" by (simp add: rA_def)
    thus "Wellfounded.accp rA y" by (rule acc_imp)
  qed
qed

lemma wfp_multp_rA: "wfp (multp rA)"
  using wfp_rA by (rule wfp_multp)

text \<open>If all elements of \<^term>\<open>M\<close> are accessible under \<^term>\<open>hlt\<close>, then \<^term>\<open>M\<close>
  is accessible under \<^term>\<open>multp hlt\<close>.\<close>

lemma accp_multp_hlt:
  assumes "\<forall>x \<in># M. Wellfounded.accp hlt x"
  shows "Wellfounded.accp (multp hlt) M"
proof -
  have "Wellfounded.accp (multp rA) M"
    using wfp_multp_rA by (simp add: wfp_iff_accp)
  thus ?thesis using assms
  proof (induction M rule: accp_induct_rule)
    case (1 M)
    show ?case
    proof (rule accp.accI)
      fix N assume "multp hlt N M"
      from multp_implies_one_step[OF transp_hlt this]
      obtain I J K where dec: "M = I + J" "N = I + K" "J \<noteq> {#}"
        and Klt: "\<forall>k \<in># K. \<exists>x \<in># J. hlt k x" by blast
      \<comment> \<open>every element of \<open>N = I + K\<close> is accessible\<close>
      have accN: "\<forall>x \<in># N. Wellfounded.accp hlt x"
      proof
        fix x assume "x \<in># N"
        then consider "x \<in># I" | "x \<in># K" using dec by auto
        thus "Wellfounded.accp hlt x"
        proof cases
          case 1 thus ?thesis using "1.prems" dec by auto
        next
          case 2
          then obtain y where "y \<in># J" "hlt x y" using Klt by blast
          hence "Wellfounded.accp hlt y" using "1.prems" dec by auto
          thus ?thesis using \<open>hlt x y\<close> by (rule accp_downward)
        qed
      qed
      \<comment> \<open>the one step is also an \<open>rA\<close> step\<close>
      have "\<forall>k \<in># K. \<exists>x \<in># J. rA k x"
      proof
        fix k assume "k \<in># K"
        then obtain x where "x \<in># J" "hlt k x" using Klt by blast
        moreover have "Wellfounded.accp hlt k"
          using accN \<open>k \<in># K\<close> dec by auto
        ultimately show "\<exists>x \<in># J. rA k x" by (auto simp: rA_def)
      qed
      hence "multp rA N M"
        using dec one_step_implies_multp[of J K rA I] by simp
      thus "Wellfounded.accp (multp hlt) N"
        using "1.IH" accN by blast
    qed
  qed
qed

text \<open>The constructor preserves accessibility.\<close>

lemma accp_H_of_accp_multp:
  assumes "Wellfounded.accp (multp hlt) M"
  shows "Wellfounded.accp hlt (H M)"
  using assms
proof (induction M rule: accp_induct_rule)
  case (1 M)
  show ?case
  proof (rule accp.accI)
    fix y assume "hlt y (H M)"
    then obtain N where "y = H N" "multp hlt N M" by (auto simp: hlt_iff)
    thus "Wellfounded.accp hlt y" using "1.IH" by blast
  qed
qed

lemma accp_hlt_H:
  assumes "\<forall>x \<in># M. Wellfounded.accp hlt x"
  shows "Wellfounded.accp hlt (H M)"
  using assms accp_multp_hlt accp_H_of_accp_multp by blast

theorem wfP_hlt: "wfP hlt"
proof (rule accp_wfpI, rule allI)
  show "Wellfounded.accp hlt x" for x
    by (induction x) (auto intro: accp_hlt_H)
qed

end
