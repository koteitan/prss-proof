theory prss_mechanized
  imports prss_paper
begin

section \<open>Mechanized proofs\<close>

subsection \<open>Basic facts about the ordinal order\<close>

lemma hlt_H_iff: "hlt (H M) (H N) \<longleftrightarrow> multp hlt M N"
  by (auto simp: hlt_iff)

lemma hlt_subset: "M \<subset># N \<Longrightarrow> hlt (H M) (H N)"
  by (simp add: hlt_H_iff subset_implies_multp)

lemma hlt_remove1: "hlt (H M) (H (add_mset x M))"
  by (rule hlt_subset) simp

lemma hlt_singleton: "hlt x y \<Longrightarrow> hlt (H {#x#}) (H {#y#})"
proof -
  assume "hlt x y"
  hence "multp hlt {#x#} {#y#}"
    by (intro one_step_implies_multp[of "{#y#}" "{#x#}" hlt "{#}", simplified]) auto
  thus ?thesis by (simp add: hlt_H_iff)
qed

lemma multp_add_mset_mono:
  assumes "multp hlt M N"
  shows "multp hlt (add_mset x M) (add_mset x N)"
proof -
  from multp_implies_one_step[OF transp_hlt assms]
  obtain I J K where "N = I + J" "M = I + K" "J \<noteq> {#}"
    and "\<forall>k\<in>#K. \<exists>j\<in>#J. hlt k j" by blast
  hence "add_mset x N = (add_mset x I) + J" "add_mset x M = (add_mset x I) + K"
    by simp_all
  thus ?thesis
    using one_step_implies_multp[of J K hlt "add_mset x I"]
          \<open>J \<noteq> {#}\<close> \<open>\<forall>k\<in>#K. \<exists>j\<in>#J. hlt k j\<close> by simp
qed

lemma hlt_under_H:
  assumes "hlt (omap C) (omap D)"
  shows "hlt (H (add_mset x (un_H (omap C)))) (H (add_mset x (un_H (omap D))))"
proof -
  have "multp hlt (un_H (omap C)) (un_H (omap D))"
    using assms by (metis H_un_H hlt_H_iff)
  thus ?thesis by (simp add: hlt_H_iff multp_add_mset_mono)
qed

text \<open>Replacing one element \<open>x\<close> of a multiset by finitely many elements that are
  all \<^const>\<open>hlt\<close>-below \<open>x\<close> strictly decreases the multiset (hence the ordinal).\<close>

lemma hlt_replace_one:
  assumes "\<forall>y \<in># K. hlt y x"
  shows "hlt (H (M + K)) (H (add_mset x M))"
proof -
  have "multp hlt (M + K) (M + {#x#})"
    by (rule one_step_implies_multp[of "{#x#}" K hlt M]) (use assms in auto)
  thus ?thesis by (simp add: hlt_H_iff)
qed

subsection \<open>Structure of \<^const>\<open>omap\<close>\<close>

text \<open>Appending a \<open>0\<close> at the end adds one top-level \<open>\<omega>\<^sup>0\<close> term.\<close>

lemma omap_snoc0: "omap (P @ [0]) = H (add_mset (H {#}) (un_H (omap P)))"
proof (induction P rule: omap.induct)
  case 1
  show ?case by simp
next
  case (2 a rest)
  let ?tw = "takeWhile (\<lambda>x. a < x) rest"
  let ?dw = "dropWhile (\<lambda>x. a < x) rest"
  have tw: "takeWhile (\<lambda>x. a < x) (rest @ [0]) = ?tw"
    by (simp add: takeWhile_tail)
  show ?case
  proof (cases "\<forall>x\<in>set rest. a < x")
    case True
    hence dwE: "?dw = []" by simp
    have dw: "dropWhile (\<lambda>x. a < x) (rest @ [0]) = [0]"
      using True by simp
    show ?thesis
      by (simp add: tw dw dwE)
  next
    case False
    have dw: "dropWhile (\<lambda>x. a < x) (rest @ [0]) = ?dw @ [0]"
      using False by (simp add: dropWhile_append)
    have "omap ((a # rest) @ [0]) = omap (a # (rest @ [0]))" by simp
    also have "\<dots> = H (add_mset (omap ?tw) (un_H (omap (?dw @ [0]))))"
      using tw dw by simp
    also have "\<dots> = H (add_mset (omap ?tw)
                        (un_H (H (add_mset (H {#}) (un_H (omap ?dw))))))"
      using "2.IH"(2) by simp
    also have "\<dots> = H (add_mset (H {#})
                        (add_mset (omap ?tw) (un_H (omap ?dw))))"
      by simp
    also have "\<dots> = H (add_mset (H {#}) (un_H (omap (a # rest))))"
      by simp
    finally show ?thesis .
  qed
qed

text \<open>(\<star>) Appending one element at the end strictly increases the ordinal:
  the new node is added to the forest, either as a new top-level root or as an
  extra child somewhere along the right spine.\<close>

lemma omap_snoc_increases: "hlt (omap C) (omap (C @ [m]))"
proof (induction C rule: omap.induct)
  case 1
  have "omap ([] @ [m]) = H (add_mset (H {#}) {#})" by simp
  thus ?case by (simp add: hlt_remove1)
next
  case (2 a rest)
  let ?tw = "takeWhile (\<lambda>x. a < x) rest"
  let ?dw = "dropWhile (\<lambda>x. a < x) rest"
  show ?case
  proof (cases "a < m \<and> (\<forall>x\<in>set rest. a < x)")
    case True
    hence am: "a < m" and allr: "\<forall>x\<in>set rest. a < x" by auto
    have twR: "?tw = rest" using allr by simp
    have tw': "takeWhile (\<lambda>x. a < x) (rest @ [m]) = rest @ [m]"
      using allr am by (simp add: takeWhile_eq_all_conv)
    have dw': "dropWhile (\<lambda>x. a < x) (rest @ [m]) = []"
      using allr am by (simp add: dropWhile_eq_Nil_conv)
    have dwe: "?dw = []" using allr by simp
    have "hlt (omap rest) (omap (rest @ [m]))"
      using "2.IH"(1) twR by simp
    hence "hlt (H {# omap rest #}) (H {# omap (rest @ [m]) #})"
      by (rule hlt_singleton)
    thus ?thesis by (simp add: twR dwe tw' dw')
  next
    case False
    have tw': "takeWhile (\<lambda>x. a < x) (rest @ [m]) = ?tw"
    proof (cases "a < m")
      case True \<comment> \<open>then not all rest > a\<close>
      with False have "\<not> (\<forall>x\<in>set rest. a < x)" by simp
      then obtain x where "x \<in> set rest" "\<not> a < x" by auto
      thus ?thesis by (simp add: takeWhile_append1)
    next
      case False
      thus ?thesis by (simp add: takeWhile_tail)
    qed
    have dw': "dropWhile (\<lambda>x. a < x) (rest @ [m]) = ?dw @ [m]"
    proof (cases "a < m")
      case True
      with False have "\<not> (\<forall>x\<in>set rest. a < x)" by simp
      thus ?thesis by (simp add: dropWhile_append)
    next
      case False
      thus ?thesis by (simp add: dropWhile_append3)
    qed
    have "hlt (omap ?dw) (omap (?dw @ [m]))" using "2.IH"(2) .
    hence "hlt (H (add_mset (omap ?tw) (un_H (omap ?dw))))
               (H (add_mset (omap ?tw) (un_H (omap (?dw @ [m])))))"
      by (rule hlt_under_H)
    thus ?thesis by (simp add: tw' dw')
  qed
qed

subsection \<open>Drop-zero step decreases the ordinal\<close>

proposition m_drop0_decreases:
  assumes "S \<noteq> []" "last S = 0"
  shows "hlt (omap (butlast S)) (omap S)"
proof -
  from assms have S: "S = butlast S @ [0]"
    by (metis append_butlast_last_id)
  let ?P = "butlast S"
  have "omap S = H (add_mset (H {#}) (un_H (omap ?P)))"
    using S omap_snoc0 by metis
  moreover have "omap ?P = H (un_H (omap ?P))" by simp
  ultimately show ?thesis
    by (metis hlt_remove1)
qed

subsection \<open>Bad-part step decreases the ordinal\<close>

text \<open>The ordinal of \<open>k\<close> consecutive copies of a bad part \<open>v # Bt\<close> (with all of
  \<open>Bt\<close> above \<open>v\<close>) is \<open>k\<close> copies of \<open>\<omega>\<^bsup>o(Bt)\<^esup>\<close>: each copy is one tree rooted at
  \<open>v\<close> with descendant forest \<open>Bt\<close>.\<close>

lemma takeWhile_cr_v:
  "takeWhile (\<lambda>x. (v::nat) < x) (concat (replicate k (v # Bt))) = []"
proof (cases k)
  case 0 thus ?thesis by simp
next
  case (Suc nat)
  have *: "concat (replicate k (v # Bt)) = v # (Bt @ concat (replicate nat (v # Bt)))"
    by (simp add: Suc)
  show ?thesis unfolding * by simp
qed

lemma dropWhile_cr_v:
  "dropWhile (\<lambda>x. (v::nat) < x) (concat (replicate k (v # Bt)))
     = concat (replicate k (v # Bt))"
proof (cases k)
  case 0 thus ?thesis by simp
next
  case (Suc nat)
  have *: "concat (replicate k (v # Bt)) = v # (Bt @ concat (replicate nat (v # Bt)))"
    by (simp add: Suc)
  show ?thesis unfolding * by simp
qed

lemma omap_rep:
  assumes "\<forall>x \<in> set Bt. v < x"
  shows "omap (concat (replicate k (v # Bt))) = H (replicate_mset k (omap Bt))"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  let ?rest = "concat (replicate k (v # Bt))"
  have tw: "takeWhile (\<lambda>x. v < x) (Bt @ ?rest) = Bt"
    using assms by (simp add: takeWhile_append takeWhile_cr_v)
  have dw: "dropWhile (\<lambda>x. v < x) (Bt @ ?rest) = ?rest"
    using assms by (simp add: dropWhile_append dropWhile_cr_v)
  have "omap (concat (replicate (Suc k) (v # Bt))) = omap (v # (Bt @ ?rest))"
    by simp
  also have "\<dots> = H (add_mset (omap Bt) (un_H (omap ?rest)))"
    by (simp add: tw dw)
  also have "\<dots> = H (add_mset (omap Bt) (replicate_mset k (omap Bt)))"
    by (simp add: Suc.IH)
  finally show ?case by simp
qed

text \<open>Computing \<open>o((v # Bt) @ [m])\<close>: \<open>m\<close> sits in \<open>v\<close>'s subtree.\<close>

lemma omap_BfM:
  assumes "\<forall>x \<in> set Bt. v < x" "v < m"
  shows "omap ((v # Bt) @ [m]) = H {# omap (Bt @ [m]) #}"
proof -
  have all: "\<forall>x \<in> set (Bt @ [m]). v < x" using assms by auto
  have tw: "takeWhile (\<lambda>x. v < x) (Bt @ [m]) = Bt @ [m]"
    using all by (simp add: takeWhile_eq_all_conv)
  have dw: "dropWhile (\<lambda>x. v < x) (Bt @ [m]) = []"
    using all by (simp add: dropWhile_eq_Nil_conv)
  have "omap ((v # Bt) @ [m]) = omap (v # (Bt @ [m]))" by simp
  also have "\<dots> = H (add_mset (omap (Bt @ [m])) (un_H (omap []))) "
    by (simp add: tw dw)
  finally show ?thesis by simp
qed

text \<open>The context-free core: replacing the maximal subtree by \<open>Suc k\<close> smaller
  siblings strictly decreases the ordinal.\<close>

lemma omap_core:
  assumes "\<forall>x \<in> set Bt. v < x" "v < m"
  shows "hlt (omap (concat (replicate (Suc k) (v # Bt)))) (omap ((v # Bt) @ [m]))"
proof -
  have L: "omap (concat (replicate (Suc k) (v # Bt)))
             = H (replicate_mset (Suc k) (omap Bt))"
    using omap_rep[OF assms(1)] .
  have R: "omap ((v # Bt) @ [m]) = H {# omap (Bt @ [m]) #}"
    using omap_BfM[OF assms] .
  have prem: "\<forall>kk \<in># replicate_mset (Suc k) (omap Bt).
                \<exists>j \<in># {# omap (Bt @ [m]) #}. hlt kk j"
    by (auto simp: omap_snoc_increases)
  have "multp hlt (replicate_mset (Suc k) (omap Bt)) {# omap (Bt @ [m]) #}"
    using one_step_implies_multp[of "{# omap (Bt @ [m]) #}"
              "replicate_mset (Suc k) (omap Bt)" hlt "{#}"] prem by simp
  hence "hlt (H (replicate_mset (Suc k) (omap Bt))) (H {# omap (Bt @ [m]) #})"
    by (simp add: hlt_H_iff)
  thus ?thesis unfolding L R .
qed

text \<open>General \<open>takeWhile\<close>/\<open>dropWhile\<close>-append helpers, kept abstract so that
  rewriting never unfolds the concrete blocks.\<close>

lemma takeWhile_append_notall:
  assumes "\<not> (\<forall>y \<in> set xs. P y)" shows "takeWhile P (xs @ ys) = takeWhile P xs"
proof -
  from assms obtain x where "x \<in> set xs" "\<not> P x" by auto
  thus ?thesis by (rule takeWhile_append1)
qed

lemma dropWhile_append_notall:
  assumes "\<not> (\<forall>y \<in> set xs. P y)" shows "dropWhile P (xs @ ys) = dropWhile P xs @ ys"
proof -
  from assms obtain x where "x \<in> set xs" "\<not> P x" by auto
  thus ?thesis by (rule dropWhile_append1)
qed

lemma takeWhile_append_all:
  "(\<forall>y \<in> set xs. P y) \<Longrightarrow> takeWhile P (xs @ ys) = xs @ takeWhile P ys"
  by (simp add: takeWhile_append2)

lemma dropWhile_append_all:
  "(\<forall>y \<in> set xs. P y) \<Longrightarrow> dropWhile P (xs @ ys) = dropWhile P ys"
  by (simp add: dropWhile_append2)

text \<open>One \<open>omap\<close>-unfolding step on a list with head \<open>g\<close>; kept with the tail
  \<open>B\<close> abstract so that rewriting never expands a concrete block.\<close>

lemma omap_cons_append:
  "omap ((g # G') @ B)
     = H (add_mset (omap (takeWhile (\<lambda>x. g < x) (G' @ B)))
                   (un_H (omap (dropWhile (\<lambda>x. g < x) (G' @ B)))))"
  by simp

text \<open>Adding a good-part context \<open>G\<close> in front, the decrease persists; the context
  is peeled by strong induction on its length until the core applies.\<close>

lemma omap_BADCTX:
  assumes "\<forall>x \<in> set Bt. v < x" "v < m" "\<forall>x \<in> set Bt. m \<le> x"
  shows "hlt (omap (G @ concat (replicate (Suc k) (v # Bt))))
             (omap (G @ (v # Bt) @ [m]))"
proof (induction G rule: length_induct)
  case (1 G)
  let ?blkK = "concat (replicate (Suc k) (v # Bt))"
  let ?blk1 = "(v # Bt) @ [m]"
  have blkK_sub: "set ?blkK \<subseteq> set (v # Bt)" by (auto simp: in_set_replicate)
  have blkK_ge: "\<forall>x \<in> set ?blkK. v \<le> x"
    using blkK_sub assms(1) by auto
  show ?case
  proof (cases G)
    case Nil
    show ?thesis using Nil omap_core[OF assms(1,2)] by simp
  next
    case (Cons g G')
    show ?thesis
    proof (cases "\<forall>x \<in> set G'. g < x")
      case False
      hence notall: "\<not> (\<forall>y \<in> set G'. g < y)" by simp
      have twK: "takeWhile (\<lambda>x. g < x) (G' @ ?blkK) = takeWhile (\<lambda>x. g < x) G'"
        by (rule takeWhile_append_notall[OF notall])
      have tw1: "takeWhile (\<lambda>x. g < x) (G' @ ?blk1) = takeWhile (\<lambda>x. g < x) G'"
        by (rule takeWhile_append_notall[OF notall])
      have dwK: "dropWhile (\<lambda>x. g < x) (G' @ ?blkK) = dropWhile (\<lambda>x. g < x) G' @ ?blkK"
        by (rule dropWhile_append_notall[OF notall])
      have dw1: "dropWhile (\<lambda>x. g < x) (G' @ ?blk1) = dropWhile (\<lambda>x. g < x) G' @ ?blk1"
        by (rule dropWhile_append_notall[OF notall])
      let ?G'' = "dropWhile (\<lambda>x. g < x) G'"
      have len: "length ?G'' < length G"
        by (simp add: Cons le_imp_less_Suc length_dropWhile_le)
      have IH: "hlt (omap (?G'' @ ?blkK)) (omap (?G'' @ ?blk1))"
        using "1.IH" len by blast
      have hltKey:
        "hlt (H (add_mset (omap (takeWhile (\<lambda>x. g < x) G')) (un_H (omap (?G'' @ ?blkK)))))
             (H (add_mset (omap (takeWhile (\<lambda>x. g < x) G')) (un_H (omap (?G'' @ ?blk1)))))"
        using IH by (rule hlt_under_H)
      have eqK: "omap (G @ ?blkK)
                   = H (add_mset (omap (takeWhile (\<lambda>x. g < x) G')) (un_H (omap (?G'' @ ?blkK))))"
        unfolding Cons by (simp only: omap_cons_append twK dwK)
      have eq1: "omap (G @ ?blk1)
                   = H (add_mset (omap (takeWhile (\<lambda>x. g < x) G')) (un_H (omap (?G'' @ ?blk1))))"
        unfolding Cons by (simp only: omap_cons_append tw1 dw1)
      show ?thesis unfolding eqK eq1 using hltKey .
    next
      case True
      show ?thesis
      proof (cases "g < v")
        case True
        have allK: "\<forall>x \<in> set (G' @ ?blkK). g < x"
        proof (intro ballI)
          fix x assume x: "x \<in> set (G' @ ?blkK)"
          show "g < x"
          proof (cases "x \<in> set G'")
            case True thus ?thesis using \<open>\<forall>x\<in>set G'. g < x\<close> by blast
          next
            case False
            hence vlex: "v \<le> x" using x blkK_ge by auto
            show ?thesis using \<open>g < v\<close> vlex by (rule less_le_trans)
          qed
        qed
        have all1: "\<forall>x \<in> set (G' @ ?blk1). g < x"
        proof (intro ballI)
          fix x assume x: "x \<in> set (G' @ ?blk1)"
          show "g < x"
          proof (cases "x \<in> set G'")
            case True thus ?thesis using \<open>\<forall>x\<in>set G'. g < x\<close> by blast
          next
            case False
            hence "x = v \<or> x \<in> set Bt \<or> x = m" using x by auto
            thus ?thesis using \<open>g < v\<close> assms(1,2) by (auto intro: less_trans)
          qed
        qed
        have twK: "takeWhile (\<lambda>x. g < x) (G' @ ?blkK) = G' @ ?blkK"
          using allK by (simp add: takeWhile_eq_all_conv)
        have dwK: "dropWhile (\<lambda>x. g < x) (G' @ ?blkK) = []"
          using allK by (simp add: dropWhile_eq_Nil_conv)
        have tw1: "takeWhile (\<lambda>x. g < x) (G' @ ?blk1) = G' @ ?blk1"
          using all1 by (simp add: takeWhile_eq_all_conv)
        have dw1: "dropWhile (\<lambda>x. g < x) (G' @ ?blk1) = []"
          using all1 by (simp add: dropWhile_eq_Nil_conv)
        have len: "length G' < length G" by (simp add: Cons)
        have IH: "hlt (omap (G' @ ?blkK)) (omap (G' @ ?blk1))"
          using "1.IH" len by blast
        have hltKey: "hlt (H {# omap (G' @ ?blkK) #}) (H {# omap (G' @ ?blk1) #})"
          using IH by (rule hlt_singleton)
        have eqK: "omap (G @ ?blkK) = H {# omap (G' @ ?blkK) #}"
          unfolding Cons by (simp only: omap_cons_append twK dwK omap.simps un_H.simps)
        have eq1: "omap (G @ ?blk1) = H {# omap (G' @ ?blk1) #}"
          unfolding Cons by (simp only: omap_cons_append tw1 dw1 omap.simps un_H.simps)
        show ?thesis unfolding eqK eq1 using hltKey .
      next
        case False
        hence gv: "\<not> g < v" .
        have allG: "\<forall>x \<in> set G'. g < x" using \<open>\<forall>x\<in>set G'. g < x\<close> .
        have blkK_cons: "?blkK = v # (Bt @ concat (replicate k (v # Bt)))" by simp
        have blk1_cons: "?blk1 = v # (Bt @ [m])" by simp
        have tK: "takeWhile (\<lambda>x. g < x) ?blkK = []" using gv unfolding blkK_cons by simp
        have dK: "dropWhile (\<lambda>x. g < x) ?blkK = ?blkK" using gv unfolding blkK_cons by simp
        have t1: "takeWhile (\<lambda>x. g < x) ?blk1 = []" using gv unfolding blk1_cons by simp
        have d1: "dropWhile (\<lambda>x. g < x) ?blk1 = ?blk1" using gv unfolding blk1_cons by simp
        have twK: "takeWhile (\<lambda>x. g < x) (G' @ ?blkK) = G'"
          using takeWhile_append_all[OF allG] tK by simp
        have dwK: "dropWhile (\<lambda>x. g < x) (G' @ ?blkK) = ?blkK"
          using dropWhile_append_all[OF allG] dK by simp
        have tw1: "takeWhile (\<lambda>x. g < x) (G' @ ?blk1) = G'"
          using takeWhile_append_all[OF allG] t1 by simp
        have dw1: "dropWhile (\<lambda>x. g < x) (G' @ ?blk1) = ?blk1"
          using dropWhile_append_all[OF allG] d1 by simp
        have hltKey: "hlt (H (add_mset (omap G') (un_H (omap ?blkK))))
                          (H (add_mset (omap G') (un_H (omap ?blk1))))"
          using omap_core[OF assms(1,2)] by (rule hlt_under_H)
        have eqK: "omap (G @ ?blkK) = H (add_mset (omap G') (un_H (omap ?blkK)))"
          unfolding Cons by (simp only: omap_cons_append twK dwK)
        have eq1: "omap (G @ ?blk1) = H (add_mset (omap G') (un_H (omap ?blk1)))"
          unfolding Cons by (simp only: omap_cons_append tw1 dw1)
        show ?thesis unfolding eqK eq1 using hltKey .
      qed
    qed
  qed
qed

proposition m_bad_decreases:
  assumes "S \<noteq> []" "0 < last S" "badset S \<noteq> {}"
  shows "hlt (omap (take (badroot S) S
                    @ concat (replicate (Suc k) (drop (badroot S) (butlast S)))))
             (omap S)"
proof -
  define m where "m = last S"
  define r where "r = badroot S"
  define Q where "Q = butlast S"
  have lenQ: "length Q = length S - 1" by (simp add: Q_def)
  \<comment> \<open>the bad set is finite and nonempty, so \<open>r\<close> is a genuine bad root\<close>
  have fin: "finite (badset S)" by (auto simp: badset_def)
  have r_in: "r \<in> badset S"
    unfolding r_def badroot_def using Max_in[OF fin assms(3)] .
  have r_lt: "r < length S - 1" and r_val: "S ! r < m"
    using r_in by (auto simp: badset_def m_def)
  have rS: "r < length S" using r_lt by (cases "length S") auto
  have r_max: "p \<le> r" if "p \<in> badset S" for p
    unfolding r_def badroot_def using Max_ge[OF fin that] .
  \<comment> \<open>structure of \<open>Q = G @ (v # Bt)\<close>\<close>
  define v where "v = Q ! r"
  define Bt where "Bt = drop (Suc r) Q"
  have rQ: "r < length Q" using r_lt lenQ by simp
  have vS: "v = S ! r" using v_def Q_def rQ by (simp add: nth_butlast lenQ)
  have B_split: "drop r Q = v # Bt"
    using rQ by (simp add: v_def Bt_def Cons_nth_drop_Suc)
  \<comment> \<open>every element of \<open>Bt\<close> is \<open>\<ge> m\<close> by maximality of the bad root\<close>
  have Bt_ge: "\<forall>x \<in> set Bt. m \<le> x"
  proof
    fix x assume "x \<in> set Bt"
    then obtain i where i: "i < length Bt" "x = Bt ! i"
      by (auto simp: in_set_conv_nth)
    hence xi: "x = Q ! (Suc r + i)" by (simp add: Bt_def)
    have idx: "Suc r + i < length Q" using i(1) by (simp add: Bt_def)
    hence p_lt: "Suc r + i < length S - 1" by (simp add: lenQ)
    have "x = S ! (Suc r + i)" using xi Q_def idx by (simp add: nth_butlast lenQ)
    moreover have "\<not> (Suc r + i \<le> r)" by simp
    ultimately have "Suc r + i \<notin> badset S" using r_max by blast
    hence "\<not> (S ! (Suc r + i) < m)" using p_lt by (auto simp: badset_def m_def)
    thus "m \<le> x" using \<open>x = S ! (Suc r + i)\<close> by simp
  qed
  have Bt_gt: "\<forall>x \<in> set Bt. v < x" using Bt_ge r_val vS by force
  have vm: "v < m" using r_val vS by simp
  \<comment> \<open>identify both sides with the \<open>omap_BADCTX\<close> statement\<close>
  have G_eq: "take r S = take r Q"
    using take_butlast[OF rS] by (simp add: Q_def)
  have S_eq: "S = take r Q @ (v # Bt) @ [m]"
  proof -
    have "Q = take r Q @ drop r Q" by simp
    also have "\<dots> = take r Q @ (v # Bt)" by (simp add: B_split)
    finally have "Q @ [m] = take r Q @ (v # Bt) @ [m]" by simp
    moreover have "S = Q @ [m]"
      using assms(1) by (simp add: Q_def m_def)
    ultimately show ?thesis by simp
  qed
  have lhs_eq: "take (badroot S) S
        @ concat (replicate (Suc k) (drop (badroot S) (butlast S)))
      = take r Q @ concat (replicate (Suc k) (v # Bt))"
    using G_eq B_split by (simp add: r_def Q_def)
  have org_eq: "omap S = omap (take r Q @ (v # Bt) @ [m])"
    by (rule arg_cong[OF S_eq])
  show ?thesis
    unfolding lhs_eq org_eq
    using omap_BADCTX[OF Bt_gt vm Bt_ge, where G = "take r Q" and k = k] .
qed

subsection \<open>Combination and termination\<close>

theorem m_step_decreases:
  assumes "step S T"
  shows "hlt (omap T) (omap S)"
  using assms
proof (cases rule: step.cases)
  case drop0
  thus ?thesis using m_drop0_decreases by simp
next
  case (bad k)
  thus ?thesis using m_bad_decreases by simp
qed

theorem m_termination: "wf {(T, S). step S T}"
proof -
  have "{(T, S). step S T} \<subseteq> inv_image {(a, b). hlt a b} omap"
    using m_step_decreases by (auto simp: inv_image_def)
  moreover have "wf (inv_image {(a, b). hlt a b} omap)"
    using wfP_hlt by (simp add: wfp_def wf_inv_image)
  ultimately show ?thesis by (blast intro: wf_subset)
qed

corollary m_no_infinite_expansion:
  "\<not> (\<exists>Seq. \<forall>i. step (Seq i) (Seq (Suc i)))"
proof
  assume "\<exists>Seq. \<forall>i. step (Seq i) (Seq (Suc i))"
  then obtain Seq where "\<forall>i. step (Seq i) (Seq (Suc i))" by blast
  hence "\<forall>i. (Seq (Suc i), Seq i) \<in> {(T, S). step S T}" by simp
  thus False using m_termination by (meson wf_iff_no_infinite_down_chain)
qed

end
