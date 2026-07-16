theory prss_paper
  imports prss_defs
begin

section \<open>Statements: termination of the Primitive Sequence System\<close>

text \<open>
  This theory states the propositions and the main theorem; all proofs are
  deferred to \<^file>\<open>prss_mechanized.thy\<close> (here they are \<^theory_text>\<open>sorry\<close>).

  The whole argument is: the forest ordinal \<^const>\<open>omap\<close> strictly decreases at
  every expansion step, and the ordinal order \<^const>\<open>hlt\<close> is well-founded
  (\<^theory_text>\<open>wfP_hlt\<close>); hence the expansion relation is well-founded, i.e. \<open>expand\<close>
  always reaches the empty sequence after finitely many steps.
\<close>

subsection \<open>Each step strictly decreases the ordinal\<close>

text \<open>Removing a trailing \<open>0\<close> drops one top-level term \<open>\<omega>\<^sup>0\<close>.\<close>

proposition p_drop0_decreases:
  assumes "S \<noteq> []" "last S = 0"
  shows "hlt (omap (butlast S)) (omap S)"
  sorry

text \<open>The bad-part copy replaces the maximal subtree \<open>\<omega>\<^bsup>o(tl B @ [m])\<^esup>\<close> by
  finitely many smaller siblings \<open>\<omega>\<^bsup>o(tl B)\<^esup>\<close>.\<close>

proposition p_bad_decreases:
  assumes "S \<noteq> []" "0 < last S" "badset S \<noteq> {}"
  shows "hlt (omap (take (badroot S) S
                    @ concat (replicate (Suc k) (drop (badroot S) (butlast S)))))
             (omap S)"
  sorry

theorem p_step_decreases:
  assumes "step S T"
  shows "hlt (omap T) (omap S)"
  sorry

subsection \<open>Main theorem\<close>

text \<open>The expansion relation is well-founded: there is no infinite expansion
  sequence, i.e. \<open>expand\<close> terminates.\<close>

theorem p_termination: "wf {(T, S). step S T}"
  sorry

corollary p_no_infinite_expansion:
  "\<not> (\<exists>Seq. \<forall>i. step (Seq i) (Seq (Suc i)))"
  sorry

end
