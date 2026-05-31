theory scratch_noms
  imports Main
begin

section \<open>Ordinals below \<open>\<epsilon>\<^sub>0\<close> as Cantor normal forms, without multisets\<close>

text \<open>
  \<^term>\<open>E a b\<close> denotes the ordinal \<open>\<omega>\<^bsup>a\<^esup> + b\<close>; \<^term>\<open>Z\<close> denotes \<open>0\<close>.
  A term is in Cantor normal form (\<^term>\<open>cnf\<close>) when exponents are non-increasing
  from left to right and hereditarily in CNF. The order \<open><o>\<close> coincides with the
  ordinal order; it is well-founded on the CNF terms.
\<close>

datatype ord = Z | E ord ord

subsection \<open>The order\<close>

fun olt :: "ord \<Rightarrow> ord \<Rightarrow> bool" (infix "<o" 50) where
  "olt Z Z = False"
| "olt Z (E _ _) = True"
| "olt (E _ _) Z = False"
| "olt (E a b) (E c d) = (olt a c \<or> (a = c \<and> olt b d))"

abbreviation ole :: "ord \<Rightarrow> ord \<Rightarrow> bool" (infix "\<le>o" 50) where
  "x \<le>o y \<equiv> (x <o y \<or> x = y)"

subsection \<open>Cantor normal form predicate\<close>

text \<open>Leading exponent of a term (\<^term>\<open>Z\<close> for \<open>0\<close>).\<close>
fun lead :: "ord \<Rightarrow> ord" where
  "lead Z = Z"
| "lead (E a _) = a"

fun cnf :: "ord \<Rightarrow> bool" where
  "cnf Z = True"
| "cnf (E a b) = (cnf a \<and> cnf b \<and> (b = Z \<or> lead b \<le>o a))"

subsection \<open>Basic order facts\<close>

lemma olt_irrefl: "\<not> x <o x"
  by (induction x) auto

lemma not_olt_Z: "\<not> x <o Z"
  by (cases x) auto

lemma olt_Z_iff: "x <o y \<Longrightarrow> y \<noteq> Z"
  using not_olt_Z by blast

lemma olt_trans: "x <o y \<Longrightarrow> y <o z \<Longrightarrow> x <o z"
proof (induction z arbitrary: x y)
  case Z
  then show ?case using not_olt_Z by blast
next
  case (E c d)
  show ?case
  proof (cases x)
    case Z
    then show ?thesis by simp
  next
    case (E a b)
    note xE = this
    from xE \<open>x <o y\<close> obtain e f where yE: "y = E e f" by (cases y) auto
    from \<open>x <o y\<close> xE yE have x_y: "a <o e \<or> (a = e \<and> b <o f)" by simp
    from \<open>y <o E c d\<close> yE have y_z: "e <o c \<or> (e = c \<and> f <o d)" by simp
    have "a <o c \<or> (a = c \<and> b <o d)"
    proof (cases "a <o e")
      case True
      show ?thesis using y_z
      proof
        assume "e <o c" thus ?thesis using True E.IH(1) by blast
      next
        assume "e = c \<and> f <o d" thus ?thesis using True by blast
      qed
    next
      case False
      with x_y have ae: "a = e" and bf: "b <o f" by auto
      show ?thesis using y_z
      proof
        assume "e <o c" thus ?thesis using ae by blast
      next
        assume "e = c \<and> f <o d" thus ?thesis using ae bf E.IH(2) by blast
      qed
    qed
    thus ?thesis using xE by simp
  qed
qed

lemma olt_total: "x <o y \<or> x = y \<or> y <o x"
proof (induction x arbitrary: y)
  case Z
  then show ?case by (cases y) auto
next
  case (E a b)
  show ?case
  proof (cases y)
    case Z
    then show ?thesis by simp
  next
    case (E c d)
    have "a <o c \<or> a = c \<or> c <o a" using E.IH(1) by blast
    moreover have "b <o d \<or> b = d \<or> d <o b" using E.IH(2) by blast
    ultimately show ?thesis unfolding \<open>y = E c d\<close> by auto
  qed
qed

lemma ole_olt_trans: "x \<le>o y \<Longrightarrow> y <o z \<Longrightarrow> x <o z"
  using olt_trans by blast

subsection \<open>Well-foundedness on CNF terms\<close>

definition R :: "ord \<Rightarrow> ord \<Rightarrow> bool" where
  "R x y \<longleftrightarrow> cnf x \<and> cnf y \<and> x <o y"

lemma accp_R_Z: "Wellfounded.accp R Z"
  by (rule accp.accI) (auto simp: R_def not_olt_Z)

text \<open>Key accessibility lemma: if exponent \<open>a\<close> is accessible and CNF, then every
  CNF term \<open>E a b\<close> with accessible tail \<open>b\<close> is accessible.\<close>

lemma accp_R_E:
  assumes a: "Wellfounded.accp R a"
  shows "cnf a \<longrightarrow> (\<forall>b. cnf (E a b) \<longrightarrow> Wellfounded.accp R b \<longrightarrow> Wellfounded.accp R (E a b))"
  using a
proof (induction a rule: accp_induct_rule)
  case (1 a)
  note IH_a = "1.IH"
  show ?case
  proof (rule impI)
    assume cnfa: "cnf a"
    have tail: "Wellfounded.accp R d" if "cnf d" "lead d <o a" for d
      using that
    proof (induction d)
      case Z
      show ?case by (rule accp_R_Z)
    next
      case (E e d')
      from \<open>cnf (E e d')\<close> have ce: "cnf e" and cd': "cnf d'"
        and bnd: "d' = Z \<or> lead d' \<le>o e" by auto
      from \<open>lead (E e d') <o a\<close> have ea: "e <o a" by simp
      have Rea: "R e a" using ce cnfa ea by (simp add: R_def)
      have ld'a: "lead d' <o a"
      proof (cases "d' = Z")
        case True then show ?thesis using ea by (cases a) (auto simp: not_olt_Z)
      next
        case False
        with bnd have "lead d' \<le>o e" by simp
        then show ?thesis using ea ole_olt_trans by blast
      qed
      have accd': "Wellfounded.accp R d'" by (rule E.IH(2)[OF cd' ld'a])
      from IH_a[OF Rea] ce have
        "\<forall>b. cnf (E e b) \<longrightarrow> Wellfounded.accp R b \<longrightarrow> Wellfounded.accp R (E e b)" by simp
      then have "cnf (E e d') \<longrightarrow> Wellfounded.accp R d' \<longrightarrow> Wellfounded.accp R (E e d')"
        by (rule spec)
      then show ?case using \<open>cnf (E e d')\<close> accd' by simp
    qed
    show "\<forall>b. cnf (E a b) \<longrightarrow> Wellfounded.accp R b \<longrightarrow> Wellfounded.accp R (E a b)"
    proof (intro allI impI)
      fix b assume cnfEab: "cnf (E a b)" and accb: "Wellfounded.accp R b"
      from accb cnfEab show "Wellfounded.accp R (E a b)"
      proof (induction b rule: accp_induct_rule)
        case (1 b)
        note IH_b = "1.IH"
        from "1.prems" have cnfb: "cnf b" by auto
        show ?case
        proof (rule accp.accI)
          fix z assume "R z (E a b)"
          then have cnfz: "cnf z" and zlt: "z <o E a b" by (auto simp: R_def)
          show "Wellfounded.accp R z"
          proof (cases z)
            case Z then show ?thesis by (simp add: accp_R_Z)
          next
            case (E c d)
            from cnfz E have cc: "cnf c" and cd: "cnf d"
              and bnd: "d = Z \<or> lead d \<le>o c" by auto
            from zlt E have disj: "c <o a \<or> (c = a \<and> d <o b)" by simp
            show ?thesis
            proof (cases "c <o a")
              case True
              have lda: "lead d <o a"
              proof (cases "d = Z")
                case True then show ?thesis using \<open>c <o a\<close> by (cases a) (auto simp: not_olt_Z)
              next
                case False with bnd have "lead d \<le>o c" by simp
                then show ?thesis using \<open>c <o a\<close> ole_olt_trans by blast
              qed
              have accd: "Wellfounded.accp R d" using tail cd lda by blast
              have Rca: "R c a" using cc cnfa \<open>c <o a\<close> by (simp add: R_def)
              from IH_a[OF Rca] cc have
                "\<forall>b'. cnf (E c b') \<longrightarrow> Wellfounded.accp R b' \<longrightarrow> Wellfounded.accp R (E c b')"
                by simp
              then have "cnf (E c d) \<longrightarrow> Wellfounded.accp R d \<longrightarrow> Wellfounded.accp R (E c d)"
                by (rule spec)
              moreover have "cnf (E c d)" using cnfz E by simp
              ultimately have "Wellfounded.accp R (E c d)" using accd by simp
              then show ?thesis using E by simp
            next
              case False
              with disj have ca: "c = a" and db: "d <o b" by auto
              have Rdb: "R d b" using cd cnfb db by (simp add: R_def)
              have cnfEad: "cnf (E a d)" using cnfz E ca by simp
              from cnfEad have "Wellfounded.accp R (E a d)" by (rule IH_b[OF Rdb])
              then show ?thesis using E ca by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma accp_R_all: "cnf x \<Longrightarrow> Wellfounded.accp R x"
proof (induction x)
  case Z
  show ?case by (rule accp_R_Z)
next
  case (E a b)
  from \<open>cnf (E a b)\<close> have ca: "cnf a" and cb: "cnf b" by auto
  from ca have accpa: "Wellfounded.accp R a" by (rule E.IH(1))
  from cb have accpb: "Wellfounded.accp R b" by (rule E.IH(2))
  have "\<forall>b. cnf (E a b) \<longrightarrow> Wellfounded.accp R b \<longrightarrow> Wellfounded.accp R (E a b)"
    using accp_R_E[OF accpa] ca by simp
  then have "cnf (E a b) \<longrightarrow> Wellfounded.accp R b \<longrightarrow> Wellfounded.accp R (E a b)"
    by (rule spec)
  then show ?case using \<open>cnf (E a b)\<close> accpb by simp
qed

lemma accp_R_any: "Wellfounded.accp R x"
proof (cases "cnf x")
  case True then show ?thesis by (rule accp_R_all)
next
  case False
  show ?thesis by (rule accp.accI) (use False in \<open>auto simp: R_def\<close>)
qed

theorem wfP_R: "wfP R"
  by (rule accp_wfpI) (rule allI, rule accp_R_any)

section \<open>Inserting a principal term \<open>\<omega>\<^bsup>e\<^esup>\<close> into a CNF\<close>

fun ins :: "ord \<Rightarrow> ord \<Rightarrow> ord" where
  "ins e Z = E e Z"
| "ins e (E a b) = (if a <o e then E e (E a b) else E a (ins e b))"

lemma lead_ins: "lead (ins e y) = e \<or> lead (ins e y) = lead y"
  by (cases y) auto

lemma cnf_ins: "cnf e \<Longrightarrow> cnf y \<Longrightarrow> cnf (ins e y)"
proof (induction y)
  case Z
  then show ?case by simp
next
  case (E a b)
  from \<open>cnf (E a b)\<close> have ca: "cnf a" and cb: "cnf b"
    and bnd: "b = Z \<or> lead b \<le>o a" by auto
  show ?case
  proof (cases "a <o e")
    case True
    then show ?thesis using \<open>cnf e\<close> \<open>cnf (E a b)\<close> by auto
  next
    case False
    hence ea: "e \<le>o a" using olt_total by blast
    have cib: "cnf (ins e b)" using E.IH \<open>cnf e\<close> cb by blast
    have "ins e b = Z \<or> lead (ins e b) \<le>o a"
    proof -
      have "lead (ins e b) = e \<or> lead (ins e b) = lead b" by (rule lead_ins)
      then show ?thesis using ea bnd by auto
    qed
    then show ?thesis using False ca cib by auto
  qed
qed

text \<open>Inserting commutes: order of insertion does not matter.\<close>
lemma ins_comm: "ins e (ins f y) = ins f (ins e y)"
proof (induction y)
  case Z
  show ?case
  proof (cases "e <o f")
    case True
    hence "\<not> f <o e" using olt_trans olt_irrefl by blast
    then show ?thesis using True by simp
  next
    case False
    show ?thesis
    proof (cases "f <o e")
      case True
      hence "\<not> e <o f" using olt_trans olt_irrefl by blast
      then show ?thesis using True by simp
    next
      case False
      with \<open>\<not> e <o f\<close> have "e = f" using olt_total by blast
      then show ?thesis by simp
    qed
  qed
next
  case (E a b)
  consider (bb) "\<not> a <o e \<and> \<not> a <o f" | (ee) "a <o e \<and> a <o f"
    | (ef) "a <o e \<and> \<not> a <o f" | (fe) "\<not> a <o e \<and> a <o f" by blast
  then show ?case
  proof cases
    case bb
    then show ?thesis by (simp add: E.IH)
  next
    case ee
    consider "e <o f" | "f <o e" | "e = f" using olt_total by blast
    then show ?thesis
    proof cases
      case 1 hence "\<not> f <o e" using olt_trans olt_irrefl by blast
      then show ?thesis using ee \<open>e <o f\<close> by simp
    next
      case 2 hence "\<not> e <o f" using olt_trans olt_irrefl by blast
      then show ?thesis using ee \<open>f <o e\<close> by simp
    next
      case 3 then show ?thesis using ee by simp
    qed
  next
    case ef
    hence "f \<le>o a" using olt_total by blast
    hence "f <o e" using ef ole_olt_trans by blast
    hence "\<not> e <o f" using olt_trans olt_irrefl by blast
    then show ?thesis using ef \<open>f <o e\<close> by simp
  next
    case fe
    hence "e \<le>o a" using olt_total by blast
    hence "e <o f" using fe ole_olt_trans by blast
    hence "\<not> f <o e" using olt_trans olt_irrefl by blast
    then show ?thesis using fe \<open>e <o f\<close> by simp
  qed
qed

section \<open>The ordinal measure of a primitive sequence\<close>

function omap :: "nat list \<Rightarrow> ord" where
  "omap [] = Z"
| "omap (a # rest) =
     ins (omap (takeWhile (\<lambda>x. a < x) rest)) (omap (dropWhile (\<lambda>x. a < x) rest))"
  by pat_completeness auto
termination
  by (relation "measure length")
     (auto simp: le_imp_less_Suc length_takeWhile_le
            intro: le_less_trans[OF length_dropWhile_le])

lemma cnf_omap: "cnf (omap S)"
proof (induction S rule: omap.induct)
  case 1 then show ?case by simp
next
  case (2 a rest)
  show ?case using 2(1) 2(2) by (simp add: cnf_ins)
qed

section \<open>Each expansion step strictly decreases the measure\<close>

text \<open>Inserting a term strictly increases the value.\<close>
lemma olt_ins_self: "y <o ins e y"
proof (induction y)
  case Z
  show ?case by simp
next
  case (E a b)
  show ?case
  proof (cases "a <o e")
    case True then show ?thesis by simp
  next
    case False then show ?thesis using E.IH(2) by simp
  qed
qed

text \<open>Appending a trailing \<open>0\<close> inserts the least term \<open>\<omega>\<^sup>0\<close>.\<close>
lemma omap_snoc0: "omap (P @ [0]) = ins Z (omap P)"
proof (induction P rule: omap.induct)
  case 1
  show ?case by simp
next
  case (2 a rest)
  have tw: "takeWhile (\<lambda>x. a < x) (rest @ [0]) = takeWhile (\<lambda>x. a < x) rest"
    by (simp add: takeWhile_tail)
  have dw: "dropWhile (\<lambda>x. a < x) (rest @ [0]) = dropWhile (\<lambda>x. a < x) rest @ [0]"
    by (simp add: dropWhile_append3)
  have "omap ((a # rest) @ [0]) = omap (a # (rest @ [0]))" by simp
  also have "\<dots> = ins (omap (takeWhile (\<lambda>x. a < x) rest))
                      (omap (dropWhile (\<lambda>x. a < x) rest @ [0]))"
    using tw dw by simp
  also have "\<dots> = ins (omap (takeWhile (\<lambda>x. a < x) rest))
                      (ins Z (omap (dropWhile (\<lambda>x. a < x) rest)))"
    using 2(2) by simp
  also have "\<dots> = ins Z (ins (omap (takeWhile (\<lambda>x. a < x) rest))
                              (omap (dropWhile (\<lambda>x. a < x) rest)))"
    by (rule ins_comm)
  also have "\<dots> = ins Z (omap (a # rest))" by simp
  finally show ?case .
qed

proposition m_drop0:
  assumes "S \<noteq> []" "last S = 0"
  shows "omap (butlast S) <o omap S"
proof -
  from assms have "S = butlast S @ [0]" by (metis append_butlast_last_id)
  hence "omap S = ins Z (omap (butlast S))" using omap_snoc0 by metis
  thus ?thesis using olt_ins_self by metis
qed

end
