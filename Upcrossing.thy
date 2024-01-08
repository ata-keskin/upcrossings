theory Upcrossing
  imports Stopping_Time Martingales.Martingale
begin                                                            

section \<open>Upcrossings and Downcrossings\<close>

context nat_filtered_measure
begin

context 
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and a b :: real
    and N :: nat
begin

primrec upcrossing :: "nat \<Rightarrow> 'a \<Rightarrow> nat" where
  "upcrossing 0 = (\<lambda>\<omega>. 0)" |
  "upcrossing (Suc n) = (\<lambda>\<omega>. hitting_time X {b..} (hitting_time X {..a} (upcrossing n \<omega>) N \<omega>) N \<omega>)"

definition downcrossing :: "nat \<Rightarrow> 'a \<Rightarrow> nat" where
  "downcrossing n = (\<lambda>\<omega>. hitting_time X {..a} (upcrossing n \<omega>) N \<omega>)"

lemma upcrossing_simps:
  "upcrossing 0 = (\<lambda>\<omega>. 0)"
  "upcrossing (Suc n) = (\<lambda>\<omega>. hitting_time X {b..} (downcrossing n \<omega>) N \<omega>)"
  by (auto simp add: downcrossing_def)

lemma downcrossing_simps:
  "downcrossing 0 = hitting_time X {..a} 0 N"
  "downcrossing n = (\<lambda>\<omega>. hitting_time X {..a} (upcrossing n \<omega>) N \<omega>)"
  by (auto simp add: downcrossing_def)

declare upcrossing.simps[simp del]

lemma upcrossing_le: "upcrossing n \<omega> \<le> N"
  by (cases n) (auto simp add: upcrossing_simps hitting_time_le)

lemma downcrossing_le: "downcrossing n \<omega> \<le> N"
  by (cases n) (auto simp add: downcrossing_simps hitting_time_le)

lemma upcrossing_le_downcrossing: "upcrossing n \<omega> \<le> downcrossing n \<omega>"
  unfolding downcrossing_simps by (auto intro: hitting_time_ge upcrossing_le)

lemma downcrossing_le_upcrossing_Suc: "downcrossing n \<omega> \<le> upcrossing (Suc n) \<omega>"
  unfolding upcrossing_simps by (auto intro: hitting_time_ge downcrossing_le)

lemma upcrossing_mono:
  assumes "n \<le> m"
  shows "upcrossing n \<omega> \<le> upcrossing m \<omega>"
  using order_trans[OF upcrossing_le_downcrossing downcrossing_le_upcrossing_Suc] assms
  by (rule lift_Suc_mono_le)

lemma downcrossing_mono:
  assumes "n \<le> m"
  shows "downcrossing n \<omega> \<le> downcrossing m \<omega>"
  using order_trans[OF downcrossing_le_upcrossing_Suc upcrossing_le_downcrossing] assms
  by (rule lift_Suc_mono_le)

lemma stopped_value_upcrossing:
  assumes "upcrossing (Suc n) \<omega> \<noteq> N"
  shows "stopped_value X (upcrossing (Suc n)) \<omega> \<ge> b"
proof -
  have *: "upcrossing (Suc n) \<omega> < N" using le_neq_implies_less upcrossing_le assms by presburger
  have "\<exists>j \<in> {downcrossing n \<omega>..upcrossing (Suc n) \<omega>}. X j \<omega> \<in> {b..}"
    using hitting_time_le_iff[THEN iffD1, OF *] upcrossing_simps by fastforce
  then obtain j where j: "j \<in> {downcrossing n \<omega>..N}" "X j \<omega> \<in> {b..}" using * by (meson atLeastatMost_subset_iff le_refl subsetD upcrossing_le)
  thus ?thesis using stopped_value_hitting_time_mem[of j _ _ X] unfolding upcrossing_simps stopped_value_def by blast
qed

lemma stopped_value_downcrossing:
  assumes "downcrossing n \<omega> \<noteq> N"
  shows "stopped_value X (downcrossing n) \<omega> \<le> a"
proof -
  have *: "downcrossing n \<omega> < N" using le_neq_implies_less downcrossing_le assms by presburger
  have "\<exists>j \<in> {upcrossing n \<omega>..downcrossing n \<omega>}. X j \<omega> \<in> {..a}"
    using hitting_time_le_iff[THEN iffD1, OF *] downcrossing_simps by fastforce
  then obtain j where j: "j \<in> {upcrossing n \<omega>..N}" "X j \<omega> \<in> {..a}" using * by (meson atLeastatMost_subset_iff le_refl subsetD downcrossing_le)
  thus ?thesis using stopped_value_hitting_time_mem[of j _ _ X] unfolding downcrossing_simps stopped_value_def by blast
qed

lemma upcrossing_less_downcrossing:
  assumes "a < b" "downcrossing (Suc n) \<omega> \<noteq> N"
  shows "upcrossing (Suc n) \<omega> < downcrossing (Suc n) \<omega>"
proof -
  have "upcrossing (Suc n) \<omega> \<noteq> N" using assms by (metis le_antisym downcrossing_le upcrossing_le_downcrossing)
  hence "stopped_value X (downcrossing (Suc n)) \<omega> < stopped_value X (upcrossing (Suc n)) \<omega>"
    using assms stopped_value_downcrossing stopped_value_upcrossing by force
  hence "downcrossing (Suc n) \<omega> \<noteq> upcrossing (Suc n) \<omega>" unfolding stopped_value_def by force
  thus ?thesis using upcrossing_le_downcrossing by (simp add: le_neq_implies_less)
qed

lemma downcrossing_less_upcrossing:
  assumes "a < b" "upcrossing (Suc n) \<omega> \<noteq> N"
  shows "downcrossing n \<omega> < upcrossing (Suc n) \<omega>"
proof -
  have "downcrossing n \<omega> \<noteq> N" using assms by (metis le_antisym upcrossing_le downcrossing_le_upcrossing_Suc)
  hence "stopped_value X (downcrossing n) \<omega> < stopped_value X (upcrossing (Suc n)) \<omega>"
    using assms stopped_value_downcrossing stopped_value_upcrossing by force
  hence "downcrossing n \<omega> \<noteq> upcrossing (Suc n) \<omega>" unfolding stopped_value_def by force
  thus ?thesis using downcrossing_le_upcrossing_Suc by (simp add: le_neq_implies_less)
qed

lemma upcrossing_less_Suc:
  assumes "a < b" "upcrossing n \<omega> \<noteq> N"
  shows "upcrossing n \<omega> < upcrossing (Suc n) \<omega>"
  by (metis assms upcrossing_le_downcrossing downcrossing_less_upcrossing order_le_less_trans le_neq_implies_less upcrossing_le)

(* The following lemma is a more elegant version of the same lemma on mathlib. *)

lemma upcrossing_eq_bound:
  assumes "a < b" "n \<ge> N"
  shows "upcrossing n \<omega> = N"
proof -
  have *: "upcrossing N \<omega> = N"
  proof -
    {
      assume *: "upcrossing N \<omega> \<noteq> N"
      hence asm: "upcrossing n \<omega> < N" if "n \<le> N" for n using upcrossing_mono upcrossing_le that by (metis le_antisym le_neq_implies_less)
      {
        fix i j
        assume "i \<le> N" "i < j"
        hence "upcrossing i \<omega> \<noteq> upcrossing j \<omega>" by (metis Suc_leI asm assms(1) leD upcrossing_less_Suc upcrossing_mono)
      }
      moreover
      {
        fix j
        assume "j \<le> N"
        hence "upcrossing j \<omega> \<le> upcrossing N \<omega>" using upcrossing_mono by blast
        hence "upcrossing (Suc N) \<omega> \<noteq> upcrossing j \<omega>" using upcrossing_less_Suc[OF assms(1) *] by simp
      }
      ultimately have "inj_on (\<lambda>n. upcrossing n \<omega>) {..Suc N}" unfolding inj_on_def by (metis atMost_iff le_SucE linorder_less_linear)
      hence "card ((\<lambda>n. upcrossing n \<omega>) ` {..Suc N}) = Suc (Suc N)" by (simp add: inj_on_iff_eq_card[THEN iffD1])
      moreover have "(\<lambda>n. upcrossing n \<omega>) ` {..Suc N} \<subseteq> {..N}" using upcrossing_le by blast
      moreover have "card ((\<lambda>n. upcrossing n \<omega>) ` {..Suc N}) \<le> Suc N" using card_mono[OF _ calculation(2)] by simp
      ultimately have False by linarith
    }
    thus ?thesis by blast
  qed
  thus ?thesis using upcrossing_mono[OF assms(2), of \<omega>] upcrossing_le[of n \<omega>] by simp
qed

lemma downcrossing_eq_bound:
  assumes "a < b" "n \<ge> N"
  shows "downcrossing n \<omega> = N"
  using upcrossing_le_downcrossing[of n \<omega>] downcrossing_le[of n \<omega>] upcrossing_eq_bound[OF assms] by simp

lemma stopping_time_crossings: 
  assumes "adapted_process M F 0 X"
  shows "stopping_time (upcrossing n)" "stopping_time (downcrossing n)"
proof -
  have "stopping_time (upcrossing n) \<and> stopping_time (downcrossing n)"
  proof (induction n)
    case 0
    then show ?case unfolding upcrossing_simps downcrossing_simps
      using stopping_time_const stopping_time_hitting_time[OF assms] by simp
  next
    case (Suc n)
    have "stopping_time (upcrossing (Suc n))" unfolding upcrossing_simps
      using assms Suc downcrossing_le by (intro stopping_time_hitting_time') auto
    moreover have "stopping_time (downcrossing (Suc n))" unfolding downcrossing_simps
      using assms calculation upcrossing_le by (intro stopping_time_hitting_time') auto
    ultimately show ?case by blast
  qed
  thus "stopping_time (upcrossing n)" "stopping_time (downcrossing n)" by blast+
qed

lemmas stopping_time_upcrossing = stopping_time_crossings(1)
lemmas stopping_time_downcrossing = stopping_time_crossings(2)

definition upcrossings_before :: "'a \<Rightarrow> nat" where
  "upcrossings_before = (\<lambda>\<omega>. Sup {n. upcrossing n \<omega> < N})"

lemma upcrossings_before_bdd_above: 
  assumes "a < b"
  shows "bdd_above {n. upcrossing n \<omega> < N}"
proof -
  have "{n. upcrossing n \<omega> < N} \<subseteq> {..<N}" unfolding lessThan_def Collect_mono_iff
    using upcrossing_eq_bound[OF assms] linorder_not_less order_less_irrefl by metis
  thus ?thesis by (meson bdd_above_Iio bdd_above_mono)
qed

lemma upcrossings_before_less:
  assumes "a < b" "0 < N"
  shows "upcrossings_before \<omega> < N"
proof -
  have *: "{n. upcrossing n \<omega> < N} \<subseteq> {..<N}" unfolding lessThan_def Collect_mono_iff
    using upcrossing_eq_bound[OF assms(1)] linorder_not_less order_less_irrefl by metis
  have "upcrossing 0 \<omega> < N" unfolding upcrossing_simps by (rule assms)
  moreover have "Sup {..<N} < N" unfolding Sup_nat_def using assms by simp
  ultimately show ?thesis unfolding upcrossings_before_def using cSup_subset_mono[OF _ _ *] by force
qed

lemma upcrossings_before_less_implies_crossing_eq_bound:
  assumes "a < b" "upcrossings_before \<omega> < n"
  shows "upcrossing n \<omega> = N"
        "downcrossing n \<omega> = N"
proof -
  have "\<not> upcrossing n \<omega> < N" using assms upcrossings_before_bdd_above[of \<omega>] upcrossings_before_def bdd_above_nat finite_Sup_less_iff by fastforce
  thus "upcrossing n \<omega> = N" using upcrossing_le[of n \<omega>] by simp
  thus "downcrossing n \<omega> = N" using upcrossing_le_downcrossing[of n \<omega>] downcrossing_le[of n \<omega>] by simp
qed

lemma upcrossings_before_le:
  assumes "a < b"
  shows "upcrossings_before \<omega> \<le> N"
  using upcrossings_before_less assms less_le_not_le upcrossings_before_def
  by (cases N) auto

lemma upcrossings_before_mem:
  assumes "a < b" "0 < N"
  shows "upcrossings_before \<omega> \<in> {n. upcrossing n \<omega> < N} \<inter> {..<N}"
proof -
  have "upcrossing 0 \<omega> < N" using assms unfolding upcrossing_simps by simp
  hence "{n. upcrossing n \<omega> < N} \<noteq> {}" by blast
  moreover have "finite {n. upcrossing n \<omega> < N}" using upcrossings_before_bdd_above[OF assms(1)] by (simp add: bdd_above_nat)
  ultimately show ?thesis using Max_in upcrossings_before_less[OF assms(1,2)] Sup_nat_def upcrossings_before_def by auto
qed

lemma upcrossing_less_of_le_upcrossings_before:
  assumes "a < b" "0 < N" "n \<le> upcrossings_before \<omega>" 
  shows "upcrossing n \<omega> < N"
  using upcrossings_before_mem[OF assms(1,2), of \<omega>] upcrossing_mono[OF assms(3), of \<omega>] by simp

lemma upcrossings_before_sum_def:
  assumes "a < b"
  shows "upcrossings_before \<omega> = (\<Sum>k\<in>{1..N}. indicator {n. upcrossing n \<omega> < N} k)"
proof (cases N)
  case 0
  then show ?thesis unfolding upcrossings_before_def by simp
next
  case (Suc N')
  have "upcrossing 0 \<omega> < N" using assms Suc unfolding upcrossing_simps by simp
  hence "{n. upcrossing n \<omega> < N} \<noteq> {}" by blast
  hence *: "\<not> upcrossing n \<omega> < N" if "n \<in> {upcrossings_before \<omega> <..N}" for n
    using finite_Sup_less_iff[THEN iffD1, OF bdd_above_nat[THEN iffD1, OF upcrossings_before_bdd_above], of \<omega> n]
    by (metis that assms greaterThanAtMost_iff less_not_refl mem_Collect_eq upcrossings_before_def)
  have **: "upcrossing n \<omega> < N" if "n \<in> {1..upcrossings_before \<omega>}" for n
    using assms that Suc by (intro upcrossing_less_of_le_upcrossings_before) auto
  have "upcrossings_before \<omega> < N" using upcrossings_before_less Suc assms by simp
  hence "{1..N} - {1..upcrossings_before \<omega>} = {upcrossings_before \<omega><..N}"
        "{1..N} \<inter> {1..upcrossings_before \<omega>} = {1..upcrossings_before \<omega>}" by force+
  hence "(\<Sum>k\<in>{1..N}. indicator {n. upcrossing n \<omega> < N} k) = 
        (\<Sum>k\<in>{1..upcrossings_before \<omega>}. indicator {n. upcrossing n \<omega> < N} k) + (\<Sum>k\<in>{upcrossings_before \<omega> <..N}. indicator {n. upcrossing n \<omega> < N} k)"
    using sum.Int_Diff[OF finite_atLeastAtMost, of _ 1 N "{1..upcrossings_before \<omega>}"] by metis
  also have "... = upcrossings_before \<omega>" using * ** by simp
  finally show ?thesis by argo
qed

lemma upcrossings_before_measurable:
  assumes "adapted_process M F 0 X" "a < b"
  shows "upcrossings_before \<in> borel_measurable M"
  unfolding upcrossings_before_sum_def[OF assms(2)]
  using stopping_time_measurable[OF stopping_time_crossings(1), OF assms(1)] by simp

lemma real_embedding_borel_measurable: "real \<in> borel_measurable borel" by (auto intro: borel_measurable_continuous_onI)

lemma upcrossings_before_measurable':
  assumes "adapted_process M F 0 X" "a < b"
  shows "(\<lambda>\<omega>. real (upcrossings_before \<omega>)) \<in> borel_measurable M"
  using real_embedding_borel_measurable upcrossings_before_measurable[OF assms] by simp 

end

lemma crossing_eq_crossing:
  assumes "N \<le> N'"
      and "downcrossing X a b N n \<omega> < N"
    shows "upcrossing X a b N n \<omega> = upcrossing X a b N' n \<omega>"
          "downcrossing X a b N n \<omega> = downcrossing X a b N' n \<omega>"
proof -
  have "upcrossing X a b N n \<omega> = upcrossing X a b N' n \<omega> \<and> downcrossing X a b N n \<omega> = downcrossing X a b N' n \<omega>" using assms(2)
  proof (induction n)
    case 0
    show ?case by (metis (no_types, lifting) upcrossing_simps(1) assms atLeast_0 bot_nat_0.extremum hitting_time_def hitting_time_eq_hitting_time inf_top.right_neutral leD downcrossing_mono downcrossing_simps(1) max_nat.left_neutral)
  next
    case (Suc n)
    hence upper_less: "upcrossing X a b N (Suc n) \<omega> < N" using upcrossing_le_downcrossing Suc order.strict_trans1 by blast
    hence lower_less: "downcrossing X a b N n \<omega> < N" using downcrossing_le_upcrossing_Suc order.strict_trans1 by blast

    obtain j where "j \<in> {downcrossing X a b N n \<omega>..<N}" "X j \<omega> \<in> {b..}"
      using hitting_time_less_iff[THEN iffD1, OF order_refl] upper_less by (force simp add: upcrossing_simps)
    hence upper_eq: "upcrossing X a b N (Suc n) \<omega> = upcrossing X a b N' (Suc n) \<omega>"
      using Suc(1)[OF lower_less] assms(1) 
      by (auto simp add: upcrossing_simps intro!: hitting_time_eq_hitting_time)
    obtain j where j: "j \<in> {upcrossing X a b N (Suc n) \<omega>..<N}" "X j \<omega> \<in> {..a}" using Suc(2) hitting_time_less_iff[THEN iffD1, OF order_refl] by (force simp add: downcrossing_simps)
    thus ?case unfolding downcrossing_simps upper_eq by (force intro: hitting_time_eq_hitting_time assms)
  qed
  thus "upcrossing X a b N n \<omega> = upcrossing X a b N' n \<omega>" "downcrossing X a b N n \<omega> = downcrossing X a b N' n \<omega>" by auto
qed

lemma crossing_eq_crossing':
  assumes "N \<le> N'"
      and "upcrossing X a b N (Suc n) \<omega> < N"
    shows "upcrossing X a b N (Suc n) \<omega> = upcrossing X a b N' (Suc n) \<omega>"
          "downcrossing X a b N n \<omega> = downcrossing X a b N' n \<omega>"
proof -
  show lower_eq: "downcrossing X a b N n \<omega> = downcrossing X a b N' n \<omega>"
    using downcrossing_le_upcrossing_Suc[THEN order.strict_trans1] crossing_eq_crossing assms by fast
  have "\<exists>j\<in>{downcrossing X a b N n \<omega>..<N}. X j \<omega> \<in> {b..}" using assms(2) by (intro hitting_time_less_iff[OF order_refl, THEN iffD1]) (simp add: upcrossing_simps lower_eq)
  then obtain j where "j\<in>{downcrossing X a b N n \<omega>..N}" "X j \<omega> \<in> {b..}" by fastforce
  thus "upcrossing X a b N (Suc n) \<omega> = upcrossing X a b N' (Suc n) \<omega>"
    unfolding upcrossing_simps stopped_value_def using hitting_time_eq_hitting_time[OF assms(1)] lower_eq by metis
qed

lemma upcrossing_eq_upcrossing:
  assumes "N \<le> N'"
      and "upcrossing X a b N n \<omega> < N"
    shows "upcrossing X a b N n \<omega> = upcrossing X a b N' n \<omega>"
  using crossing_eq_crossing'[OF assms(1)] assms(2) upcrossing_simps
  by (cases n) (presburger, fast)

lemma upcrossings_before_zero: "upcrossings_before X a b 0 \<omega> = 0" 
  unfolding upcrossings_before_def by simp

lemma upcrossings_before_less_exists_upcrossing:
  assumes "a < b"
      and upcrossing: "N \<le> L" "X L \<omega> < a" "L \<le> U" "b < X U \<omega>"
    shows "upcrossings_before X a b N \<omega> < upcrossings_before X a b (Suc U) \<omega>"
proof -
  have "upcrossing X a b (Suc U) (upcrossings_before X a b N \<omega>) \<omega> \<le> L"
    using assms upcrossing_le[THEN order_trans, OF upcrossing(1)]
    by (cases "0 < N", subst upcrossing_eq_upcrossing[of N "Suc U", symmetric, OF _ upcrossing_less_of_le_upcrossings_before])
       (auto simp add: upcrossings_before_zero upcrossing_simps) 
  hence "downcrossing X a b (Suc U) (upcrossings_before X a b N \<omega>) \<omega> \<le> U" 
    unfolding downcrossing_simps using upcrossing by (force intro: hitting_time_le_iff[THEN iffD2])
  hence "upcrossing X a b (Suc U) (Suc (upcrossings_before X a b N \<omega>)) \<omega> < Suc U" 
    unfolding upcrossing_simps using upcrossing by (force intro: hitting_time_less_iff[THEN iffD2])
  thus ?thesis using cSup_upper[OF _ upcrossings_before_bdd_above[OF assms(1)]] upcrossings_before_def by fastforce
qed

lemma crossings_translate:
  "upcrossing X a b N = upcrossing (\<lambda>n \<omega>. (X n \<omega> + c)) (a + c) (b + c) N"
  "downcrossing X a b N = downcrossing (\<lambda>n \<omega>. (X n \<omega> + c)) (a + c) (b + c) N"
proof -
  have upper: "upcrossing X a b N n = upcrossing (\<lambda>n \<omega>. (X n \<omega> + c)) (a + c) (b + c) N n" for n
  proof (induction n)
    case 0
    then show ?case by (simp only: upcrossing.simps)
  next
    case (Suc n)
    have "((+) c ` {..a}) = {..a + c}" by simp
    moreover have "((+) c ` {b..}) = {b + c..}" by simp
    ultimately show ?case unfolding upcrossing.simps using hitting_time_translate[of X "{b..}" c] hitting_time_translate[of X "{..a}" c] Suc by presburger 
  qed
  thus "upcrossing X a b N = upcrossing (\<lambda>n \<omega>. (X n \<omega> + c)) (a + c) (b + c) N" by blast
  have "((+) c ` {..a}) = {..a + c}" by simp
  thus "downcrossing X a b N = downcrossing (\<lambda>n \<omega>. (X n \<omega> + c)) (a + c) (b + c) N" using upper downcrossing_simps hitting_time_translate[of X "{..a}" c] by presburger
qed

lemma upcrossings_before_translate: 
  "upcrossings_before X a b N = upcrossings_before (\<lambda>n \<omega>. (X n \<omega> + c)) (a + c) (b + c) N"
  using upcrossings_before_def crossings_translate by simp

lemma crossings_pos_eq:
  assumes "a < b"
  shows "upcrossing X a b N = upcrossing (\<lambda>n \<omega>. max 0 (X n \<omega> - a)) 0 (b - a) N"
        "downcrossing X a b N = downcrossing (\<lambda>n \<omega>. max 0 (X n \<omega> - a)) 0 (b - a) N"
proof -
  have *: "max 0 (x - a) \<in> {..0} \<longleftrightarrow> x - a \<in> {..0}" "max 0 (x - a) \<in> {b - a..} \<longleftrightarrow> x - a \<in> {b - a..}" for x using assms by auto
  have "upcrossing X a b N = upcrossing (\<lambda>n \<omega>. X n \<omega> - a) 0 (b - a) N" using crossings_translate[of X a b N "- a"] by simp
  thus upper: "upcrossing X a b N = upcrossing (\<lambda>n \<omega>. max 0 (X n \<omega> - a)) 0 (b - a) N" unfolding upcrossing_def hitting_time_def' using * by presburger

  thus "downcrossing X a b N = downcrossing (\<lambda>n \<omega>. max 0 (X n \<omega> - a)) 0 (b - a) N" 
    unfolding downcrossing_simps hitting_time_def' using upper * by simp
qed

lemma upcrossings_before_mono:
  assumes "a < b" "N \<le> N'"
  shows "upcrossings_before X a b N \<omega> \<le> upcrossings_before X a b N' \<omega>"
proof (cases N)
  case 0
  then show ?thesis unfolding upcrossings_before_def by simp
next
  case (Suc N')
  hence "upcrossing X a b N 0 \<omega> < N" unfolding upcrossing_simps by simp
  thus ?thesis unfolding upcrossings_before_def using upcrossings_before_bdd_above upcrossing_eq_upcrossing assms by (intro cSup_subset_mono) auto
qed

lemma upcrossings_before_pos_eq:
  assumes "a < b"
  shows "upcrossings_before X a b N = upcrossings_before (\<lambda>n \<omega>. max 0 (X n \<omega> - a)) 0 (b - a) N"
  using upcrossings_before_def crossings_pos_eq[OF assms] by simp

text \<open>We define \<open>upcrossings\<close> to be the total number of upcrossings a stochastic process completes as \<open>N \<longlonglongrightarrow> \<infinity>\<close>.\<close>

definition upcrossings :: "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> ennreal" where
  "upcrossings X a b = (\<lambda>\<omega>. (SUP N. ennreal (upcrossings_before X a b N \<omega>)))"

lemma upcrossings_measurable: 
  assumes "adapted_process M F 0 X" "a < b"
  shows "upcrossings X a b \<in> borel_measurable M"
  unfolding upcrossings_def
  using upcrossings_before_measurable'[OF assms] by (auto intro!: borel_measurable_SUP)

end

lemma limsup_lower_bound:
  fixes u:: "nat \<Rightarrow> ereal"
  assumes "limsup u > l"
  shows "\<exists>N>k. u N > l"
proof -
  have "limsup u = - liminf (\<lambda>n. - u n)" using liminf_ereal_cminus[of 0 u] by simp
  hence "liminf (\<lambda>n. - u n) < - l" using assms ereal_less_uminus_reorder by presburger
  hence "\<exists>N>k. - u N < - l" using liminf_upper_bound by blast
  thus ?thesis using ereal_less_uminus_reorder by simp
qed

lemma (in nat_finite_filtered_measure) integrable_upcrossings_before:
  assumes "adapted_process M F 0 X" "a < b"
  shows "integrable M (\<lambda>\<omega>. real (upcrossings_before X a b N \<omega>))"
proof -
  have "(\<integral>\<^sup>+ x. ennreal (norm (real (upcrossings_before X a b N x))) \<partial>M) \<le> (\<integral>\<^sup>+ x. ennreal N \<partial>M)" using upcrossings_before_le[OF assms(2)] by (intro nn_integral_mono) simp
  also have "... = ennreal N * emeasure M (space M)" by simp
  also have "... < \<infinity>" by (metis emeasure_real ennreal_less_top ennreal_mult_less_top infinity_ennreal_def)
  finally show ?thesis by (intro integrableI_bounded upcrossings_before_measurable' assms)
qed

section \<open>Doob's Upcrossing Inequality\<close>

context nat_finite_filtered_measure
begin

theorem upcrossing_inequality:
  fixes a b :: real and N :: nat
  assumes "submartingale M F 0 X"
  shows "(b - a) * (\<integral>\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M) \<le> (\<integral>\<omega>. max 0 (X N \<omega> - a) \<partial>M)"
proof -
  interpret submartingale_linorder M F 0 X unfolding submartingale_linorder_def by (intro assms)
  show ?thesis 
  proof (cases "a < b")
    case True
    have *: "(b - a) * (\<integral>\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M) \<le> (\<integral>\<omega>. X N \<omega> \<partial>M)"
      if asm: "submartingale M F 0 X" "a < b" "\<And>\<omega>. X 0 \<omega> \<ge> 0" "\<And>\<omega>. X N \<omega> \<ge> a"
      for a b X
    proof -
      interpret subm: submartingale M F 0 X by (intro asm)      
      define C :: "nat \<Rightarrow> 'a \<Rightarrow> real" where "C = (\<lambda>n \<omega>. \<Sum>k < N. indicator {downcrossing X a b N k \<omega>..<upcrossing X a b N (Suc k) \<omega>} n)"
      have C_values: "C n \<omega> \<in> {0, 1}" for n \<omega>
      proof (cases "\<exists>j < N. n \<in> {downcrossing X a b N j \<omega>..<upcrossing X a b N (Suc j) \<omega>}")
        case True
        then obtain j where j: "j \<in> {..<N}" "n \<in> {downcrossing X a b N j \<omega>..<upcrossing X a b N (Suc j) \<omega>}" by blast
        {
          fix k l :: nat assume k_less_l: "k < l"
          hence Suc_k_le_l: "Suc k \<le> l" by simp
          have "{downcrossing X a b N k \<omega>..<upcrossing X a b N (Suc k) \<omega>} \<inter> {downcrossing X a b N l \<omega>..<upcrossing X a b N (Suc l) \<omega>} = 
                {downcrossing X a b N l \<omega>..<upcrossing X a b N (Suc k) \<omega>}" 
            using k_less_l upcrossing_mono downcrossing_mono by simp
          moreover have "upcrossing X a b N (Suc k) \<omega> \<le> downcrossing X a b N l \<omega>"
            using upcrossing_le_downcrossing downcrossing_mono[OF Suc_k_le_l] order_trans by blast
          ultimately have "{downcrossing X a b N k \<omega>..<upcrossing X a b N (Suc k) \<omega>} \<inter> {downcrossing X a b N l \<omega>..<upcrossing X a b N (Suc l) \<omega>} = {}" by simp
        }
        hence "disjoint_family_on (\<lambda>k. {downcrossing X a b N k \<omega>..<upcrossing X a b N (Suc k) \<omega>}) {..<N}" 
          unfolding disjoint_family_on_def
          by (metis Int_commute linorder_less_linear)
        hence "C n \<omega> = 1" unfolding C_def using sum_indicator_disjoint_family[where ?f="\<lambda>_. 1"] j by fastforce
        thus ?thesis by blast
      next
        case False
        hence "C n \<omega> = 0" unfolding C_def by simp
        thus ?thesis by simp
      qed
      hence C_interval: "C n \<omega> \<in> {0..1}" for n \<omega> by (metis atLeastAtMost_iff empty_iff insert_iff order.refl zero_less_one_class.zero_le_one)

      define C' where "C' = (\<lambda>n \<omega>. \<Sum>k < n. C k \<omega> *\<^sub>R (X (Suc k) \<omega> - X k \<omega>))"
      define one_minus_C' where "one_minus_C' = (\<lambda>n \<omega>. \<Sum>k < n. (1 - C k \<omega>) *\<^sub>R (X (Suc k) \<omega> - X k \<omega>))"

      text \<open>We use the fact that the crossing times are stopping times to show that C is predictable.\<close>
      have adapted_C: "adapted_process M F 0 C"
      proof
        fix i
        have "(\<lambda>\<omega>. indicat_real {downcrossing X a b N k \<omega>..<upcrossing X a b N (Suc k) \<omega>} i) \<in> borel_measurable (F i)" for k
          unfolding indicator_def
          using stopping_time_upcrossing[OF subm.adapted_process_axioms, THEN stopping_time_measurable_gr]
                stopping_time_downcrossing[OF subm.adapted_process_axioms, THEN stopping_time_measurable_le] 
          by force
        thus "C i \<in> borel_measurable (F i)" unfolding C_def by simp
      qed
      hence "adapted_process M F 0 (\<lambda>n \<omega>. 1 - C n \<omega>)" by (intro adapted_process.diff_adapted adapted_process_const)
      hence submartingale_one_minus_C': "submartingale M F 0 one_minus_C'" unfolding one_minus_C'_def using C_interval
        by (intro submartingale_partial_sum_scaleR[of _ _ 1] submartingale_linorder.intro asm) auto

      have "C n \<in> borel_measurable M" for n
        using adapted_C adapted_process.adapted measurable_from_subalg subalg by blast

      have integrable_C': "integrable M (C' n)" for n unfolding C'_def using C_interval
        by (intro submartingale_partial_sum_scaleR[THEN submartingale.integrable] submartingale_linorder.intro adapted_C asm) auto

      have "integral\<^sup>L M (C' n) \<le> integral\<^sup>L M (X n)" for n
      proof -                       
        interpret subm': submartingale_linorder M F 0 one_minus_C' unfolding submartingale_linorder_def by (rule submartingale_one_minus_C')
        have "0 \<le> integral\<^sup>L M (one_minus_C' n)"
          using subm'.set_integral_le[OF sets.top, where i=0 and j=n] space_F subm'.integrable by (fastforce simp add: set_integral_space one_minus_C'_def)
        moreover have "one_minus_C' n \<omega> = (\<Sum>k < n. X (Suc k) \<omega> - X k \<omega>) - C' n \<omega>" for \<omega>
          unfolding one_minus_C'_def C'_def by (simp only: scaleR_diff_left sum_subtractf scale_one)
        ultimately have "0 \<le> (LINT \<omega>|M. (\<Sum>k < n. X (Suc k) \<omega> - X k \<omega>)) - integral\<^sup>L M (C' n)"
          using subm.integrable integrable_C'
          by (subst Bochner_Integration.integral_diff[symmetric]) (auto simp add: one_minus_C'_def)
        moreover have "(LINT \<omega>|M. (\<Sum>k<n. X (Suc k) \<omega> - X k \<omega>)) \<le> (LINT \<omega>|M. X n \<omega>)" using asm sum_lessThan_telescope[of "\<lambda>i. X i _" n] subm.integrable
          by (intro integral_mono) auto
        ultimately show ?thesis by linarith
      qed
      moreover have "(b - a) * (\<integral>\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M) \<le> integral\<^sup>L M (C' N)"
      proof (cases N)
        case 0
        then show ?thesis using C'_def upcrossings_before_zero by simp
      next
        case (Suc N')
        {
          fix \<omega>
          have dc_not_N: "downcrossing X a b N k \<omega> \<noteq> N" if "k < upcrossings_before X a b N \<omega>" for k
            by (metis Suc Suc_leI asm(2) downcrossing_le_upcrossing_Suc leD that upcrossing_less_of_le_upcrossings_before zero_less_Suc)
          have uc_not_N:"upcrossing X a b N (Suc k) \<omega> \<noteq> N" if "k < upcrossings_before X a b N \<omega>" for k 
            by (metis Suc Suc_leI asm(2) order_less_irrefl that upcrossing_less_of_le_upcrossings_before zero_less_Suc)

          have subset_lessThan_N: "{downcrossing X a b N i \<omega>..<upcrossing X a b N (Suc i) \<omega>} \<subseteq> {..<N}" if "i < N" for i using that
            by (simp add: lessThan_atLeast0 upcrossing_le)

          have "C' N \<omega> = (\<Sum>k<N. \<Sum>i<N. indicator {downcrossing X a b N i \<omega>..<upcrossing X a b N (Suc i) \<omega>} k * (X (Suc k) \<omega> - X k \<omega>))"
            unfolding C'_def C_def by (simp add: sum_distrib_right)
          also have "... = (\<Sum>i<N. \<Sum>k<N. indicator {downcrossing X a b N i \<omega>..<upcrossing X a b N (Suc i) \<omega>} k * (X (Suc k) \<omega> - X k \<omega>))"
            using sum.swap by fast
          also have "... = (\<Sum>i<N. \<Sum>k\<in>{..<N} \<inter> {downcrossing X a b N i \<omega>..<upcrossing X a b N (Suc i) \<omega>}. X (Suc k) \<omega> - X k \<omega>)"
            by (subst Indicator_Function.sum_indicator_mult) simp+
          also have "... = (\<Sum>i<N. \<Sum>k\<in>{downcrossing X a b N i \<omega>..<upcrossing X a b N (Suc i) \<omega>}. X (Suc k) \<omega> - X k \<omega>)"
            using subset_lessThan_N[THEN Int_absorb1] by simp
          also have "... = (\<Sum>i<N. X (upcrossing X a b N (Suc i) \<omega>) \<omega> - X (downcrossing X a b N i \<omega>) \<omega>)" 
            by (subst sum_Suc_diff'[OF downcrossing_le_upcrossing_Suc]) blast
          finally have *: "C' N \<omega> = (\<Sum>i<N. X (upcrossing X a b N (Suc i) \<omega>) \<omega> - X (downcrossing X a b N i \<omega>) \<omega>)" .

          have summand_zero_if: "X (upcrossing X a b N (Suc k) \<omega>) \<omega> - X (downcrossing X a b N k \<omega>) \<omega> = 0" if "k > upcrossings_before X a b N \<omega>" for k
            using that upcrossings_before_less_implies_crossing_eq_bound[OF asm(2)] by simp

          have summand_nonneg_if: "X (upcrossing X a b N (Suc (upcrossings_before X a b N \<omega>)) \<omega>) \<omega> - X (downcrossing X a b N (upcrossings_before X a b N \<omega>) \<omega>) \<omega> \<ge> 0"
            using upcrossings_before_less_implies_crossing_eq_bound(1)[OF asm(2) lessI]
                  stopped_value_downcrossing[of X a b N _ \<omega>, THEN order_trans, OF _ asm(4)[of \<omega>]]
            by (cases "downcrossing X a b N (upcrossings_before X a b N \<omega>) \<omega> \<noteq> N") (simp add: stopped_value_def)+

          have interval: "{upcrossings_before X a b N \<omega>..<N} - {upcrossings_before X a b N \<omega>} = {upcrossings_before X a b N \<omega><..<N}"
            using Diff_insert atLeastSucLessThan_greaterThanLessThan lessThan_Suc lessThan_minus_lessThan by metis

          have "(b - a) * real (upcrossings_before X a b N \<omega>) = (\<Sum>_<upcrossings_before X a b N \<omega>. b - a)" by simp
          also have "... \<le> (\<Sum>k<upcrossings_before X a b N \<omega>. stopped_value X (upcrossing X a b N (Suc k)) \<omega> - stopped_value X (downcrossing X a b N k) \<omega>)"
            using stopped_value_downcrossing[OF dc_not_N] stopped_value_upcrossing[OF uc_not_N] by (force intro!: sum_mono)
          also have "... = (\<Sum>k<upcrossings_before X a b N \<omega>. X (upcrossing X a b N (Suc k) \<omega>) \<omega> - X (downcrossing X a b N k \<omega>) \<omega>)" unfolding stopped_value_def by blast
          also have "... \<le> (\<Sum>k<upcrossings_before X a b N \<omega>. X (upcrossing X a b N (Suc k) \<omega>) \<omega> - X (downcrossing X a b N k \<omega>) \<omega>)
                          + (\<Sum>k\<in>{upcrossings_before X a b N \<omega>}. X (upcrossing X a b N (Suc k) \<omega>) \<omega> - X (downcrossing X a b N k \<omega>) \<omega>)
                          + (\<Sum>k\<in>{upcrossings_before X a b N \<omega><..<N}. X (upcrossing X a b N (Suc k) \<omega>) \<omega> - X (downcrossing X a b N k \<omega>) \<omega>)" 
            using summand_zero_if summand_nonneg_if by auto
          also have "... = (\<Sum>k<N. X (upcrossing X a b N (Suc k) \<omega>) \<omega> - X (downcrossing X a b N k \<omega>) \<omega>)"
            using upcrossings_before_le[OF asm(2)]
            by (subst sum.subset_diff[where A="{..<N}" and B="{..<upcrossings_before X a b N \<omega>}"], simp, simp,
                subst sum.subset_diff[where A="{..<N} - {..<upcrossings_before X a b N \<omega>}" and B="{upcrossings_before X a b N \<omega>}"])
               (simp add: Suc asm(2) upcrossings_before_less, simp, simp add: interval)
          finally have "(b - a) * real (upcrossings_before X a b N \<omega>) \<le> C' N \<omega>" using * by presburger
        }
        thus ?thesis using integrable_upcrossings_before subm.adapted_process_axioms asm integrable_C'
          by (subst integral_mult_right_zero[symmetric], intro integral_mono) auto
      qed
      ultimately show ?thesis using order_trans by blast
    qed

    have "(b - a) * (\<integral>\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M) = (b - a) * (\<integral>\<omega>. real (upcrossings_before (\<lambda>n \<omega>. max 0 (X n \<omega> - a)) 0 (b - a) N \<omega>) \<partial>M)"
      using upcrossings_before_pos_eq[OF True] by simp                                                                             
    also have "... \<le> (\<integral>\<omega>. max 0 (X N \<omega> - a) \<partial>M)" 
      using *[OF submartingale_linorder.max_0[OF submartingale_linorder.intro, OF submartingale.diff, OF assms supermartingale_const], of 0 "b - a" a] True by simp
    finally show ?thesis .
  next
    case False
    have "0 \<le> (\<integral>\<omega>. max 0 (X N \<omega> - a) \<partial>M)" by simp
    moreover have "0 \<le> (\<integral>\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M)" by simp
    moreover have "b - a \<le> 0" using False by simp
    ultimately show ?thesis using mult_nonpos_nonneg order_trans by meson
  qed
qed

theorem upcrossing_inequality_Sup:
  fixes a b :: real
  assumes "submartingale M F 0 X"
  shows "(b - a) * (\<integral>\<^sup>+\<omega>. upcrossings X a b \<omega> \<partial>M) \<le> (SUP N. (\<integral>\<^sup>+\<omega>. max 0 (X N \<omega> - a) \<partial>M))"
proof -
  interpret submartingale M F 0 X by (intro assms)
  show ?thesis
  proof (cases "a < b")
    case True
    have "(\<integral>\<^sup>+\<omega>. upcrossings X a b \<omega> \<partial>M) = (SUP N. (\<integral>\<^sup>+\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M))"
      unfolding upcrossings_def
      using upcrossings_before_mono True upcrossings_before_measurable'[OF adapted_process_axioms]
      by (auto intro: nn_integral_monotone_convergence_SUP simp add: mono_def le_funI)
    hence "(b - a) * (\<integral>\<^sup>+\<omega>. upcrossings X a b \<omega> \<partial>M) = (SUP N. (b - a) * (\<integral>\<^sup>+\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M))"
      by (simp add: SUP_mult_left_ennreal)
    moreover
    {
      fix N
      have "(\<integral>\<^sup>+\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M) = (\<integral>\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M)" 
        by (force intro!: nn_integral_eq_integral integrable_upcrossings_before True adapted_process_axioms)
      moreover have "(\<integral>\<^sup>+\<omega>. max 0 (X N \<omega> - a) \<partial>M) = (\<integral>\<omega>. max 0 (X N \<omega> - a) \<partial>M)"
        using Bochner_Integration.integrable_diff[OF integrable integrable_const]
        by (force intro!: nn_integral_eq_integral)
      ultimately have "(b - a) * (\<integral>\<^sup>+\<omega>. real (upcrossings_before X a b N \<omega>) \<partial>M) \<le> (\<integral>\<^sup>+\<omega>. max 0 (X N \<omega> - a) \<partial>M)"
        using upcrossing_inequality[OF assms, of b a N] True ennreal_mult'[symmetric] by simp
    }
    ultimately show ?thesis by (force intro!: Sup_mono)
  qed (simp add: ennreal_neg)
qed

lemma ereal_abs_max_min: "\<bar>c\<bar> = max 0 c - min 0 c" for c :: ereal 
  by (cases "c \<ge> 0") auto

section \<open>Doob's First Martingale Convergence Theorem\<close>

theorem submartingale_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "submartingale M F 0 X" 
      and "\<And>n. (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) \<le> C"
  obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" "integrable M X\<^sub>l\<^sub>i\<^sub>m" "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  interpret submartingale_linorder M F 0 X unfolding submartingale_linorder_def by (rule assms)
  have finite_upcrossings: "AE \<omega> in M. upcrossings X a b \<omega> \<noteq> \<infinity>" if "a < b" for a b
  proof -
    have C_nonneg: "C \<ge> 0" using assms(2) by (meson Bochner_Integration.integral_nonneg linorder_not_less max.cobounded1 order_less_le_trans)
    {
      fix n
      have "(\<integral>\<^sup>+\<omega>. max 0 (X n \<omega> - a) \<partial>M) \<le> (\<integral>\<^sup>+\<omega>. max 0 (X n \<omega>) + \<bar>a\<bar> \<partial>M)" by (fastforce intro: nn_integral_mono ennreal_leI)
      also have "... = (\<integral>\<^sup>+\<omega>. max 0 (X n \<omega>) \<partial>M) + \<bar>a\<bar> * emeasure M (space M)" by (simp add: nn_integral_add)
      also have "... = (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) + \<bar>a\<bar> * emeasure M (space M)" using integrable by (simp add: nn_integral_eq_integral)
      also have "... \<le> C + \<bar>a\<bar> * emeasure M (space M)" using assms(2) ennreal_leI by simp
      finally have "(\<integral>\<^sup>+\<omega>. max 0 (X n \<omega> - a) \<partial>M) \<le> C + \<bar>a\<bar> * enn2real (emeasure M (space M))" using finite_emeasure_space C_nonneg by (simp add: ennreal_enn2real_if ennreal_mult)
    }
    hence "(SUP N. \<integral>\<^sup>+ x. ennreal (max 0 (X N x - a)) \<partial>M) / (b - a) \<le> ennreal (C + \<bar>a\<bar> * enn2real (emeasure M (space M))) / (b - a)" by (fast intro: divide_right_mono_ennreal Sup_least)
    moreover have "ennreal (C + \<bar>a\<bar> * enn2real (emeasure M (space M))) / (b - a) < \<infinity>" using that C_nonneg by (subst divide_ennreal) auto
    moreover have "integral\<^sup>N M (upcrossings X a b) \<le> (SUP N. \<integral>\<^sup>+ x. ennreal (max 0 (X N x - a)) \<partial>M) / (b - a)"
      using upcrossing_inequality_Sup[OF assms(1), of b a, THEN divide_right_mono_ennreal, of "b - a"]
            ennreal_mult_divide_eq mult.commute[of "ennreal (b - a)"] that by simp
    ultimately show ?thesis using upcrossings_measurable adapted_process_axioms that by (intro nn_integral_noteq_infinite) auto
  qed
  define S where "S = ((\<lambda>(a :: real, b). {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))}) ` {(a, b) \<in> \<rat> \<times> \<rat>. a < b})"

  have "(0, 1) \<in> {(a :: real, b). (a, b) \<in> \<rat> \<times> \<rat> \<and> a < b}" unfolding Rats_def by simp
  moreover have "countable {(a, b). (a, b) \<in> \<rat> \<times> \<rat> \<and> a < b}" by (blast intro: countable_subset[OF _ countable_SIGMA[OF countable_rat countable_rat]])
  ultimately have from_nat_into_S: "range (from_nat_into S) = S" "from_nat_into S n \<in> S" for n 
    unfolding S_def
    by (auto intro!: range_from_nat_into from_nat_into simp only: Rats_def)
  {
    fix a b :: real
    assume a_less_b: "a < b"
    then obtain N where N: "x \<in> space M - N \<Longrightarrow> upcrossings X a b x \<noteq> \<infinity>" "N \<in> null_sets M" for x using AE_E3[OF finite_upcrossings] by blast
    {
      fix \<omega>
      assume liminf_limsup: "liminf (\<lambda>n. X n \<omega>) < a" "b < limsup (\<lambda>n. X n \<omega>)"
      have "upcrossings X a b \<omega> = \<infinity>"
      proof -
        {
          fix n
          have "\<exists>m. upcrossings_before X a b m \<omega> \<ge> n"
          proof (induction n)
            case 0
            have "Sup {n. upcrossing X a b 0 n \<omega> < 0} = 0" by simp
            then show ?case unfolding upcrossings_before_def by blast
          next
            case (Suc n)
            then obtain m where m: "n \<le> upcrossings_before X a b m \<omega>" by blast
            obtain l where l: "l \<ge> m" "X l \<omega> < a" using liminf_upper_bound[OF liminf_limsup(1), of m] nless_le by auto
            obtain u where u: "u \<ge> l" "X u \<omega> > b" using limsup_lower_bound[OF liminf_limsup(2), of l] nless_le by auto
            show ?case using upcrossings_before_less_exists_upcrossing[OF a_less_b, where ?X=X, OF l u] m by (metis Suc_leI le_neq_implies_less)
          qed
        }
        thus ?thesis unfolding upcrossings_def by (simp add: ennreal_SUP_eq_top)
      qed
    }
    hence "{\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))} \<subseteq> N" using N by blast
    moreover have "{\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))} \<inter> N \<in> null_sets M" by (force intro: null_set_Int1[OF N(2)])
    ultimately have "emeasure M {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) < a \<and> b < limsup (\<lambda>n. ereal (X n \<omega>))} = 0" by (simp add: Int_absorb1 Int_commute null_setsD1)  
  }
  hence "emeasure M (from_nat_into S n) = 0" for n using from_nat_into_S(2)[of n] unfolding S_def by force
  moreover have "S \<subseteq> M" unfolding S_def by force
  ultimately have "emeasure M (\<Union> (range (from_nat_into S))) = 0" using from_nat_into_S by (intro emeasure_UN_eq_0) auto
  moreover have "(\<Union> S) = {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) \<noteq> limsup (\<lambda>n. ereal (X n \<omega>))}" (is "?L = ?R")
  proof -
    {
      fix \<omega>
      assume asm: "\<omega> \<in> ?L"
      then obtain a b :: real where "a < b" "liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a \<and> ereal b < limsup (\<lambda>n. ereal (X n \<omega>))" unfolding S_def by blast
      hence "liminf (\<lambda>n. ereal (X n \<omega>)) \<noteq> limsup (\<lambda>n. ereal (X n \<omega>))" using ereal_less_le order.asym by fastforce
      hence "\<omega> \<in> ?R" using asm unfolding S_def by blast
    }
    moreover
    {
      fix \<omega>
      assume asm: "\<omega> \<in> ?R"
      hence "liminf (\<lambda>n. ereal (X n \<omega>)) < limsup (\<lambda>n. ereal (X n \<omega>))" using Liminf_le_Limsup[of sequentially] less_eq_ereal_def by auto
      then obtain a' where a': "liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a'" "ereal a' < limsup (\<lambda>n. ereal (X n \<omega>))" using ereal_dense2 by blast
      then obtain b' where b': "ereal a' < ereal b'" "ereal b' < limsup (\<lambda>n. ereal (X n \<omega>))" using ereal_dense2 by blast
      hence "a' < b'" by simp
      then obtain a where a: "a \<in> \<rat>" "a' < a" "a < b'" using Rats_dense_in_real by blast
      then obtain b where b: "b \<in> \<rat>" "a < b" "b < b'" using Rats_dense_in_real by blast
      have "liminf (\<lambda>n. ereal (X n \<omega>)) < ereal a" using a a' le_ereal_less order_less_imp_le by meson
      moreover have "ereal b < limsup (\<lambda>n. ereal (X n \<omega>))" using b b' order_less_imp_le ereal_less_le by meson
      ultimately have "\<omega> \<in> ?L" unfolding S_def using a b asm by blast
    }
    ultimately show ?thesis by blast
  qed
  ultimately have "emeasure M {\<omega> \<in> space M. liminf (\<lambda>n. ereal (X n \<omega>)) \<noteq> limsup (\<lambda>n. ereal (X n \<omega>))} = 0" using from_nat_into_S by argo
  hence liminf_limsup_AE: "AE \<omega> in M. liminf (\<lambda>n. X n \<omega>) = limsup (\<lambda>n. X n \<omega>)" by (intro AE_iff_measurable[THEN iffD2, OF _ refl]) auto
  hence convergent_AE: "AE \<omega> in M. convergent (\<lambda>n. ereal (X n \<omega>))" using convergent_ereal by fastforce
  have bounded_pos_part: "ennreal (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) \<le> ennreal C" for n using assms(2) ennreal_leI by blast

  (* integral of positive part is < \<infinity> *)
  {
    fix \<omega>
    assume asm: "convergent (\<lambda>n. ereal (X n \<omega>))"
    hence "(\<lambda>n. max 0 (ereal (X n \<omega>))) \<longlonglongrightarrow> max 0 (lim (\<lambda>n. ereal (X n \<omega>)))" 
      using convergent_LIMSEQ_iff isCont_tendsto_compose continuous_max continuous_const continuous_ident continuous_at_e2ennreal
      by fast
    hence "(\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) \<longlonglongrightarrow> e2ennreal (max 0 (lim (\<lambda>n. ereal (X n \<omega>))))" 
      using isCont_tendsto_compose continuous_at_e2ennreal by blast
    moreover have "lim (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) = e2ennreal (max 0 (lim (\<lambda>n. ereal (X n \<omega>))))" using limI calculation by blast
    ultimately have "e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) = liminf (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>))))" using convergent_liminf_cl by (metis asm convergent_def limI)
  }
  hence "(\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) \<partial>M)" using convergent_AE by (fast intro: nn_integral_cong_AE)
  moreover have "(\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (max 0 (ereal (X n \<omega>)))) \<partial>M) \<le> liminf (\<lambda>n. (\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (ereal (X n \<omega>))) \<partial>M))" 
    by (intro nn_integral_liminf) auto
  moreover have "(\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (ereal (X n \<omega>))) \<partial>M) = ennreal (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M)" for n 
    using e2ennreal_ereal ereal_max_0
    by (subst nn_integral_eq_integral[symmetric]) (fastforce intro!: nn_integral_cong integrable | presburger)+
  moreover have liminf_pos_part_finite: "liminf (\<lambda>n. ennreal (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M)) < \<infinity>" 
    unfolding liminf_SUP_INF 
    using Inf_lower2[OF _ bounded_pos_part] 
    by (intro order.strict_trans1[OF Sup_least, of _ "ennreal C"]) (metis (mono_tags, lifting) atLeast_iff imageE image_eqI order.refl, simp)
  ultimately have pos_part_finite: "(\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) < \<infinity>" by force
  (* - * - *)

  (* integral of negative part is < \<infinity> *)
  {
    fix \<omega>
    assume asm: "convergent (\<lambda>n. ereal (X n \<omega>))"
    hence "(\<lambda>n. - min 0 (ereal (X n \<omega>))) \<longlonglongrightarrow> - min 0 (lim (\<lambda>n. ereal (X n \<omega>)))" 
      using convergent_LIMSEQ_iff isCont_tendsto_compose continuous_min continuous_const continuous_ident continuous_at_e2ennreal
      by fast
    hence "(\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) \<longlonglongrightarrow> e2ennreal (- min 0 (lim (\<lambda>n. ereal (X n \<omega>))))" 
      using isCont_tendsto_compose continuous_at_e2ennreal by blast
    moreover have "lim (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) = e2ennreal (- min 0 (lim (\<lambda>n. ereal (X n \<omega>))))" using limI calculation by blast
    ultimately have "e2ennreal (- min 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) = liminf (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>))))" using convergent_liminf_cl by (metis asm convergent_def limI)
  }
  hence "(\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) \<partial>M)" using convergent_AE by (fast intro: nn_integral_cong_AE)
  moreover have "(\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. e2ennreal (- min 0 (ereal (X n \<omega>)))) \<partial>M) \<le> liminf (\<lambda>n. (\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (ereal (X n \<omega>))) \<partial>M))" 
    by (intro nn_integral_liminf) auto
  moreover have "(\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (ereal (X n \<omega>))) \<partial>M) = (\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M)" for n
  proof -
    have *: "(- min 0 c) = max 0 c - c" if "c \<noteq> \<infinity>" for c :: ereal using that by (cases "c \<ge> 0") auto
    hence "(\<integral>\<^sup>+\<omega>. e2ennreal (- min 0 (ereal (X n \<omega>))) \<partial>M) = (\<integral>\<^sup>+\<omega>. e2ennreal (max 0 (ereal (X n \<omega>)) - (ereal (X n \<omega>))) \<partial>M)" by simp
    also have "... = (\<integral>\<^sup>+ \<omega>. ennreal (max 0 (X n \<omega>) - (X n \<omega>)) \<partial>M)" using e2ennreal_ereal ereal_max_0 ereal_minus(1) by (intro nn_integral_cong) presburger
    also have "... = (\<integral>\<omega>. max 0 (X n \<omega>) - (X n \<omega>) \<partial>M)" using integrable by (intro nn_integral_eq_integral) auto 
    finally show ?thesis using Bochner_Integration.integral_diff integrable by simp
  qed
  moreover have "liminf (\<lambda>n. ennreal ((\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M))) < \<infinity>"
  proof -
    {
      fix n A
      assume asm: "ennreal ((\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M)) \<in> A"
      have "(\<integral>\<omega>. X 0 \<omega> \<partial>M) \<le> (\<integral>\<omega>. X n \<omega> \<partial>M)" using set_integral_le[OF sets.top order_refl, of n] space_F by (simp add: integrable set_integral_space)
      hence "(\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M) \<le> C - (\<integral>\<omega>. X 0 \<omega> \<partial>M)" using assms(2)[of n] by argo
      hence "ennreal ((\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) - (\<integral>\<omega>. X n \<omega> \<partial>M)) \<le> ennreal (C - (\<integral>\<omega>. X 0 \<omega> \<partial>M))" using ennreal_leI by blast
      hence "Inf A \<le> ennreal (C - (\<integral>\<omega>. X 0 \<omega> \<partial>M))" by (rule Inf_lower2[OF asm])
    }
    thus ?thesis 
      unfolding liminf_SUP_INF  
      by (intro order.strict_trans1[OF Sup_least, of _ "ennreal (C - (\<integral>\<omega>. X 0 \<omega> \<partial>M))"]) (metis (no_types, lifting)  atLeast_iff imageE image_eqI order.refl order_trans, simp)
  qed
  ultimately have neg_part_finite: "(\<integral>\<^sup>+ \<omega>. e2ennreal (- (min 0 (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M) < \<infinity>" by simp
  (* - * - *)
  
  (* Putting it all together now to show that the limit is integrable and < \<infinity> a.e. *)
  have "e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> = e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) + e2ennreal (- (min 0 (liminf (\<lambda>n. ereal (X n \<omega>)))))" for \<omega>
    unfolding ereal_abs_max_min
    by (simp add: eq_onp_same_args max_def plus_ennreal.abs_eq)
  hence "(\<integral>\<^sup>+ \<omega>. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<partial>M) = (\<integral>\<^sup>+ \<omega>. e2ennreal (max 0 (liminf (\<lambda>n. ereal (X n \<omega>)))) \<partial>M) + (\<integral>\<^sup>+ \<omega>. e2ennreal (- (min 0 (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M)" by (auto intro: nn_integral_add)
  hence nn_integral_finite: "(\<integral>\<^sup>+ \<omega>. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<partial>M) \<noteq> \<infinity>" using pos_part_finite neg_part_finite by auto
  hence finite_AE: "AE \<omega> in M. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>" by (intro nn_integral_noteq_infinite) auto
  moreover
  {
    fix \<omega>
    assume asm: "liminf (\<lambda>n. X n \<omega>) = limsup (\<lambda>n. X n \<omega>)" "\<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>"
    hence "(\<lambda>n. X n \<omega>) \<longlonglongrightarrow> real_of_ereal (liminf (\<lambda>n. X n \<omega>))" using limsup_le_liminf_real ereal_real' by simp
  }
  ultimately have converges: "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> real_of_ereal (liminf (\<lambda>n. X n \<omega>))" using liminf_limsup_AE by fastforce

  {
    fix \<omega>
    assume "e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>"
    hence "\<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<noteq> \<infinity>" by force
    hence "e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> = ennreal (norm (real_of_ereal (liminf (\<lambda>n. ereal (X n \<omega>)))))" by fastforce
  }
  hence "(\<integral>\<^sup>+ \<omega>. e2ennreal \<bar>liminf (\<lambda>n. ereal (X n \<omega>))\<bar> \<partial>M) = (\<integral>\<^sup>+ \<omega>. ennreal (norm (real_of_ereal (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M)" using finite_AE by (fast intro: nn_integral_cong_AE)  
  hence "(\<integral>\<^sup>+ \<omega>. ennreal (norm (real_of_ereal (liminf (\<lambda>n. ereal (X n \<omega>))))) \<partial>M) < \<infinity>" using nn_integral_finite by (simp add: order_less_le)
  hence "integrable M (\<lambda>\<omega>. real_of_ereal (liminf (\<lambda>n. X n \<omega>)))" by (intro integrableI_bounded) auto
  moreover have "(\<lambda>\<omega>. real_of_ereal (liminf (\<lambda>n. X n \<omega>))) \<in> borel_measurable F\<^sub>\<infinity>" using borel_measurable_liminf[OF F_infinity_measurableI] adapted by measurable
  ultimately show ?thesis using that converges by presburger
qed

text \<open>We state the theorem again for martingales and supermartingales.\<close>

corollary supermartingale_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "supermartingale M F 0 X"
      and "\<And>n. (\<integral>\<omega>. max 0 (- X n \<omega>) \<partial>M) \<le> C"
    obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" "integrable M X\<^sub>l\<^sub>i\<^sub>m" "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  obtain Y where *: "AE \<omega> in M. (\<lambda>n. - X n \<omega>) \<longlonglongrightarrow> Y \<omega>" "integrable M Y" "Y \<in> borel_measurable (F\<^sub>\<infinity>)"
    using supermartingale.uminus[OF assms(1), THEN submartingale_convergence_AE] assms(2) by auto
  hence "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> (- Y) \<omega>" "integrable M (- Y)" "- Y \<in> borel_measurable (F\<^sub>\<infinity>)" 
    using isCont_tendsto_compose[OF isCont_minus, OF continuous_ident] integrable_minus borel_measurable_uminus unfolding fun_Compl_def by fastforce+
  thus ?thesis using that[of "- Y"] by blast
qed

corollary martingale_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "martingale M F 0 X"
      and "\<And>n. (\<integral>\<omega>. \<bar>X n \<omega>\<bar> \<partial>M) \<le> C"
  obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" "integrable M X\<^sub>l\<^sub>i\<^sub>m" "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  interpret martingale_linorder M F 0 X unfolding martingale_linorder_def by (rule assms)
  have "max 0 (X n \<omega>) \<le> \<bar>X n \<omega>\<bar>" for n \<omega> by linarith
  hence "(\<integral>\<omega>. max 0 (X n \<omega>) \<partial>M) \<le> C" for n using assms(2)[THEN dual_order.trans, OF integral_mono, OF integrable_max] integrable by fast
  thus ?thesis using that submartingale_convergence_AE[OF submartingale_axioms] by blast
qed

corollary martingale_nonneg_convergence_AE:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "martingale M F 0 X" "\<And>n. AE \<omega> in M. X n \<omega> \<ge> 0"
  obtains X\<^sub>l\<^sub>i\<^sub>m where "AE \<omega> in M. (\<lambda>n. X n \<omega>) \<longlonglongrightarrow> X\<^sub>l\<^sub>i\<^sub>m \<omega>" "integrable M X\<^sub>l\<^sub>i\<^sub>m" "X\<^sub>l\<^sub>i\<^sub>m \<in> borel_measurable (F\<^sub>\<infinity>)"
proof -
  interpret martingale_linorder M F 0 X unfolding martingale_linorder_def by (rule assms)
  have "AE \<omega> in M. max 0 (- X n \<omega>) = 0" for n using assms(2)[of n] by force
  hence "(\<integral>\<omega>. max 0 (- X n \<omega>) \<partial>M) \<le> 0" for n by (simp add: integral_eq_zero_AE)
  thus ?thesis using that supermartingale_convergence_AE[OF supermartingale_axioms] by blast
qed

end

end
