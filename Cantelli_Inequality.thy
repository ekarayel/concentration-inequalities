theory Cantelli_Inequality
  imports "HOL-Probability.Probability"
begin

context prob_space
begin

lemma cantelli_arith:
  assumes "a > (0::real)"
  shows "(V + (V / a)^2)  / (a + (V / a))^2 = V / (a ^2 + V)"
  using assms
  by (sos "((((() & ()) & (() & ())) & ((() & ()) & (() & ()))) & ((((() & ()) & (() & ())) & ((() & ()) & (() & ()))) & (((() & ()) & (() & ())) & ((() & ()) & (() & ())))))")

lemma cantelli_inequality:
  assumes [measurable]: "random_variable borel Z"
  assumes intZsq: "integrable M (\<lambda>z. Z z^2)"
  assumes a: "a > 0"
  shows "prob {z \<in> space M. Z z - expectation Z \<ge> a} \<le>
    variance Z / (a^2 + variance Z)"
proof -
  define u where "u = variance Z / a"
  have u: "u \<ge> 0"
    unfolding u_def
    by (simp add: a divide_nonneg_pos)
  define Y where "Y = (\<lambda>z. Z z + (-expectation Z))"
  have "random_variable borel (\<lambda>z. \<bar>Y z + u\<bar>)"
    unfolding Y_def
    by auto
  then have ev: "{z \<in> space M. a + u \<le> \<bar>Y z + u\<bar>} \<in> events"
    by auto

  have intZ:"integrable M Z"
    apply (subst square_integrable_imp_integrable[OF _ intZsq])
    by auto
  then have i1: "integrable M (\<lambda>z. (Z z - expectation Z + u)\<^sup>2)"
    unfolding power2_sum power2_diff using intZsq
    by auto

  have intY:"integrable M Y"
    unfolding Y_def using intZ by auto
  have intYsq:"integrable M (\<lambda>z. Y z^2)"
    unfolding Y_def power2_sum using intZsq intZ by auto

  have "expectation Y = 0"
    unfolding Y_def
    apply (subst Bochner_Integration.integral_add[OF intZ])
    using prob_space by auto
    
  then have "expectation (\<lambda>z. (Y z + u)^2) =
    expectation (\<lambda>z. (Y z)^2) + u^2"
    unfolding power2_sum
    apply (subst Bochner_Integration.integral_add[OF _ _])
    using intY intYsq apply auto[2]
    apply (subst Bochner_Integration.integral_add[OF _ _])
    using intY intYsq apply auto[2]
    using prob_space by auto
  then have *: "expectation (\<lambda>z. (Y z + u)^2) = variance Z + u^2"
    unfolding Y_def by auto

  have "
    prob {z \<in> space M. Z z - expectation Z \<ge> a} =
    prob {z \<in> space M. Y z + u \<ge> a + u}"
    apply (intro arg_cong[where f = prob])
    using Y_def by auto
  also have "... \<le> prob {z \<in> space M. a + u \<le> \<bar>Y z + u\<bar>}"
    apply (intro finite_measure_mono[OF _ ev])
    by auto

  also have "... \<le> expectation (\<lambda>z. (Y z + u)^2) / (a + u)^2"
    apply (intro second_moment_method)
    unfolding Y_def using a u i1 by auto
  also have "... = ((variance Z) + u^2)  / (a + u)^2"
    using * by auto
  also have "... = variance Z / (a ^2 + variance Z)"
    unfolding u_def using a by (auto intro!: cantelli_arith)
  finally show ?thesis .
qed

end

end