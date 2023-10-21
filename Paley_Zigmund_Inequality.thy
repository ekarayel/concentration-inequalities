theory Paley_Zigmund_Inequality
  imports "HOL-Probability.Probability"
begin

context prob_space
begin

lemma paley_zigmund:
  assumes rv: "random_variable borel Z"
  assumes intZsq: "integrable M (\<lambda>z. (Z z)^2)"
  assumes t: "\<theta> \<le> 1"
  assumes Zpos: "\<And>z. z \<in> space M \<Longrightarrow> Z z \<ge> 0"
  shows "
    (variance Z + (1-\<theta>)^2 * (expectation Z)^2) *
    prob {z \<in> space M. Z z > \<theta> * expectation Z}
      \<ge> (1-\<theta>)^2 * (expectation Z)^2"
proof -
  have intZ: "integrable M Z"
    apply (subst square_integrable_imp_integrable[OF rv intZsq])
    by auto

  define eZ where "eZ = expectation Z"
  have "eZ \<ge> 0"
    unfolding eZ_def
    using Bochner_Integration.integral_nonneg Zpos by blast

  have "expectation (\<lambda>z. Z z - \<theta> * eZ) = expectation (\<lambda>z. Z z + (- \<theta> * eZ))"
    by auto
  moreover have "... = expectation Z + expectation (\<lambda>z. - \<theta> * eZ)"
    apply (subst Bochner_Integration.integral_add)
    using intZ by auto
  moreover have "... = eZ + (- \<theta> * eZ)"
    apply (subst lebesgue_integral_const)
    using eZ_def prob_space by auto
  ultimately have *: "expectation (\<lambda>z. Z z - \<theta> * eZ) = eZ - \<theta> * eZ"
    by linarith

  have ev: "{z \<in> space M. \<theta> * eZ < Z z} \<in> events"
    using rv unfolding borel_measurable_iff_greater
    by auto

  have ***: "eZ - \<theta> * eZ \<le>
    expectation (\<lambda>z. (Z z - \<theta> * eZ) * indicat_real {z \<in> space M. Z z > \<theta> * eZ} z)"
    unfolding *[symmetric]
    apply (auto intro!: integral_mono) 
    using intZ apply auto[1]
    apply (auto intro!: integrable_real_mult_indicator simp add: intZ ev)[1]
    unfolding indicator_def of_bool_def
    by (auto simp add: mult_nonneg_nonpos2)

  have "variance Z =
     variance (\<lambda>z. (Z z - \<theta> * eZ))"
    using "*" eZ_def by auto
  moreover have "... =
    expectation (\<lambda>z. (Z z - \<theta> * eZ)^2)
    - (expectation (\<lambda>x. Z x - \<theta> * eZ))\<^sup>2"
    apply (subst variance_eq)
    by (auto simp add: intZ power2_diff intZsq)

  moreover have "... = expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) - ((1-\<theta>)^2 * eZ^2)"
    unfolding *
    apply auto
    by (metis left_diff_distrib mult_1 power_mult_distrib)
  
  ultimately have veq: "expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) = (variance Z + (1-\<theta>)^2 * eZ^2)"
    by linarith

  have "(1-\<theta>)^2 * (expectation Z)^2 = (eZ - \<theta> * eZ)^2"
    unfolding eZ_def[symmetric]
    by (metis mult.commute mult.right_neutral power_mult_distrib right_diff_distrib')

  moreover have"... \<le>
    (expectation (\<lambda>z. (Z z - \<theta> * eZ) * indicat_real {z \<in> space M. Z z > \<theta> * eZ} z))^2"
    using ***  
    by (smt (verit) \<open>0 \<le> eZ\<close> mult.commute mult_left_le power2_less_imp_less t)

  moreover have "... \<le>
    expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * (expectation (\<lambda>z. indicat_real {z \<in> space M. Z z > \<theta> * eZ} z^2))"
    sorry
    (* Cauchy-Schwarz for E of product of two random variables *)

  moreover have "... = 
    expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * expectation (\<lambda>z. indicat_real {z \<in> space M. Z z > \<theta> * eZ} z)"
    by (metis (no_types, lifting) indicator_simps(1) indicator_simps(2) one_power2 power_zero_numeral)
  moreover have "... = expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * prob {z \<in> space M. Z z > \<theta> * eZ}"
    using ev measure_space_inter by auto
  ultimately have "(1-\<theta>)^2 * (expectation Z)^2 \<le>
     expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * prob {z \<in> space M. Z z > \<theta> * eZ}" by auto
  thus ?thesis
    using eZ_def veq by fastforce
qed

end

end