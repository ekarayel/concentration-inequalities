theory Paley_Zigmund_Inequality
  imports "HOL-Probability.Probability"
    Lp.Lp
begin

context prob_space
begin

lemma arith:
  assumes "a \<ge> (0::real)" "b \<ge> 0" "c \<ge> 0"
    "a \<le> (b powr (1/2)) * (c powr (1/2))"
  shows "a^2 \<le> b * c"
  by (metis assms(1) assms(2) assms(3) assms(4) powr_half_sqrt real_sqrt_le_iff real_sqrt_mult real_sqrt_unique)

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

  have sqI:"(indicat_real E x)^2 = indicat_real E (x::'a)" for E x
    by (metis indicator_simps(1) indicator_simps(2) one_power2 zero_power2)

  define eZ where "eZ = expectation Z"
  have "eZ \<ge> 0"
    unfolding eZ_def
    using Bochner_Integration.integral_nonneg Zpos by blast
  then have ezp:"eZ - \<theta> * eZ \<ge> 0"
    by (metis diff_ge_0_iff_ge mult.commute mult_left_le t)

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

  (* TODO: Generalize beyond p = 2, q = 2 *)
  define p where "p = (2::real)"
  define q where "q = (2::real)"
  have pq: "0 < (p::real)" "0 < (q::real)" "1 / p + 1 / q = 1 "
    unfolding p_def q_def by auto

  have bm1: "(\<lambda>z. (Z z - \<theta> * eZ)) \<in> borel_measurable M"
    using borel_measurable_const borel_measurable_diff rv by blast
  have bm2: "(\<lambda>z. indicat_real {z \<in> space M. Z z > \<theta> * eZ} z) \<in> borel_measurable M"
    using borel_measurable_indicator ev by blast
  have int1: "integrable M (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p)"
    unfolding p_def by (auto simp add: intZsq power2_diff intZ)

  have "integrable M
   (\<lambda>x. 1 * indicat_real {z \<in> space M. \<theta> * eZ < Z z} x)"
    apply (intro integrable_real_mult_indicator[OF ev])
    by auto
    
  then have int2: " integrable M
     (\<lambda>x. \<bar>indicat_real {z \<in> space M. \<theta> * eZ < Z z} x\<bar> powr q)"
    unfolding q_def by (auto simp add: sqI )

  from Holder_inequality[OF pq bm1 bm2 int1 int2]
  have hi: "\<bar>expectation (\<lambda>x. (Z x - \<theta> * eZ) * indicat_real {z \<in> space M. \<theta> * eZ < Z z} x)\<bar>
    \<le> expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p) *
      expectation (\<lambda>x. \<bar>indicat_real {z \<in> space M. \<theta> * eZ < Z z} x\<bar> powr q) powr (1 / q)"
    by auto

  have "eZ - \<theta> * eZ \<le>
    expectation (\<lambda>z. (Z z - \<theta> * eZ) * indicat_real {z \<in> space M. Z z > \<theta> * eZ} z)"
    unfolding *[symmetric]
    apply (auto intro!: integral_mono) 
    using intZ apply auto[1]
    apply (auto intro!: integrable_real_mult_indicator simp add: intZ ev)[1]
    unfolding indicator_def of_bool_def
    by (auto simp add: mult_nonneg_nonpos2)

  moreover have "... \<le>
      expectation (\<lambda>x. (Z x - \<theta> * eZ)^2 ) powr (1 / 2) *
      expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x) powr (1 / 2)"
    using hi unfolding p_def q_def by (auto simp add: sqI)

  ultimately have ***: "(eZ - \<theta> * eZ)^2 \<le>
     expectation (\<lambda>x. (Z x - \<theta> * eZ)^2 ) *
     expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x)"
    by (auto intro!: arith[OF ezp])

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

  moreover have "... \<le> 
    expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * expectation (\<lambda>z. indicat_real {z \<in> space M. Z z > \<theta> * eZ} z)"
    using "***" by blast
  moreover have "... = expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * prob {z \<in> space M. Z z > \<theta> * eZ}"
    using ev measure_space_inter by auto
  ultimately have "(1-\<theta>)^2 * (expectation Z)^2 \<le>
     expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) * prob {z \<in> space M. Z z > \<theta> * eZ}" by auto
  thus ?thesis
    using eZ_def veq by fastforce
qed

end

end