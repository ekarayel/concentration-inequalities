theory Bennett_Inequality
  imports Concentration_Inequalities_Preliminary
begin

context prob_space
begin

(* Restating Chernoff inequality for independent variables *)
lemma indep_vars_Chernoff_ineq_ge:
  assumes I: "finite I"
  assumes ind: "indep_vars (\<lambda> _. borel) X I"
  assumes sge: "s \<ge> 0"
  assumes int: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. exp (s * X i x))"
  shows "prob {x \<in> space M. (\<Sum>i \<in>I. X i x - expectation (X i)) \<ge> t} \<le>
    exp (-s*t) *
    (\<Prod>i\<in>I. expectation (\<lambda>x. exp(s * (X i x - expectation (X i)))))"
proof (cases "s = 0")
  case [simp]: True
  thus ?thesis
    by (simp add: prob_space)
next
  case False
  then have s: "s > 0" using sge by auto

  have [measurable]: "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
    using ind unfolding indep_vars_def by blast

  have indep1: "indep_vars (\<lambda>_. borel)
     (\<lambda>i \<omega>. exp (s * (X i \<omega> - expectation (X i)))) I"
    apply (intro indep_vars_compose[OF ind, unfolded o_def])
    by auto

  define S where "S = (\<lambda>x. (\<Sum>i \<in>I. X i x - expectation (X i)))"
 
  have int1: "\<And>i. i \<in> I \<Longrightarrow>
         integrable M (\<lambda>\<omega>. exp (s * (X i \<omega> - expectation (X i))))"
    by (auto simp add: algebra_simps exp_diff int)

  have eprod: "\<And>x. exp (s * S x) = (\<Prod>i\<in>I. exp(s * (X i x - expectation (X i))))"
     unfolding S_def
     by (simp add: assms(1) exp_sum vector_space_over_itself.scale_sum_right)

  from indep_vars_integrable[OF I indep1 int1]
  have intS: "integrable M (\<lambda>x. exp (s * S x))"
    unfolding eprod by auto

  then have si: "set_integrable M (space M) (\<lambda>x. exp (s * S x))"
    unfolding set_integrable_def
    apply (intro integrable_mult_indicator)
    by auto

  from Chernoff_ineq_ge[OF s si]
  have "prob {x \<in> space M. S x \<ge> t} \<le> exp (- s * t) * (\<integral>x\<in>space M. exp (s * S x)\<partial>M)"
    by auto

  also have "(\<integral>x\<in>space M. exp (s * S x)\<partial>M) = expectation (\<lambda>x. exp(s * S x))"
     unfolding set_integral_space[OF intS] by auto

  also have "... = expectation (\<lambda>x. \<Prod>i\<in>I. exp(s * (X i x - expectation (X i))))"
     unfolding S_def
     by (simp add: assms(1) exp_sum vector_space_over_itself.scale_sum_right)
  also have "... = (\<Prod>i\<in>I. expectation (\<lambda>x. exp(s * (X i x - expectation (X i)))))"
     apply (intro indep_vars_lebesgue_integral[OF I indep1 int1]) .
  finally show ?thesis
    unfolding S_def
    by auto
qed

definition bennett_h::"real \<Rightarrow> real"
  where "bennett_h u = (1 + u) * ln (1 + u) - u"

lemma exp_sub_two_terms_eq:
  fixes x :: real
  shows "exp x - x - 1 = (\<Sum>n. x^(n+2) / fact (n+2))"
    "summable (\<lambda>n. x^(n+2) / fact (n+2))"
proof -
  have "(\<Sum>i<2. inverse (fact i) * x ^ i) = 1 + x"
    apply code_simp
    by auto
  thus "exp x - x - 1 = (\<Sum>n. x^(n+2) / fact (n+2))"
    unfolding exp_def
    apply (subst suminf_split_initial_segment[where k = 2])
    by (auto simp add: summable_exp divide_inverse_commute)
  have "summable (\<lambda>n. x^n / fact n)"
    by (simp add: divide_inverse_commute summable_exp)
  then have "summable (\<lambda>n. x^(Suc (Suc n)) / fact (Suc (Suc n)))"
    apply (subst summable_Suc_iff)
    apply (subst summable_Suc_iff)
    by auto 
  thus "summable (\<lambda>n. x^(n+2) / fact (n+2))" by auto
qed

lemma psi_mono:
  defines "f \<equiv> (\<lambda>x. (exp x - x - 1) - x^2 / 2)"
  assumes xy: "a \<le> (b::real)"
  shows "f a \<le> f b"
proof -
  have 1: "(f has_real_derivative (exp x - x - 1)) (at x)" for x
    unfolding f_def
    by (auto intro!: derivative_eq_intros)
  
  have 2: "\<And>x. x \<in> {a..b} \<Longrightarrow> 0 \<le> exp x - x - 1"
    by (smt (verit) exp_ge_add_one_self)

  from deriv_nonneg_imp_mono[OF 1 2 xy]
  show ?thesis by auto
qed

(* TODO: not sure if this holds for y < 0 too *)
lemma psi_inequality:
  assumes le: "x \<le> (y::real)" "y \<ge> 0"
  shows "y^2 * (exp x - x - 1) \<le> x^2 * (exp y - y - 1)"
proof -

  have x: "exp x - x - 1 = (\<Sum>n. (x^(n+2) / fact (n+2)))"
    "summable (\<lambda>n. x^(n+2) / fact (n+2))"
    using exp_sub_two_terms_eq .

  have y: "exp y - y - 1 = (\<Sum>n. (y^(n+2) / fact (n+2)))"
    "summable (\<lambda>n. y^(n+2) / fact (n+2))"
    using exp_sub_two_terms_eq .

  (* Simplify the expressions in the inequality *)
  have l:"y^2 * (exp x - x - 1) = (\<Sum>n. y^2 * (x^(n+2) / fact (n+2)))"
    using x
    apply (subst suminf_mult)
    by auto
  have ls: "summable (\<lambda>n. y^2 * (x^(n+2) / fact (n+2)))"
    by (intro summable_mult[OF x(2)])

  have r:"x^2 * (exp y - y - 1) = (\<Sum>n. x^2 * (y^(n+2) / fact (n+2)))"
    using y
    apply (subst suminf_mult)
    by auto
  have rs: "summable (\<lambda>n. x^2 * (y^(n+2) / fact (n+2)))"
    by (intro summable_mult[OF y(2)])

  have "\<bar>x\<bar> \<le> \<bar>y\<bar> \<or> \<bar>y\<bar> < \<bar>x\<bar>" by auto
  moreover {
    assume "\<bar>x\<bar> \<le> \<bar>y\<bar>"
    then have "x^ n \<le> y ^n" for n
    by (smt (verit, ccfv_threshold) bot_nat_0.not_eq_extremum le power_0 real_root_less_mono real_root_power_cancel root_abs_power)
    then have "(x^2 * y^2) * x^n \<le> (x^2 * y^2) * y^n" for n
      by (simp add: mult_left_mono)
    then have "y\<^sup>2 * (x ^ (n + 2)) \<le> x\<^sup>2 * (y ^ (n + 2))" for n
      by (metis (full_types) ab_semigroup_mult_class.mult_ac(1) mult.commute power_add)
    then have "y\<^sup>2 * (x ^ (n + 2)) / fact (n+2)\<le> x\<^sup>2 * (y ^ (n + 2)) / fact (n+2)" for n
      by (meson divide_right_mono fact_ge_zero)
    then have "(\<Sum>n. y^2 * (x^(n+2) / fact (n+2))) \<le> (\<Sum>n. x^2 * (y^(n+2) / fact (n+2)))"
      apply (intro suminf_le[OF _ ls rs])
      by auto
    then have "y^2 * (exp x - x - 1) \<le> x^2 * (exp y - y - 1)"
    using l r by presburger
  }
  moreover {
    assume ineq: "\<bar>y\<bar> < \<bar>x\<bar>"

    from psi_mono[OF assms(1)]
    have "(exp x - x - 1) - x^2 /2 \<le> (exp y - y - 1) - y^2/2" .

    then have "y^2 * ((exp x - x - 1) - x^2 /2) \<le> x^2 * ((exp y - y - 1) - y^2/2)"
      by (smt (verit, best) ineq diff_divide_distrib exp_lower_Taylor_quadratic le(1) le(2) mult_nonneg_nonneg one_less_exp_iff power_zero_numeral prob_space.psi_mono prob_space_completion right_diff_distrib zero_le_power2)
      
    then have "y^2 * (exp x - x - 1) \<le> x^2 * (exp y - y - 1)"
      by (simp add: mult.commute right_diff_distrib)
  }
  ultimately show ?thesis by auto
qed

(* Helper lemma, starting with normalized zero-mean variables *)
lemma bennett_inequality_1:
  assumes I: "finite I"
  assumes ind: "indep_vars (\<lambda> _. borel) X I"
  assumes intsq: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)^2)"
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<le> 1"
  assumes e0: "\<And>i. i \<in> I \<Longrightarrow> expectation (X i) = 0"
  assumes t: "t \<ge> 0"
  defines "V \<equiv> (\<Sum>i \<in> I. variance (X i))"
  shows "prob {x \<in> space M. (\<Sum>i \<in> I. X i x) \<ge> t} \<le>
    exp (-V * bennett_h (t / V))"
proof (cases "V = 0")
  case True
  then show ?thesis
    by auto
next
  case f: False
  have "V \<ge> 0"
    unfolding V_def
    apply (intro sum_nonneg  integral_nonneg_AE)
    by auto
  then have Vpos: "V > 0" using f by auto

  define l :: real where "l = ln(1 + t / V)"
  then have l: "l \<ge> 0"
    using t Vpos by auto
  have rv[measurable]: "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
    using ind unfolding indep_vars_def by blast

  define \<psi> where "\<psi> = (\<lambda>x::real. exp(x) - x - 1)"

  have rw: "exp y = 1 + y + \<psi> y" for y
    unfolding \<psi>_def by auto

  have ebnd: "\<And>i. i \<in> I \<Longrightarrow>
         AE x in M. exp (l * X i x) \<le> exp l"
     apply (drule bnd)
     using l by (auto simp add: mult_left_le)

  (* integrability *)
  have int: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x))"
  using rv intsq square_integrable_imp_integrable by blast

  have intl: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (l * X i x))"
    using int by blast

  have intexpl: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. exp (l * X i x))"
    apply (intro integrable_const_bound[where B = "exp l"])
    using ebnd by auto

  have intpsi: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. \<psi> (l * X i x))"
    unfolding \<psi>_def
    using intl intexpl by auto

  have **: "\<And>i. i \<in> I \<Longrightarrow>
    expectation (\<lambda>x. \<psi> (l * X i x)) \<le> \<psi> l * expectation (\<lambda>x. (X i x)^2)"
  proof -
    fix i assume i: "i \<in> I"
    then have "AE x in M. l * X i x \<le> l"
      using ebnd by auto
    then have "AE x in M. l^2 * \<psi> (l * X i x) \<le> (l * X i x)^2 * \<psi> l"
      using psi_inequality[OF _ l] unfolding \<psi>_def
      by auto
    then have "AE x in M. l^2 * \<psi> (l * X i x) \<le> l^2 * (\<psi> l * (X i x)^2)"
      by (auto simp add: field_simps)
    then have "AE x in M. \<psi> (l * X i x) \<le> \<psi> l * (X i x)^2 "
      by (smt (verit, best) AE_cong \<psi>_def exp_eq_one_iff mult_cancel_left mult_eq_0_iff mult_left_mono zero_eq_power2 zero_le_power2)
    then have "AE x in M. 0 \<le> \<psi> l * (X i x)^2 - \<psi> (l * X i x) "
      by auto
    then have "expectation (\<lambda>x. \<psi> l * (X i x)^2 + (- \<psi> (l * X i x))) \<ge> 0"
      by (simp add: integral_nonneg_AE)
    also have "expectation (\<lambda>x. \<psi> l * (X i x)^2 + (- \<psi> (l * X i x))) =
        \<psi> l * expectation (\<lambda>x. (X i x)^2) - expectation (\<lambda>x. \<psi> (l * X i x))"
      apply (subst Bochner_Integration.integral_add)
      using intpsi[OF i] intsq[OF i] by auto
    finally show "expectation (\<lambda>x. \<psi> (l * X i x)) \<le> \<psi> l * expectation (\<lambda>x. (X i x)^2)"
      by auto
  qed

  (* Analyzing the expectation *)
  then have *: "\<And>i. i \<in> I \<Longrightarrow> expectation (\<lambda>x. exp (l * X i x)) \<le>
      exp(\<psi> l * expectation(\<lambda>x. X i x^2))"
  proof -
    fix i
    assume iI: "i \<in> I"
    have "expectation (\<lambda>x. exp (l * X i x)) =
      1 + l * expectation (\<lambda>x. X i x) +
       expectation (\<lambda>x. \<psi> (l * X i x))"
      unfolding rw
      apply (subst Bochner_Integration.integral_add)
      using iI intl intpsi apply auto[2]
      apply (subst Bochner_Integration.integral_add)
      using intl iI prob_space by auto
    also have "... = 1 + expectation (\<lambda>x. \<psi> (l * X i x))"
      using e0[OF iI] by auto
    also have "... \<le> 1 + \<psi> l * expectation (\<lambda>x. X i x^2)"
      using **[OF iI] by auto
    also have "... \<le> exp (\<psi> l  * expectation (\<lambda>x. X i x^2))"
      by auto
    finally show "expectation (\<lambda>x. exp (l * X i x)) \<le>
      exp(\<psi> l * expectation(\<lambda>x. X i x^2))" .
  qed

  have Veq: "V = (\<Sum>i \<in> I. expectation(\<lambda>x. X i x^2))"
    unfolding V_def
    using e0 by auto
    
  from indep_vars_Chernoff_ineq_ge[OF I ind l intexpl]
  have "prob {x \<in> space M. (\<Sum>i \<in> I. X i x) \<ge> t} \<le> exp (- l * t) *
     (\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x))))"
    using e0 by auto
  also have "(\<Prod>i\<in>I. expectation (\<lambda>x. exp (l * (X i x)))) \<le>
    (\<Prod>i\<in>I.  exp(\<psi> l * expectation(\<lambda>x. X i x^2)))"
    by (auto intro: prod_mono simp add: *)
  also have "... =
    exp (\<psi> l * V)"
    by (simp add: Veq I exp_sum sum_distrib_left)
  finally have "prob {x \<in> space M. (\<Sum>i \<in> I. X i x) \<ge> t} \<le>
    exp (\<psi> l * V - l * t)"
    by (simp add:mult_exp_exp)

  also have "\<psi> l * V - l * t = -V * bennett_h (t / V)"
    unfolding \<psi>_def l_def bennett_h_def
    apply (subst exp_ln)
    apply (auto simp add: algebra_simps)
    by (smt (verit) Vpos divide_nonneg_nonneg t)
  finally show ?thesis .
qed

end

end
