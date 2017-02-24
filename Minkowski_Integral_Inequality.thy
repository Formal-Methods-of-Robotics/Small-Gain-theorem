
(* Title:      Minkowski Integral Inequality
   Author:     Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk>
   Maintainer: Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk> 
*)

theory Minkowski_Integral_Inequality
imports  Complex_Main 
"~~/src/HOL/Probability/Set_Integral"
"~~/src/HOL/library/Quadratic_Discriminant"
begin

lemma nonnegative_of_quadratic_polynomial:
  fixes a b c x :: real
  assumes  "a > 0"
  and  "\<And>x. a*x^2 + b*x + c\<ge>0 "
  shows "discrim a b c \<le>0"
proof -
have "\<exists>x. a*x^2 + b*x + c<0 " when "discrim a b c > 0" "a>0"
  proof -
    let ?P="\<lambda>x. a*x^2 + b*x +c"
   have "?P (- b / (2*a)) =  (4*a*c-b^2)/(4*a)" using \<open>a>0\<close>
   apply (auto simp add:field_simps)
      by algebra
   also have "... <0"
      using that unfolding discrim_def by (simp add: divide_neg_pos)
   finally show ?thesis by blast
   qed
then show ?thesis using assms
  using not_less by blast
qed

lemma  schwaz_integral_ineq:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<And>t. t \<in> A"
          "set_integrable M A f" 
          "set_integrable M A g "
          "set_integrable M A (\<lambda>t. (f t)\<^sup>2)" 
          "set_integrable M A (\<lambda>t. (g t)\<^sup>2)"
          "set_integrable M A (\<lambda>t. f t * g t)"
          "(LINT t:A|M. (g t)\<^sup>2) > 0"
  shows "(LINT t:A|M. f t * g t) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)"
proof -
  fix  \<alpha>:: "real"
  let ?a ="(LINT t:A|M. (g t)\<^sup>2)" and ?b="2*(LINT t:A|M. f t * g t)" and ?c="(LINT t:A|M. (f t)\<^sup>2)"
  have "\<And>\<alpha>. (LINT t:A|M. (f t + \<alpha>* g t)\<^sup>2) \<ge> 0" 
    by (simp add: integral_nonneg_AE)
  then have "\<And>\<alpha>. (LINT t:A|M. (f t)\<^sup>2 + 2 * (f t *(\<alpha> * g t)) + (\<alpha> * g t)\<^sup>2 ) \<ge> 0" 
    by (simp add: add.commute add.left_commute mult.assoc power2_sum)
  then have "\<And>\<alpha>. (LINT t:A|M. (f t)\<^sup>2 + 2*\<alpha>* (f t * g t) + (\<alpha>)\<^sup>2*(g t)\<^sup>2) \<ge> 0 " 
    by (simp add: diff_add_eq mult.assoc mult.left_commute semiring_normalization_rules(30))
  then have "\<And>\<alpha>. (LINT t:A|M. (f t)\<^sup>2) + 2*\<alpha>*(LINT t:A|M. f t * g t) + (\<alpha>)\<^sup>2* (LINT t:A|M.(g t)\<^sup>2) \<ge> 0"
    using assms by force
  then have "\<And>\<alpha>. ?c + ?b*\<alpha> + ?a*(\<alpha>)\<^sup>2 \<ge> 0" 
    by (simp add: mult.assoc mult.commute)
  then have "\<And>\<alpha>. ?a*(\<alpha>)\<^sup>2 + ?b*\<alpha> + ?c \<ge>0" 
    by (metis (lifting) add.assoc add.commute)
  then have "discrim ?a ?b ?c \<le> 0"  
    using assms nonnegative_of_quadratic_polynomial by presburger
  then have s1: "?b\<^sup>2 \<le> 4 * ?a * ?c" 
    by (simp add: discrim_def)
  have "?b\<^sup>2\<ge>0" 
    by simp
  then have "?b \<le> sqrt(4 * ?a * ?c)" 
    using s1 by (simp add: real_le_rsqrt)
  then have "?b \<le> 2 * sqrt(?a) * sqrt(?c)" 
    by (simp add: real_sqrt_mult_distrib2)
  then have "2*(LINT t:A|M. f t * g t) \<le> 2 * sqrt(LINT t:A|M. (g t)\<^sup>2) * sqrt(LINT t:A|M. (f t)\<^sup>2)" 
    by blast
  then have "(LINT t:A|M. f t * g t) \<le> sqrt(LINT t:A|M. (g t)\<^sup>2) * sqrt(LINT t:A|M. (f t)\<^sup>2)" 
    by linarith
  then have "(LINT t:A|M. f t * g t) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)" 
    by (simp add: semiring_normalization_rules(7))
  from this assms show "(LINT t:A|M. f t * g t) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)" 
    by fastforce
qed

lemma minkowski_integral_ineq:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<And>t. t \<in> A"
          "set_integrable M A f" 
          "set_integrable M A g"
          "set_integrable M A (\<lambda>t. (f t)\<^sup>2)" 
          "set_integrable M A (\<lambda>t. (g t)\<^sup>2)"
          "set_integrable M A (\<lambda>t. f t * g t)"
          "(LINT t:A|M. (g t)\<^sup>2) > 0"
  shows "sqrt(LINT t:A|M. (f t + g t)\<^sup>2) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2)"
proof -
  have "(LINT t:A|M. (f t + g t)\<^sup>2) = (LINT t:A|M. (f t)\<^sup>2 + 2 * (f t * g t) + (g t)\<^sup>2)" 
    by (simp add: add.commute add.left_commute mult.assoc power2_sum)
  then have "(LINT t:A|M. (f t + g t)\<^sup>2) = (LINT t:A|M. (f t)\<^sup>2) + 2*(LINT t:A|M. (f t * g t)) + (LINT t:A|M. (g t)\<^sup>2)"
    using assms by auto
  then have "(LINT t:A|M. (f t + g t)\<^sup>2) \<le> 
   (LINT t:A|M. (f t)\<^sup>2) + 2*(sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)) + (LINT t:A|M. (g t)\<^sup>2)"
    using schwaz_integral_ineq assms by auto
  then have "(LINT t:A|M. (f t + g t)\<^sup>2) \<le> 
   (sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2)) * (sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2))"
    by (simp add: add.commute distrib_right sum_squares_ge_zero semiring_normalization_rules(34))
  then have m:"(LINT t:A|M. (f t + g t)\<^sup>2) \<le> (sqrt(LINT t:A|M. (f t)\<^sup>2)+ sqrt(LINT t:A|M. (g t)\<^sup>2))\<^sup>2"
    by (simp add: power2_eq_square)
(* to get rid of asb *)
  have lhs: "sqrt(LINT t:A|M. (f t + g t)\<^sup>2) \<ge> 0" 
    by (simp add: integral_nonneg_AE)
  have rhs: "sqrt(LINT t:A|M. (f t)\<^sup>2) \<ge> 0 \<and> sqrt(LINT t:A|M. (g t)\<^sup>2) \<ge> 0"
    by (simp add: integral_nonneg_AE)
  from lhs rhs m have "sqrt(LINT t:A|M. (f t + g t)\<^sup>2) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2)+ sqrt(LINT t:A|M. (g t)\<^sup>2)" 
    using real_le_lsqrt by force
  thus ?thesis.
qed 


(*for negative*)

lemma  schwaz_integral_ineq_ng:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<And>t. t \<in> A"
          "set_integrable M A f" 
          "set_integrable M A g "
          "set_integrable M A (\<lambda>t. (f t)\<^sup>2)" 
          "set_integrable M A (\<lambda>t. (g t)\<^sup>2)"
          "set_integrable M A (\<lambda>t. f t * g t)"
          "(LINT t:A|M. (g t)\<^sup>2) > 0"
  shows "(LINT t:A|M. f t * - g t) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)"
proof -
  fix  \<alpha>:: "real"
  let ?a ="(LINT t:A|M. (g t)\<^sup>2)" and ?b="2*(LINT t:A|M. f t * -g t)" and ?c="(LINT t:A|M. (f t)\<^sup>2)"
  have "\<And>\<alpha>. (LINT t:A|M. (f t - \<alpha>* g t)\<^sup>2) \<ge> 0" 
    by (simp add: integral_nonneg_AE)
  then have "\<And>\<alpha>. (LINT t:A|M. (f t)\<^sup>2 + (\<alpha>*g t)\<^sup>2 - 2*\<alpha>*(f t * g t)) \<ge> 0"
    by (simp add:  power2_diff linordered_field_class.sign_simps(24) mult.left_commute)
  then have "\<And>\<alpha>. (LINT t:A|M. (f t)\<^sup>2) + 2*\<alpha>*(LINT t:A|M. f t * - g t) + (\<alpha>)\<^sup>2*(LINT t:A|M. (g t)\<^sup>2) \<ge> 0"
    using assms by (simp add: diff_add_eq semiring_normalization_rules(30))
  then have " \<And>\<alpha>. ?c + ?b*\<alpha> + ?a*(\<alpha>)\<^sup>2 \<ge> 0" 
    by (simp add: mult.assoc mult.commute)
  then have "\<And>\<alpha>. ?a*(\<alpha>)\<^sup>2 + ?b*\<alpha> + ?c \<ge>0" 
    by (metis (lifting) add.assoc add.commute)
  then have " discrim ?a ?b ?c \<le> 0"  
    using assms  nonnegative_of_quadratic_polynomial by presburger
  then have m:" ?b\<^sup>2 \<le> 4 * ?a * ?c" 
    by (simp add: discrim_def)
  have "?b\<^sup>2\<ge>0" by simp
  from this m have "?b \<le> sqrt(4 * ?a * ?c)" 
    by (simp add: real_le_rsqrt)
  then have "?b \<le> 2 * sqrt(?a) * sqrt(?c)"
    by (simp add: linordered_field_class.sign_simps(24) mult.left_commute real_sqrt_mult_distrib2)   
  from this assms show "(LINT t:A|M. f t * -g t) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)" 
    by (simp add: linordered_field_class.sign_simps(24) mult.left_commute)
qed

lemma  minkowski_integral_ineq_ng:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<And>t. t \<in> A"
          "set_integrable M A f" 
          "set_integrable M A g "
          "set_integrable M A (\<lambda>t. (f t)\<^sup>2)" 
          "set_integrable M A (\<lambda>t. (g t)\<^sup>2)"
          "set_integrable M A (\<lambda>t. f t * g t)"
          "(LINT t:A|M. (g t)\<^sup>2) > 0"
  shows "sqrt(LINT t:A|M. (f t - g t)\<^sup>2) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2)"
proof -
  have "(LINT t:A|M. (f t + -g t)\<^sup>2) = (LINT t:A|M. (f t)\<^sup>2 + 2*(f t * -g t) + (g t)\<^sup>2)" 
    by (simp add: diff_add_eq power2_diff mult.assoc)
  then have mn1: "(LINT t:A|M. (f t + -g t)\<^sup>2) = 
    (LINT t:A|M. (f t)\<^sup>2) + 2*(LINT t:A|M. f t * -g t) + (LINT t:A|M. (g t)\<^sup>2)"
    using assms by auto
  have "(LINT t:A|M. f t * -g t) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * sqrt(LINT t:A|M. (g t)\<^sup>2)"
    using schwaz_integral_ineq_ng assms by blast
  from this mn1  have "(LINT t:A|M. (f t + -g t)\<^sup>2) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) * (sqrt(LINT t:A|M. (f t)\<^sup>2)
    + sqrt(LINT t:A|M. (g t)\<^sup>2)) + sqrt(LINT t:A|M. (g t)\<^sup>2) * (sqrt(LINT t:A|M. (g t)\<^sup>2) + sqrt(LINT t:A|M. (f t)\<^sup>2))"
    by (simp add: sum_squares_ge_zero semiring_normalization_rules(34))
  then have mn2: "(LINT t:A|M. (f t + -g t)\<^sup>2) \<le> 
    (sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2))\<^sup>2"
    by (simp add: add.commute distrib_right power2_eq_square)
(* to get rid of asb *)
  have lhs: "sqrt(LINT t:A|M. (f t + -g t)\<^sup>2) \<ge> 0" 
    by (simp add: integral_nonneg_AE)
  have rhs: "sqrt(LINT t:A|M. (f t)\<^sup>2) \<ge> 0 \<and> sqrt(LINT t:A|M. (g t)\<^sup>2) \<ge> 0"
    by (simp add: integral_nonneg_AE)
  show ?thesis using lhs rhs mn2 real_le_lsqrt by force
qed 

end 