
(* Title:      L2 Norm Integral
   Author:     Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk>
   Maintainer: Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk> 
*)

theory L2Norm_Integral
imports 
"~~/src/HOL/Probability/Set_Integral"
"~~/Minkowski_Integral_Inequality"
begin

definition L2norm:: "real measure \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real" where
  "L2norm M f A = sqrt (LINT  t:A|M. (f t)\<^sup>2)"
  
lemma L2norm_cong1:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> L2norm M f A = L2norm M g B"
  unfolding L2norm_def by (metis indicator_simps(2) mult_zero_left real_scaleR_def)

lemma strong_L2norm_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B =simp=> f x = g x\<rbrakk> \<Longrightarrow> L2norm M f A = L2norm M g B"
  unfolding L2norm_def simp_implies_def by (metis (full_types) L2norm_cong1 L2norm_def) 

lemma L2norm_nonneg: 
  shows "L2norm M f A \<ge> 0"
proof -
  have "\<forall>t. (f t)\<^sup>2 \<ge> 0" 
    by simp
  then have "(LINT  t:A|M. (f t)\<^sup>2) \<ge> 0" 
    by (simp add: integral_nonneg_AE)
  then have "sqrt (LINT  t:A|M. (f t)\<^sup>2) \<ge> 0" 
    by simp
  from this L2norm_def show ?thesis 
    by metis 
qed

lemma L2norm_zero: "\<forall>t\<in>A. f t = 0 \<Longrightarrow> L2norm M f A = 0" unfolding L2norm_def 
proof -
  assume "\<forall>t\<in>A. f t = 0"
  then have "\<And>t. indicator A t *\<^sub>R (f t)\<^sup>2 = 0"
    by auto
  then show "sqrt (LINT t:A|M. (f t)\<^sup>2) = 0"
    by (simp add: integral_eq_zero_AE)
qed 

lemma L2norm_right_distrib:
  fixes M a b c and f :: "real \<Rightarrow> real"
  assumes "0 \<le> c" "set_integrable M A f" 
  shows "c * L2norm M f A = L2norm M (\<lambda>t. c * f t) A"
proof -
  have "c* (sqrt(LINT t:A|M. (f t)\<^sup>2)) = sqrt(c\<^sup>2 *(LINT t:A|M. (f t)\<^sup>2))" 
    by (simp add: assms real_sqrt_mult_distrib2) 
  then have "c * sqrt(LINT t:A|M. (f t)\<^sup>2) = sqrt(LINT t:A|M. c\<^sup>2 * (f t)\<^sup>2)"
    by (metis (no_types) set_integral_mult_right)
  then have "c * sqrt(LINT t:A|M. (f t)\<^sup>2) = sqrt(LINT t:A|M. (c * f t)\<^sup>2)"
    by (simp add: power_mult_distrib)
  thus ?thesis
    by (metis L2norm_def)
qed

lemma L2norm_left_distrib:
  fixes M a b c and f :: "real \<Rightarrow> real"
  assumes "0 \<le> c"  "set_integrable M A f" 
  shows "L2norm M f A * c = L2norm M (\<lambda>t. f t * c) A"
proof -
  have "sqrt (LINT t:A|M. (f t)\<^sup>2) * c = sqrt((LINT t:A|M. (f t)\<^sup>2) * c\<^sup>2)"
    by (simp add: assms real_sqrt_mult_distrib2) 
  then have "sqrt(LINT t:A|M. (f t)\<^sup>2) * c = sqrt((LINT t:A|M. (f t)\<^sup>2 * c\<^sup>2))"
    by (metis (no_types) set_integral_mult_left)
  then have "sqrt (LINT t:A|M. (f t)\<^sup>2) * c = sqrt((LINT t:A|M. (f t*c)\<^sup>2 ))"
    by (simp add: power_mult_distrib) 
  thus ?thesis 
    by (metis L2norm_def)
qed

lemma L2norm_empty [simp]: "L2norm M f {} = 0"
  unfolding L2norm_def by simp

lemma L2norm_neq: "L2norm M (\<lambda>t. - f t) A = L2norm M (\<lambda>t. f t) A"
  unfolding L2norm_def by fastforce

lemma L2norm_neq1: "L2norm M (-f) A = L2norm M (\<lambda>t. f t) A"
  unfolding L2norm_def by fastforce
 
lemma L2norm_triangle_ineq:
  fixes f g ::  "real \<Rightarrow> real"
  assumes "\<And>t. t \<in> A"
          "set_integrable M A f" 
          "set_integrable M A g"
          "set_integrable M A (\<lambda>t. (f t)\<^sup>2)" 
          "set_integrable M A (\<lambda>t. (g t)\<^sup>2)"
          "set_integrable M A (\<lambda>t. f t * g t)"
          "(LINT t:A|M. (g t)\<^sup>2) > 0"
  shows "L2norm M (\<lambda>t. f t + g t) A \<le> L2norm M f A + L2norm M g A"
proof -
  have "sqrt(LINT t:A|M. (f t + g t)\<^sup>2) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2)"
    using minkowski_integral_ineq assms by blast 
  thus ?thesis unfolding L2norm_def
    by blast
qed

lemma L2norm_triangle_ineq_nq:
  fixes f g ::  "real \<Rightarrow> real"
  assumes "\<And>t. t \<in> A"
          "set_integrable M A f" 
          "set_integrable M A g"
          "set_integrable M A (\<lambda>t. (f t)\<^sup>2)" 
          "set_integrable M A (\<lambda>t. (g t)\<^sup>2)"
          "set_integrable M A (\<lambda>t. f t * g t)"
          "(LINT t:A|M. (g t)\<^sup>2) > 0"
  shows "L2norm M (\<lambda>t. f t - g t) A \<le> L2norm M f A + L2norm M g A"
proof -
  have "sqrt(LINT t:A|M. (f t - g t)\<^sup>2) \<le> sqrt(LINT t:A|M. (f t)\<^sup>2) + sqrt(LINT t:A|M. (g t)\<^sup>2)"
    using assms minkowski_integral_ineq_ng mult_minus_right by blast
  thus ?thesis unfolding L2norm_def 
    using L2norm_neq by fastforce
qed

end