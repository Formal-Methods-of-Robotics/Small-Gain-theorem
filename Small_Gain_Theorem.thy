
(* Title:      Small-Gain Theorem
   Author:     Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk>
   Maintainer: Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk> 
*)

theory Small_Gain_Theorem
imports  
"~~/src/HOL/Probability/Analysis"   
"~~/src/HOL/Probability/Probability"
"~~/src/HOL/Library/Function_Algebras"
"~~/L2Norm_Integral"
begin

section \<open> Definitions of Signals\<close>

text \<open>Time Interval Definition\<close>

definition T :: "real set"
  where "T ={t.  (0\<le>t \<and> t<\<infinity>)}"
                                              
definition T\<^sub>\<tau> :: "real set"
  where "T\<^sub>\<tau> ={t. (\<forall>\<tau>\<in>T.  0\<le>t \<and> t\<le>\<tau> )}"

lemma T\<^sub>\<tau>_subset_T: "T\<^sub>\<tau> \<subseteq> T" 
  using T\<^sub>\<tau>_def T_def by auto

text \<open>Signal Range Definition\<close>

definition R :: "real set"
  where "R ={r.  (-\<infinity><r \<and> r<\<infinity>)}"

text \<open>Signal Definition\<close>

definition Signal ::"(real \<Rightarrow> real) \<Rightarrow> bool"
  where "Signal u = (\<forall>t\<in>T. \<exists>!x\<in>R.  x = u t \<and>  u:T\<rightarrow>R \<and> u t\<in> u ` T \<and> u piecewise_differentiable_on T 
                    \<and> continuous_on T u)" 

lemma signal_integration_bound:
fixes M
assumes "Signal u"
    and "set_integrable M T u"
  shows "(LINT  t:T|M. (u t)\<^sup>2) < \<infinity>"
using assms by simp

lemma sig1: "Signal u \<Longrightarrow> \<forall>t\<in>T. u t \<in> range (\<lambda>t\<in>T. u t)"
  by auto

lemma sig2: "Signal u \<Longrightarrow> \<forall>t\<in>T. u t \<in> R"
  using Signal_def by blast

lemma sig3: "Signal u \<Longrightarrow> range (\<lambda>t\<in>T. u t) \<subseteq> R"   
  unfolding Signal_def  by (simp add:R_def)

lemma sig4: "Signal u \<Longrightarrow>\<forall> A. range (\<lambda>t\<in>T. u t) = (\<lambda>t\<in>T. u t) ` A \<Longrightarrow> A\<subseteq>T "   
  using  Signal_def  by blast  

section \<open>Definitions of Signals Space\<close>

consts
 signal_prod :: " real  \<Rightarrow> 'a   \<Rightarrow> 'a "  (infixl "\<cdot>"  70)

text \<open>\<open>Domain Space Definition\<close>\<close> 

locale Domain_Space =
fixes  D :: "(real \<Rightarrow> real) set"
assumes non_empty_D [iff, intro?]: "D \<noteq> {}"
    and spaceD_mem [iff]: "range (\<lambda>t\<in>T. u t)\<subseteq>R \<Longrightarrow>\<lbrakk>range (\<lambda>t\<in>T. u t) = (\<lambda>t\<in>T. u t)`A \<Longrightarrow>A\<subseteq>T\<rbrakk>\<Longrightarrow>(\<lambda>t\<in>T. u t)\<in>D"
    and spaceD_add1[iff]: "u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow> u + s \<in> D"
    and spaceD_add2[simp]:"u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow> u + s = (\<lambda>t\<in>T. u t + s t)"
    and spaceD_add3 :     "u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow> u + s = s + u"
    and spaceD_add_assoc: "u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow> g\<in>D \<Longrightarrow> (u + s) + g = u + (s + g) "
    and spaceD_pointwise[simp]:"u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow>\<forall>t\<in>T. (u + s)t = u t + s t"
    and spaceD_sub[iff]:       "u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow> u - s \<in> D"
    and spaceD_mult1[iff]:     "u\<in>D \<Longrightarrow>a\<in>\<real>\<Longrightarrow> (a \<cdot> u) \<in>D"
    and spaceD_mult2:          "u\<in>D \<Longrightarrow>a\<in>\<real>\<Longrightarrow>\<forall>t\<in>T. (a \<cdot> u)t = a * u t"
    and spaceD_mult_distr1:    "u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow>a\<in>\<real>\<Longrightarrow> a \<cdot> (u + s) = a \<cdot> u + a \<cdot> s"
    and spaceD_mult_distr2:    "u\<in>D \<Longrightarrow> s\<in>D \<Longrightarrow>a\<in>\<real>\<Longrightarrow>\<forall>t\<in>T.  a \<cdot> (u + s)t = a * u t + a * s t"
    and spaceD_mult_distr3:    "u\<in>D \<Longrightarrow>a\<in>\<real>\<Longrightarrow>b\<in>\<real>\<Longrightarrow> (a + b) \<cdot> u  = a \<cdot> u + b \<cdot> u"
    and spaceD_mult_assoc:     "u\<in>D \<Longrightarrow>a\<in>\<real>\<Longrightarrow>b\<in>\<real>\<Longrightarrow> (a * b) \<cdot> u  = a \<cdot> (b \<cdot> u)"

text \<open>\<open>Range Space Definition\<close>\<close>
 
locale Range_Space =
fixes  G :: "(real \<Rightarrow> real) set"
assumes non_empty_G [iff, intro?]: "G \<noteq> {}"
    and spaceG_mem[iff]:  "range (\<lambda>t\<in>T. y t)\<subseteq>R \<Longrightarrow> \<lbrakk>range (\<lambda>t\<in>T. y t) = (\<lambda>t\<in>T. y t)`B \<Longrightarrow>B\<subseteq>T\<rbrakk> \<Longrightarrow> (\<lambda>t\<in>T. y t)\<in>G" 
    and spaceG_add1[iff]: "y\<in>G \<Longrightarrow> z\<in>G \<Longrightarrow> y + z \<in>G"
    and spaceG_add2[simp]:"y\<in>G \<Longrightarrow> z\<in>G \<Longrightarrow> y + z = (\<lambda>t\<in>T. y t + z t)"
    and spaceG_add3 :     "y\<in>G \<Longrightarrow> z\<in>G \<Longrightarrow> y + z = z + y"
    and spaceG_add_assoc: "y\<in>G \<Longrightarrow> z\<in>G \<Longrightarrow> j\<in>G \<Longrightarrow> (y + z) + j = y + (z + j) "
    and spaceG_pointwise[simp]:"y\<in>G \<Longrightarrow> z\<in>G \<Longrightarrow>\<forall>t\<in>T. (y + z)t = y t + z t"
    and spaceG_mult1[iff]:     "y\<in>G  \<Longrightarrow>a\<in>\<real>\<Longrightarrow> (a \<cdot> y) \<in>G"
    and spaceG_mult2 :         "y\<in>G  \<Longrightarrow>a\<in>\<real>\<Longrightarrow>\<forall>t\<in>T. (a \<cdot> y)t = a * y t"
    and spaceG_mult_distr1 :   "y\<in>G \<Longrightarrow> z\<in>G  \<Longrightarrow>a\<in>\<real>\<Longrightarrow> a \<cdot> (y + z) = a \<cdot> y + a \<cdot> z"
    and spaceG_mult_distr2 :   "y\<in>G \<Longrightarrow> z\<in>G  \<Longrightarrow>a\<in>\<real>\<Longrightarrow>\<forall>t\<in>T.  a \<cdot> (y + z)t = a * y t + a * z t"
    and spaceG_mult_distr3 :   "y\<in>G \<Longrightarrow>a\<in>\<real>\<Longrightarrow>b\<in>\<real>\<Longrightarrow> (a + b) \<cdot> y  = a \<cdot> y + b \<cdot> y"
    and spaceG_mult_assoc :    "y\<in>G  \<Longrightarrow>a\<in>\<real>\<Longrightarrow>b\<in>\<real>\<Longrightarrow> (a * b) \<cdot> y  = a \<cdot> (b \<cdot> y)"
      
text \<open>\<open>Operator Space Definition\<close>\<close> 

locale Operator_Space =
fixes  OP :: "((real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real)) set"
assumes  non_empty_OP [iff, intro?]: "OP \<noteq> {}"
    and  spaceG_mem [iff]:"Domain_Space D \<Longrightarrow> Range_Space G \<Longrightarrow> H\<in>OP"
    and  asm_op1 [iff] :  "H\<in>OP \<Longrightarrow>Domain_Space D\<Longrightarrow>Range_Space G\<Longrightarrow> H: D\<rightarrow>G "
    and  asm_op2 [iff] :  "H\<in>OP \<Longrightarrow>Domain_Space D\<Longrightarrow>Range_Space G\<Longrightarrow> H: G\<rightarrow>D "
    and  asm_op3 [iff] :  "H\<in>OP \<Longrightarrow>range H \<subseteq> T\<rightarrow>R"
    and  asm_op4 [iff] :  "H\<in>OP \<Longrightarrow>Domain_Space D\<Longrightarrow>Range_Space G\<Longrightarrow> H: D\<rightarrow>G \<Longrightarrow>range H = H`D \<Longrightarrow>D \<subseteq> T\<rightarrow>R "
    and  asm_op5 [iff] :  "H\<in>OP \<Longrightarrow>Domain_Space D\<Longrightarrow>Range_Space G\<Longrightarrow> H: G\<rightarrow>D \<Longrightarrow>range H = H`G \<Longrightarrow>G \<subseteq> T\<rightarrow>R "
    and  asm_op6 : "H\<in>OP \<Longrightarrow> Domain_Space D \<Longrightarrow> Range_Space G \<Longrightarrow> s\<in>D \<Longrightarrow> z\<in>G \<Longrightarrow> z= H(s)"

definition Signal_Y :: "(real \<Rightarrow> real) \<Rightarrow> ((real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> ((real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real) set \<Rightarrow> bool" 
  where  "Signal_Y y H e OP = (\<forall>a. \<exists>!b.  (a=e \<and> b=y \<and>Operator_Space OP \<and> H\<in>OP \<and> range y \<subseteq> R ) \<longrightarrow>   y = H e )"
    
(* signal truncation *)
definition trunc :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real set \<Rightarrow> bool"
  where "trunc u u\<^sub>\<tau> U U\<^sub>\<tau> = (Signal u \<and> u ` T = U \<and> (\<forall>\<tau>\<in>T. \<forall>t\<in>T. if t\<le>\<tau> then ((u t\<in>U \<longrightarrow> u t\<in>U\<^sub>\<tau>) \<and> u t = u\<^sub>\<tau> t) 
                           else ((u t\<in>U \<longrightarrow> 0\<in>U\<^sub>\<tau>) \<and> u\<^sub>\<tau> t=0 )))"

text \<open>\<open>Truncation Space Definition\<close>\<close>

locale TR_Space =
  fixes  TR :: "(real \<Rightarrow> real) set"
  assumes non_empty_TR [iff, intro?]: "TR \<noteq> {}"
      and spaceTR_mem [iff]: "trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> (\<lambda>t\<in>T\<^sub>\<tau>. u\<^sub>\<tau> t)\<in>TR"
      and spaceTR_1:      "trunc u u\<^sub>\<tau> U U\<^sub>\<tau>\<Longrightarrow> u\<^sub>\<tau>\<in>TR \<Longrightarrow> U\<^sub>\<tau> \<inter> U =  u\<^sub>\<tau> ` T\<^sub>\<tau>"  
      and spaceTR_2[iff]: "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>\<Longrightarrow>trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>\<Longrightarrow> e\<^sub>1\<^sub>\<tau>= u\<^sub>1\<^sub>\<tau> - (H\<^sub>2 e\<^sub>2\<^sub>\<tau>) 
                           \<Longrightarrow> e\<^sub>2\<^sub>\<tau>= u\<^sub>2\<^sub>\<tau> + (H\<^sub>1 e\<^sub>1\<^sub>\<tau>) \<Longrightarrow>u\<^sub>1\<^sub>\<tau>\<in>TR\<Longrightarrow>u\<^sub>2\<^sub>\<tau>\<in>TR\<Longrightarrow>e\<^sub>1\<^sub>\<tau>\<in>TR"
      and spaceTR_3[iff]: "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>\<Longrightarrow>trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>\<Longrightarrow> e\<^sub>1\<^sub>\<tau>= u\<^sub>1\<^sub>\<tau> - (H\<^sub>2 e\<^sub>2\<^sub>\<tau>) 
                           \<Longrightarrow> e\<^sub>2\<^sub>\<tau>= u\<^sub>2\<^sub>\<tau> + (H\<^sub>1 e\<^sub>1\<^sub>\<tau>) \<Longrightarrow>u\<^sub>1\<^sub>\<tau>\<in>TR\<Longrightarrow>u\<^sub>2\<^sub>\<tau>\<in>TR\<Longrightarrow>e\<^sub>2\<^sub>\<tau>\<in>TR"
      and spaceTR_4[iff]: "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>\<Longrightarrow>trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>\<Longrightarrow> e\<^sub>1\<^sub>\<tau>= u\<^sub>1\<^sub>\<tau> - (H\<^sub>2 e\<^sub>2\<^sub>\<tau>) \<Longrightarrow> e\<^sub>2\<^sub>\<tau>= u\<^sub>2\<^sub>\<tau> + (H\<^sub>1 e\<^sub>1\<^sub>\<tau>) 
                           \<Longrightarrow> Signal_Y y\<^sub>1\<^sub>\<tau> H\<^sub>1 e\<^sub>1\<^sub>\<tau> OP \<Longrightarrow>u\<^sub>1\<^sub>\<tau>\<in>TR\<Longrightarrow>u\<^sub>2\<^sub>\<tau>\<in>TR\<Longrightarrow>e\<^sub>1\<^sub>\<tau>\<in>TR\<Longrightarrow>  e\<^sub>2\<^sub>\<tau>\<in>TR \<Longrightarrow> y\<^sub>1\<^sub>\<tau>\<in>TR "
      and spaceTR_5[iff]: "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>\<Longrightarrow>trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>\<Longrightarrow> e\<^sub>1\<^sub>\<tau>= u\<^sub>1\<^sub>\<tau> - (H\<^sub>2 e\<^sub>2\<^sub>\<tau>) \<Longrightarrow> e\<^sub>2\<^sub>\<tau>= u\<^sub>2\<^sub>\<tau> + (H\<^sub>1 e\<^sub>1\<^sub>\<tau>) 
                           \<Longrightarrow> Signal_Y y\<^sub>2\<^sub>\<tau> H\<^sub>2 e\<^sub>2\<^sub>\<tau> OP 
                           \<Longrightarrow>u\<^sub>1\<^sub>\<tau>\<in>TR\<Longrightarrow>u\<^sub>2\<^sub>\<tau>\<in>TR\<Longrightarrow>e\<^sub>1\<^sub>\<tau>\<in>TR\<Longrightarrow>  e\<^sub>2\<^sub>\<tau>\<in>TR \<Longrightarrow> y\<^sub>2\<^sub>\<tau>\<in>TR "
      and spaceTR_6 :     "trunc u u\<^sub>\<tau> U U\<^sub>\<tau>\<Longrightarrow>Signal_Y y H e OP\<Longrightarrow> Signal_Y y\<^sub>\<tau> H e\<^sub>\<tau> OP\<Longrightarrow> e\<^sub>\<tau>\<in>TR \<Longrightarrow> y\<^sub>\<tau>\<in>TR 
                           \<Longrightarrow> y\<^sub>\<tau> ` T\<^sub>\<tau> \<subseteq> range y\<^sub>\<tau> \<inter> range y"

(* Some lemmas for truncation definition *)

lemma tr1:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> \<exists>t\<in>T.  u\<^sub>\<tau> t\<in>U\<^sub>\<tau> " 
  unfolding trunc_def using T_def by force

lemma tr1a:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> \<forall>t\<in>T\<^sub>\<tau>.  u\<^sub>\<tau> t\<in>U\<^sub>\<tau> " 
  unfolding trunc_def using T\<^sub>\<tau>_subset_T subset_eq by fastforce

lemma tr1b:" trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>\<forall>\<tau>\<in>T. \<forall>t\<in>T. t>\<tau> \<longrightarrow>  0\<in>U\<^sub>\<tau> " 
  unfolding trunc_def using T_def by force

lemma tr1c:" trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>\<forall>\<tau>\<in>T. \<forall>t\<in>T. t>\<tau> \<and> t\<notin>T\<^sub>\<tau> \<longrightarrow> 0\<in>U\<^sub>\<tau> " 
  unfolding trunc_def using T_def by fastforce

lemma tr1d:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>  u\<^sub>\<tau> ` T\<^sub>\<tau> \<subseteq> U\<^sub>\<tau>" 
  unfolding trunc_def using T\<^sub>\<tau>_subset_T by force

lemma tr1e:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> u\<^sub>\<tau> ` T\<^sub>\<tau>  \<subseteq> U" 
  unfolding trunc_def using T\<^sub>\<tau>_subset_T by force

lemma tr1f:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> u\<^sub>\<tau> ` T\<^sub>\<tau>  \<subseteq>  u ` T" 
  unfolding trunc_def using T\<^sub>\<tau>_subset_T image_iff image_subsetI subsetCE by fastforce

lemma tr1g:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> u ` T\<^sub>\<tau> =  u\<^sub>\<tau> ` T\<^sub>\<tau>" 
  unfolding trunc_def using T\<^sub>\<tau>_subset_T by force

lemma tr3:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>\<forall>\<tau>\<in>T. \<forall>t\<in>T. t>\<tau> \<longrightarrow>  u\<^sub>\<tau> t\<in>U\<^sub>\<tau> \<and> u\<^sub>\<tau> t=0 " 
  unfolding trunc_def by force

lemma tr6:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> \<forall>\<tau>\<in>T. \<forall>t\<in>T. t>\<tau> \<Longrightarrow> \<forall>t\<in>T\<^sub>\<tau>.  \<not>(u\<^sub>\<tau> ` T\<^sub>\<tau>  \<subseteq> U) " 
  using T\<^sub>\<tau>_subset_T by fast

lemma tr7:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> T = T\<^sub>\<tau> \<Longrightarrow> u ` T = u\<^sub>\<tau> ` T\<^sub>\<tau> " 
  using trunc_def by (metis tr1g)

lemma tr8:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> (\<lambda>t\<in>T\<^sub>\<tau>. u t) =  (\<lambda>t\<in>T\<^sub>\<tau>. u\<^sub>\<tau> t)  " 
  using trunc_def T\<^sub>\<tau>_def T\<^sub>\<tau>_subset_T by force

lemma tr9:"trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>  u\<^sub>\<tau> ` T\<^sub>\<tau>  \<subseteq>  U\<^sub>\<tau> \<inter> U  "  
  by (simp add: tr1d tr1e)

lemma tr10:" trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>\<forall>\<tau>\<in>T. \<forall>t\<in>T. t\<le>\<tau> \<longrightarrow>  u t\<in>U\<^sub>\<tau> "
  unfolding trunc_def by fastforce

lemma tr11:" trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>\<forall>\<tau>\<in>T. \<forall>t\<in>T. t\<le>\<tau> \<longrightarrow>  u\<^sub>\<tau> t\<in>U\<^sub>\<tau> "
  unfolding trunc_def by fastforce

lemma tr12:" trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>\<forall>\<tau>\<in>T. \<forall>t\<in>T. t\<le>\<tau> \<longrightarrow>  u\<^sub>\<tau> t  \<in>  U\<^sub>\<tau> \<inter> U "
  unfolding trunc_def by force

(*some lemmas for output signal y*)

lemma sig_Y1: "Signal_Y y H e OP \<Longrightarrow> (\<lambda>t\<in>T. y t) = H (\<lambda>t\<in>T. e t)"
  using Signal_Y_def by metis

lemma sig_Y3: "trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow> Signal_Y y\<^sub>\<tau> H e\<^sub>\<tau> OP\<Longrightarrow> (\<lambda>t\<in>T\<^sub>\<tau>. y\<^sub>\<tau> t) = H(\<lambda>t\<in>T\<^sub>\<tau>. e\<^sub>\<tau> t) "
  using Signal_Y_def by metis


definition Causality :: "(real \<Rightarrow> real)\<Rightarrow> (real \<Rightarrow> real)\<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) 
                         \<Rightarrow> real set \<Rightarrow> real set \<Rightarrow> ((real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> ((real \<Rightarrow> real) 
                         \<Rightarrow> real \<Rightarrow> real) set \<Rightarrow> (real \<Rightarrow> real) set \<Rightarrow> bool" 
  where "Causality u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> H OP TR = ((Operator_Space OP \<and> H\<in>OP \<and>  trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<and> TR_Space TR \<and> u\<^sub>\<tau>\<in>TR \<and> e\<^sub>\<tau>\<in>TR) 
                                           \<longrightarrow> H (\<lambda>t\<in>T\<^sub>\<tau>. e t) = H (\<lambda>t\<in>T\<^sub>\<tau>. e\<^sub>\<tau> t))"
  
lemma Caus1: "Operator_Space OP \<Longrightarrow>H\<in>OP \<Longrightarrow>TR_Space TR\<Longrightarrow>u\<^sub>\<tau>\<in>TR \<and> e\<^sub>\<tau>\<in>TR\<Longrightarrow>trunc u u\<^sub>\<tau> U U\<^sub>\<tau> \<Longrightarrow>Causality u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> H OP TR
             \<Longrightarrow> H (\<lambda>t\<in>T\<^sub>\<tau>. e t) = H (\<lambda>t\<in>T\<^sub>\<tau>. e\<^sub>\<tau> t)"   using Causality_def by blast
                                                       
lemma sig_Y_tr:"Signal_Y y H e OP\<Longrightarrow> Causality u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> H OP TR \<Longrightarrow> (\<lambda>t\<in>T\<^sub>\<tau>. y t) = H(\<lambda>t\<in>T\<^sub>\<tau>. e\<^sub>\<tau> t)"
  using Signal_Y_def by metis

lemma sig_Y_tr1:"Signal_Y y H e OP\<Longrightarrow> Causality u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> H OP TR \<Longrightarrow> (\<lambda>t\<in>T\<^sub>\<tau>. y\<^sub>\<tau> t) = H(\<lambda>t\<in>T\<^sub>\<tau>. e\<^sub>\<tau> t)"
  using Signal_Y_def by metis

definition Stability :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real)\<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real 
                        \<Rightarrow> ((real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real measure \<Rightarrow> ((real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real) set \<Rightarrow> (real \<Rightarrow> real) set \<Rightarrow> bool" 
  where "Stability u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> \<gamma> \<beta> H M OP TR = ((Causality u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> H OP TR) \<longrightarrow> (\<exists>a. \<exists>b. a\<in>T \<and> b\<in>T \<and> \<gamma>=a \<and> \<beta>=b 
                                                 \<and> ((L2norm M (\<lambda>t. (H e) t) T\<^sub>\<tau>) \<le> \<gamma> * (L2norm M (\<lambda>t. e\<^sub>\<tau> t) T\<^sub>\<tau>) + \<beta>)))"

lemma stb1: "Causality u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> H OP TR \<Longrightarrow> Stability u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> \<gamma> \<beta> H M OP TR \<Longrightarrow>(\<exists>\<gamma>. \<gamma>\<in>T) \<Longrightarrow>  (\<exists>\<beta>. \<beta>\<in>T) 
            \<Longrightarrow> (L2norm M (\<lambda>t. (H e) t) T\<^sub>\<tau> \<le> \<gamma> * (L2norm M (\<lambda>t. e\<^sub>\<tau> t) T\<^sub>\<tau>) + \<beta>)" using Stability_def  by blast

lemma stb2: "Signal_Y y H e OP\<Longrightarrow>Stability u u\<^sub>\<tau> e e\<^sub>\<tau> U U\<^sub>\<tau> \<gamma> \<beta> H M OP TR\<Longrightarrow>(\<exists>\<gamma>. \<gamma>\<in>T) \<Longrightarrow>  (\<exists>\<beta>. \<beta>\<in>T) 
            \<Longrightarrow> (L2norm M (\<lambda>t. y t) T\<^sub>\<tau> \<le> \<gamma> * (L2norm M (\<lambda>t. e\<^sub>\<tau> t) T\<^sub>\<tau>) + \<beta>)"
  using Stability_def Signal_Y_def by (metis (mono_tags, hide_lams) add_le_imp_le_right order_refl)


section \<open>\<open>Small-Gain Theorem Definitions\<close>\<close> 

text \<open>Closed feedback loop interconnection\<close>

lemma e1: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "Domain_Space D"
    and "Range_Space G"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> H\<^sub>1 e\<^sub>1\<in>G"
    and "e\<^sub>2 = u\<^sub>2 + (H\<^sub>1 e\<^sub>1)"
  shows "e\<^sub>1 = u\<^sub>1 - (H\<^sub>2 e\<^sub>2)"
  using assms Operator_Space.asm_op6 Operator_Space.spaceG_mem eq_iff_diff_eq_0 by fastforce

lemma e2: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "Domain_Space D"
    and "Range_Space G"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> H\<^sub>1 e\<^sub>1\<in>G"
    and "e\<^sub>1 = u\<^sub>1 - (H\<^sub>2 e\<^sub>2)"
  shows "e\<^sub>2 = u\<^sub>2 + (H\<^sub>1 e\<^sub>1)"
  using assms Operator_Space.asm_op6 Operator_Space.spaceG_mem eq_iff_diff_eq_0 by fastforce


lemma e1_1: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "Domain_Space D"
    and "Range_Space G"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G"
    and "e\<^sub>2 = u\<^sub>2 + y\<^sub>1"
  shows "e\<^sub>1 = u\<^sub>1 - y\<^sub>2"
  using assms by (metis Signal_Y_def)

lemma e2_2: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "Domain_Space D"
    and "Range_Space G"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G"
    and "e\<^sub>1 = u\<^sub>1 - y\<^sub>2"
  shows "e\<^sub>2 = u\<^sub>2 + y\<^sub>1"
  using assms by (metis Signal_Y_def)

lemma e1_11: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "Domain_Space D"
    and "Range_Space G"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and>  H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and>  H\<^sub>1 e\<^sub>1\<in>G"
    and "(e\<^sub>2 = u\<^sub>2 + y\<^sub>1) "
    and "(e\<^sub>2 = u\<^sub>2 + (H\<^sub>1 e\<^sub>1))"
  shows "(e\<^sub>1 = u\<^sub>1 - y\<^sub>2) \<longleftrightarrow> (e\<^sub>1 = u\<^sub>1 - (H\<^sub>2 e\<^sub>2))"
  using assms  by (metis (full_types) Signal_Y_def)

lemma e2_22: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "Domain_Space D"
    and "Range_Space G"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and>  H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and>  H\<^sub>1 e\<^sub>1\<in>G"
    and "e\<^sub>1 = u\<^sub>1 - y\<^sub>2"
    and "e\<^sub>1 = u\<^sub>1 - (H\<^sub>2 e\<^sub>2) "
  shows "(e\<^sub>2 = u\<^sub>2 + y\<^sub>1) \<longleftrightarrow> (e\<^sub>2 = u\<^sub>2 + (H\<^sub>1 e\<^sub>1))"
  using assms  by (metis (full_types) Signal_Y_def)


(* With truncation*)

lemma tr_e1: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>"
    and "trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "TR_Space TR"
    and "u\<^sub>1\<^sub>\<tau>\<in>TR \<and> u\<^sub>2\<^sub>\<tau>\<in>TR \<and> e\<^sub>1\<^sub>\<tau>\<in>TR \<and> e\<^sub>2\<^sub>\<tau>\<in>TR \<and> y\<^sub>1\<^sub>\<tau>\<in>TR \<and> y\<^sub>2\<^sub>\<tau>\<in>TR"
    and "Domain_Space D"
    and "Range_Space G"
    and "Causality u\<^sub>1 u\<^sub>1\<^sub>\<tau> e\<^sub>1 e\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> H\<^sub>1 OP TR"
    and "Causality u\<^sub>2 u\<^sub>2\<^sub>\<tau> e\<^sub>2 e\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau> H\<^sub>2 OP TR"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and>  H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and>  H\<^sub>1 e\<^sub>1\<in>G"
    and "(e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>1 e\<^sub>1)t))"
  shows "e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>2 e\<^sub>2)t)"
  using assms by (metis Signal_Y_def)

lemma tr_e2: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>"
    and "trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "TR_Space TR"
    and "u\<^sub>1\<^sub>\<tau>\<in>TR \<and> u\<^sub>2\<^sub>\<tau>\<in>TR \<and> e\<^sub>1\<^sub>\<tau>\<in>TR \<and> e\<^sub>2\<^sub>\<tau>\<in>TR \<and> y\<^sub>1\<^sub>\<tau>\<in>TR \<and> y\<^sub>2\<^sub>\<tau>\<in>TR"
    and "Domain_Space D"
    and "Range_Space G"
    and "Causality u\<^sub>1 u\<^sub>1\<^sub>\<tau> e\<^sub>1 e\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> H\<^sub>1 OP TR"
    and "Causality u\<^sub>2 u\<^sub>2\<^sub>\<tau> e\<^sub>2 e\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau> H\<^sub>2 OP TR"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and>  H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and>  H\<^sub>1 e\<^sub>1\<in>G"
    and "e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>2 e\<^sub>2)t)"
  shows "e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>1 e\<^sub>1)t)"
  using assms by (metis Signal_Y_def)


lemma tr_e1_11: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>"
    and "trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "TR_Space TR"
    and "u\<^sub>1\<^sub>\<tau>\<in>TR \<and> u\<^sub>2\<^sub>\<tau>\<in>TR \<and> e\<^sub>1\<^sub>\<tau>\<in>TR \<and> e\<^sub>2\<^sub>\<tau>\<in>TR \<and> y\<^sub>1\<^sub>\<tau>\<in>TR \<and> y\<^sub>2\<^sub>\<tau>\<in>TR"
    and "Domain_Space D"
    and "Range_Space G"
    and "Causality u\<^sub>1 u\<^sub>1\<^sub>\<tau> e\<^sub>1 e\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> H\<^sub>1 OP TR"
    and "Causality u\<^sub>2 u\<^sub>2\<^sub>\<tau> e\<^sub>2 e\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau> H\<^sub>2 OP TR"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and>  H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and>  H\<^sub>1 e\<^sub>1\<in>G"
    and "(e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t\<in>T\<^sub>\<tau>. y\<^sub>1 t)) "
    and "(e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>1 e\<^sub>1)t))"
  shows "(e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t\<in>T\<^sub>\<tau>. y\<^sub>2 t)) \<longleftrightarrow> (e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>2 e\<^sub>2)t))"
  using assms by (metis (full_types) sig_Y_tr1)

lemma tr_e2_22: 
assumes "Signal u\<^sub>1"
    and "Signal u\<^sub>2"
    and "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau>"
    and "trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>"
    and "Operator_Space OP"
    and "H\<^sub>1\<in>OP"
    and "H\<^sub>2\<in>OP"
    and "TR_Space TR"
    and "u\<^sub>1\<^sub>\<tau>\<in>TR \<and> u\<^sub>2\<^sub>\<tau>\<in>TR \<and> e\<^sub>1\<^sub>\<tau>\<in>TR \<and> e\<^sub>2\<^sub>\<tau>\<in>TR \<and> y\<^sub>1\<^sub>\<tau>\<in>TR \<and> y\<^sub>2\<^sub>\<tau>\<in>TR"
    and "Domain_Space D"
    and "Range_Space G"
    and "Causality u\<^sub>1 u\<^sub>1\<^sub>\<tau> e\<^sub>1 e\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> H\<^sub>1 OP TR"
    and "Causality u\<^sub>2 u\<^sub>2\<^sub>\<tau> e\<^sub>2 e\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau> H\<^sub>2 OP TR"
    and "Signal_Y y\<^sub>1 H\<^sub>1 e\<^sub>1 OP"
    and "Signal_Y y\<^sub>2 H\<^sub>2 e\<^sub>2 OP"
    and "u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and>  H\<^sub>2 e\<^sub>2\<in>D"
    and "u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and>  H\<^sub>1 e\<^sub>1\<in>G"
    and "e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t\<in>T\<^sub>\<tau>. y\<^sub>2 t)"
    and "e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>2 e\<^sub>2)t)"
  shows "(e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t\<in>T\<^sub>\<tau>. y\<^sub>1 t)) \<longleftrightarrow> (e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t\<in>T\<^sub>\<tau>. (H\<^sub>1 e\<^sub>1)t))"
  using assms by (metis sig_Y_tr1)

theorem Small_Gain_Theorem:
assumes "\<And>\<tau>. \<tau>\<in>T" and "\<And>t. t\<in>T\<^sub>\<tau>"   and "Signal u\<^sub>1 \<and> Signal u\<^sub>2"
    and "trunc u\<^sub>1 u\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> \<and> trunc u\<^sub>2 u\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau>"and "Operator_Space OP \<Longrightarrow>H\<^sub>1:D\<rightarrow>G \<and> H\<^sub>1\<in>OP \<and> H\<^sub>2:G\<rightarrow>D \<and>H\<^sub>2\<in>OP"
    and "Domain_Space D \<Longrightarrow> u\<^sub>1\<in>D \<and> e\<^sub>1\<in>D \<and> y\<^sub>2\<in>D \<and> H\<^sub>2 e\<^sub>2\<in>D \<and> u\<^sub>1\<^sub>\<tau>\<in>D \<and> e\<^sub>1\<^sub>\<tau>\<in>D \<and> y\<^sub>2\<^sub>\<tau>\<in>D"
    and "Range_Space G  \<Longrightarrow> u\<^sub>2\<in>G \<and> e\<^sub>2\<in>G \<and> y\<^sub>1\<in>G \<and> H\<^sub>1 e\<^sub>1\<in>G \<and> u\<^sub>2\<^sub>\<tau>\<in>G \<and> e\<^sub>2\<^sub>\<tau>\<in>G \<and> y\<^sub>1\<^sub>\<tau>\<in>G"
    and "Causality u\<^sub>1 u\<^sub>1\<^sub>\<tau> e\<^sub>1 e\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> H\<^sub>1 OP TR " and " Causality u\<^sub>2 u\<^sub>2\<^sub>\<tau> e\<^sub>2 e\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau> H\<^sub>2 OP TR"
    and "TR_Space TR \<Longrightarrow> u\<^sub>1\<^sub>\<tau>\<in>TR \<and> e\<^sub>1\<^sub>\<tau>\<in>TR \<and> y\<^sub>2\<^sub>\<tau>\<in>TR \<and> u\<^sub>2\<^sub>\<tau>\<in>TR \<and> e\<^sub>2\<^sub>\<tau>\<in>TR \<and> y\<^sub>1\<^sub>\<tau>\<in>TR"
    and "e\<^sub>1 = u\<^sub>1 - y\<^sub>2" and "e\<^sub>1 = u\<^sub>1 - (H\<^sub>2 e\<^sub>2)"and "e\<^sub>2 = u\<^sub>2 + y\<^sub>1" and "e\<^sub>2 = u\<^sub>2 + (H\<^sub>1 e\<^sub>1)"
    and "\<And>t. t\<in>T\<^sub>\<tau> \<Longrightarrow>e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t. y\<^sub>2 t)" and "\<And>t. t\<in>T\<^sub>\<tau> \<Longrightarrow>e\<^sub>1\<^sub>\<tau> = u\<^sub>1\<^sub>\<tau> - (\<lambda>t. (H\<^sub>2 e\<^sub>2)t)"
    and "\<And>t. t\<in>T\<^sub>\<tau> \<Longrightarrow>e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t. y\<^sub>1 t)" and "\<And>t. t\<in>T\<^sub>\<tau> \<Longrightarrow>e\<^sub>2\<^sub>\<tau> = u\<^sub>2\<^sub>\<tau> + (\<lambda>t. (H\<^sub>1 e\<^sub>1)t)"
    and "Stability u\<^sub>1 u\<^sub>1\<^sub>\<tau> e\<^sub>1 e\<^sub>1\<^sub>\<tau> U\<^sub>1 U\<^sub>1\<^sub>\<tau> \<gamma>\<^sub>1 \<beta>\<^sub>1 H\<^sub>1 M OP TR" and "Stability u\<^sub>2 u\<^sub>2\<^sub>\<tau> e\<^sub>2 e\<^sub>2\<^sub>\<tau> U\<^sub>2 U\<^sub>2\<^sub>\<tau> \<gamma>\<^sub>2 \<beta>\<^sub>2 H\<^sub>2 M OP TR"
    and "set_integrable M T\<^sub>\<tau> u\<^sub>1\<^sub>\<tau>" "set_integrable M T\<^sub>\<tau> u\<^sub>2\<^sub>\<tau>" "set_integrable M T\<^sub>\<tau> e\<^sub>1\<^sub>\<tau>" "set_integrable M T\<^sub>\<tau> e\<^sub>2\<^sub>\<tau>"
    and "set_integrable M T\<^sub>\<tau> y\<^sub>1\<^sub>\<tau>" "set_integrable M T\<^sub>\<tau> y\<^sub>2\<^sub>\<tau>" "set_integrable M T\<^sub>\<tau> (\<lambda>t. (H\<^sub>1 e\<^sub>1)t)"
    and "set_integrable M T\<^sub>\<tau> (\<lambda>t. (H\<^sub>2 e\<^sub>2)t)" and "set_integrable M T\<^sub>\<tau> (\<lambda>t. (u\<^sub>1\<^sub>\<tau> t)\<^sup>2)" 
    and "set_integrable M T\<^sub>\<tau> (\<lambda>t. ((H\<^sub>2 e\<^sub>2)t)\<^sup>2)"and "set_integrable M T\<^sub>\<tau> (\<lambda>t. u\<^sub>1\<^sub>\<tau> t * (H\<^sub>2 e\<^sub>2)t )"
    and "set_integrable M T\<^sub>\<tau> (\<lambda>t. (u\<^sub>2\<^sub>\<tau> t)\<^sup>2)" and "set_integrable M T\<^sub>\<tau> (\<lambda>t. ((H\<^sub>1 e\<^sub>1)t)\<^sup>2)"
    and "set_integrable M T\<^sub>\<tau> (\<lambda>t. u\<^sub>2\<^sub>\<tau> t *(H\<^sub>1 e\<^sub>1)t)"  and "set_integrable M T\<^sub>\<tau> (\<lambda>t. (e\<^sub>1\<^sub>\<tau> t)\<^sup>2)" 
    and "set_integrable M T\<^sub>\<tau> (\<lambda>t. (e\<^sub>2\<^sub>\<tau> t)\<^sup>2)"   and "set_integrable M T\<^sub>\<tau> (\<lambda>t. e\<^sub>1\<^sub>\<tau> t * e\<^sub>2\<^sub>\<tau> t )"
    and "(LINT t:T\<^sub>\<tau>|M. (( H\<^sub>2 e\<^sub>2 )t)\<^sup>2 )>0" and "(LINT t:T\<^sub>\<tau>|M. (( H\<^sub>1 e\<^sub>1 )t)\<^sup>2 )>0" 
    and "(LINT t:T\<^sub>\<tau>|M. (e\<^sub>2\<^sub>\<tau> t)\<^sup>2 )>0" and " \<gamma>\<^sub>1 * \<gamma>\<^sub>2 <1"
  shows "(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2 + \<gamma>\<^sub>2 * \<beta>\<^sub>1 )/(1 - \<gamma>\<^sub>1 * \<gamma>\<^sub>2)"
    and "(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>1 *(L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1 + \<gamma>\<^sub>1 * \<beta>\<^sub>2 )/(1 - \<gamma>\<^sub>1 * \<gamma>\<^sub>2)"
    and "(L2norm M (\<lambda>t. e\<^sub>1 t + e\<^sub>2 t) T\<^sub>\<tau>) \<le> (L2norm M e\<^sub>1 T\<^sub>\<tau>) + (L2norm M e\<^sub>2 T\<^sub>\<tau>)"
proof -
from assms have asm_e1_1:"(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) = (L2norm M (\<lambda>t. u\<^sub>1\<^sub>\<tau> t + - (H\<^sub>2 e\<^sub>2)t) T\<^sub>\<tau>)"
  by (metis minus_apply minus_real_def)

then have asm_e1_2:"(L2norm M (\<lambda>t. u\<^sub>1\<^sub>\<tau> t +  -( H\<^sub>2 e\<^sub>2 )t ) T\<^sub>\<tau>) \<le> (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (L2norm M (H\<^sub>2 e\<^sub>2) T\<^sub>\<tau>)"
  using assms L2norm_triangle_ineq_nq  by auto 
                                                
from asm_e1_1 asm_e1_2 have "(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) \<le> (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (L2norm M (H\<^sub>2 e\<^sub>2) T\<^sub>\<tau>)" 
  by presburger

note step_e1_1 =this

have "(L2norm M (\<lambda>t. (H\<^sub>2 e\<^sub>2) t) T\<^sub>\<tau> \<le> \<gamma>\<^sub>2 * (L2norm M (\<lambda>t. e\<^sub>2\<^sub>\<tau> t) T\<^sub>\<tau>) + \<beta>\<^sub>2)"
  using assms Stability_def by auto

from this step_e1_1 have "(L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (L2norm M (H\<^sub>2 e\<^sub>2) T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2))"
  by simp

from this step_e1_1 have e1:"(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2))"
  by force

note step_e1_2 =this

have e2_1:"(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) = (L2norm M (\<lambda>t. u\<^sub>2\<^sub>\<tau> t + (H\<^sub>1 e\<^sub>1)t) T\<^sub>\<tau>)"
  using assms by (metis plus_fun_apply)

then have e2_2:"(L2norm M (\<lambda>t. u\<^sub>2\<^sub>\<tau> t +  ( H\<^sub>1 e\<^sub>1 )t ) T\<^sub>\<tau>) \<le> (L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (L2norm M (H\<^sub>1 e\<^sub>1) T\<^sub>\<tau>)"
  using assms L2norm_triangle_ineq  by meson 

have "(L2norm M (\<lambda>t. (H\<^sub>1 e\<^sub>1) t) T\<^sub>\<tau> \<le> \<gamma>\<^sub>1 * (L2norm M (\<lambda>t. e\<^sub>1\<^sub>\<tau> t) T\<^sub>\<tau>) + \<beta>\<^sub>1)"
  using assms Stability_def by auto

from this e2_2 have e2_3:"(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (L2norm M (H\<^sub>1 e\<^sub>1) T\<^sub>\<tau>) \<le> (L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1)"
  by simp

from this e2_1 e2_2 have e2_4:"(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>)\<le> ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1))"
  by linarith
   
from this step_e1_2  have "((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2)) 
\<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1)) + \<beta>\<^sub>2))"
  using T\<^sub>\<tau>_def assms(1) assms(2) by fastforce

note step_e1_3 =this

then have asm_e1_3: "((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1)) + \<beta>\<^sub>2)) 
= ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 * \<beta>\<^sub>1 + \<beta>\<^sub>2)"
  by algebra

then have asm_e1_4:"((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 * \<beta>\<^sub>1 + \<beta>\<^sub>2) 
= \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2 + \<gamma>\<^sub>2 * \<beta>\<^sub>1 )"
  by linarith

then have "(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) \<le> \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2 + \<gamma>\<^sub>2 * \<beta>\<^sub>1 )"
  using step_e1_1 step_e1_2 step_e1_3 asm_e1_3  by linarith

then have "(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) - \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2 + \<gamma>\<^sub>2 * \<beta>\<^sub>1 )"
  by force

then have "(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>)*(1 - \<gamma>\<^sub>1 * \<gamma>\<^sub>2 )\<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2 + \<gamma>\<^sub>2 * \<beta>\<^sub>1 )"
  by (metis linordered_field_class.sign_simps(24) real_scaleR_def real_vector.scale_right_diff_distrib 
      semiring_normalization_rules(12))

with \<open>\<gamma>\<^sub>1 * \<gamma>\<^sub>2 <1\<close> this show "(L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>)\<le> ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>2 *(L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2 + \<gamma>\<^sub>2 * \<beta>\<^sub>1 )/(1 - \<gamma>\<^sub>1 * \<gamma>\<^sub>2 )"
  by (simp add: less_diff_eq pos_le_divide_eq)

note sig_e1 =this

(* For Signal e2 *)

from e2_4 e1 have e2_5:"((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1)) \<le> 
                        ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2)) + \<beta>\<^sub>1))"
  using T\<^sub>\<tau>_def assms(1) assms(2) by fastforce

then have "((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * ((L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>2)) + \<beta>\<^sub>1)) 
           = \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>)+((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1 + \<gamma>\<^sub>1 *\<beta>\<^sub>2))"
  by algebra

then have "(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) \<le> \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>)+((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1 + \<gamma>\<^sub>1 *\<beta>\<^sub>2 ))"
  using  e2_4 e2_5 by linarith

then have "(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) - \<gamma>\<^sub>1 * \<gamma>\<^sub>2 * (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1 + \<gamma>\<^sub>1 *\<beta>\<^sub>2 ))"
  by force

then have "(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>)*(1 - \<gamma>\<^sub>1 * \<gamma>\<^sub>2) \<le> ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + (\<gamma>\<^sub>1 * (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1 + \<gamma>\<^sub>1 *\<beta>\<^sub>2 ))"
  by (metis linordered_field_class.sign_simps(24) real_scaleR_def real_vector.scale_right_diff_distrib 
      semiring_normalization_rules(12))

with \<open>\<gamma>\<^sub>1 * \<gamma>\<^sub>2 <1\<close> this show "(L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) \<le> ((L2norm M u\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>) + \<gamma>\<^sub>1 * (L2norm M u\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + \<beta>\<^sub>1 + \<gamma>\<^sub>1 *\<beta>\<^sub>2 )/(1 - \<gamma>\<^sub>1 * \<gamma>\<^sub>2)"
  by (simp add: less_diff_eq pos_le_divide_eq)

note sig_e2 =this

from sig_e1 sig_e2 have "(L2norm M (\<lambda>t. e\<^sub>1\<^sub>\<tau> t + e\<^sub>2\<^sub>\<tau> t) T\<^sub>\<tau>) \<le> (L2norm M e\<^sub>1\<^sub>\<tau> T\<^sub>\<tau>) + (L2norm M e\<^sub>2\<^sub>\<tau> T\<^sub>\<tau>)"
  using assms L2norm_triangle_ineq by meson

then show "(L2norm M (\<lambda>t. e\<^sub>1 t + e\<^sub>2 t) T\<^sub>\<tau>) \<le> (L2norm M e\<^sub>1 T\<^sub>\<tau>) + (L2norm M e\<^sub>2 T\<^sub>\<tau>)" 
  using assms L2norm_triangle_ineq by (metis T_def diff_add_cancel le_add_same_cancel2 mem_Collect_eq)

qed

end
