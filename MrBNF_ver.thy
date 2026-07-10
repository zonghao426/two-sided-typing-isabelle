theory MrBNF_ver
  imports Binders.MRBNF_Recursor "Case_Studies.FixedCountableVars" "HOL-Library.FSet"
begin

section \<open>Types and Terms\<close>

datatype "type" = 
    Nat
  | Prod "type" "type"
  | To "type" "type"
  | OnlyTo "type" "type"
  | Ok

typedef 'a :: infinite dpair = "{(x::'a,y). x \<noteq> y}"
  unfolding mem_Collect_eq split_beta
  by (metis (full_types) arb_element finite.intros(1) finite_insert fst_conv insertI1 snd_conv)

setup_lifting type_definition_dpair

lift_definition dfst :: "'a :: infinite dpair \<Rightarrow> 'a" is fst .
lift_definition dsnd :: "'a :: infinite dpair \<Rightarrow> 'a" is snd .
lift_definition dmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a :: infinite dpair \<Rightarrow> 'a :: infinite dpair" is
  "\<lambda>f (x, y). if bij f then (f x, f y) else (x, y)"
  by (auto split: if_splits simp: bij_implies_inject)
lift_definition dset :: "'a :: infinite dpair \<Rightarrow> 'a set" is "\<lambda>(a,b). {a, b}" .

mrbnf "'a :: var dpair"
  map: dmap
  sets: bound: dset
  bd: natLeq
  subgoal
    by (rule ext, transfer) auto
  subgoal
    by (rule ext, transfer) auto
  subgoal
    by (transfer) auto
  subgoal
    by (rule ext, transfer) auto
  subgoal
    by (rule infinite_regular_card_order_natLeq)
  subgoal
    by transfer (auto simp flip: finite_iff_ordLess_natLeq)
  subgoal
    by blast
  subgoal
    unfolding UNIV_I[THEN eqTrueI] simp_thms
    by transfer auto
  done

binder_datatype (FVars: 'var) "term" = 
  Zero
  | Succ "'var term"
  | Pred "'var term"
  | If "'var term" "'var term" "'var term"
  | Var 'var
  | App "'var term" "'var term"
  | Fix f::'var x::'var M::"'var term" binds f x in M
  | Pair "'var term" "'var term"
  | Let "(xy::'var) dpair" M::"'var term" N::"'var term" binds xy in N
  for subst: subst

lemma finite_FVars[simp]: "finite (FVars M)"
  apply(induction M)
          apply(auto)
  done

definition usubst ("_[_ <- _]" [1000, 49, 49] 1000) where
  "usubst t u x = subst (Var(x := u)) t"

lemma SSupp_term_fun_upd: "SSupp Var (Var(x :: 'var :: var := u)) \<subseteq> {x}"
  by (auto simp: SSupp_def)

lemma IImsupp_term_fun_upd: "IImsupp Var FVars (Var(x :: 'var :: var := u)) \<subseteq> {x} \<union> FVars u"
  by (auto simp: IImsupp_def SSupp_def)

lemma usubst_simps[simp]:
  "usubst Zero u y = Zero"
  "usubst (Succ t) u y = Succ (usubst t u y)"
  "usubst (Pred t) u y = Pred (usubst t u y)"
  "usubst (If t1 t2 t3) u y = If (usubst t1 u y) (usubst t2 u y) (usubst t3 u y)"
  "usubst (Var x) u y = (if x = y then u else Var x)"
  "usubst (App t1 t2) u y = App (usubst t1 u y) (usubst t2 u y)"
  "f \<noteq> y \<Longrightarrow> f \<notin> FVars u \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> FVars u \<Longrightarrow>
   usubst (Fix f x t) u y = Fix f x (usubst t u y)"
  "usubst (Pair t1 t2) u y = Pair (usubst t1 u y) (usubst t2 u y)"
  "y \<notin> dset xy \<Longrightarrow> dset xy \<inter> FVars u = {} \<Longrightarrow> dset xy \<inter> FVars t1 = {} \<Longrightarrow>
  usubst (term.Let xy t1 t2) u y = term.Let xy (usubst t1 u y) (usubst t2 u y)"
  unfolding usubst_def using IImsupp_term_fun_upd SSupp_term_fun_upd
  by (subst term.subst; fastforce)+

inductive num :: "'var::var term \<Rightarrow> bool" where
  "num Zero"
| "num n \<Longrightarrow> num (Succ n)"

declare [[inductive_internals]]

inductive val :: "'var::var term \<Rightarrow> bool" where
  "val (Var x)"
| "num n \<Longrightarrow> val n"
| "val V \<Longrightarrow> val W \<Longrightarrow> val (Pair V W)"
| "val (Fix f x M)"

section \<open>Beta Reduction\<close>

inductive beta :: "'var::var term \<Rightarrow> 'var::var term \<Rightarrow> bool"  (infix "\<rightarrow>" 70) where
  OrdApp2: "N \<rightarrow> N' \<Longrightarrow> App (Fix f x M) N \<rightarrow> App (Fix f x M) N'"
| OrdApp1: "M \<rightarrow> M' \<Longrightarrow> App M N \<rightarrow> App M' N"
| OrdSucc: "M \<rightarrow> M' \<Longrightarrow> Succ M \<rightarrow> Succ M'"
| OrdPred: "M \<rightarrow> M' \<Longrightarrow> Pred M \<rightarrow> Pred M'"
| OrdPair1: "M \<rightarrow> M' \<Longrightarrow> Pair M N \<rightarrow> Pair M' N"
| OrdPair2: "val V \<Longrightarrow> N \<rightarrow> N' \<Longrightarrow> Pair V N \<rightarrow> Pair V N'"
| OrdLet: "M \<rightarrow> M' \<Longrightarrow> Let xy M N \<rightarrow> Let xy M' N"
| OrdIf: "M \<rightarrow> M' \<Longrightarrow> If M N P \<rightarrow> If M' N P"
| Ifz : "If Zero N P \<rightarrow> N"
| Ifs : "num n \<Longrightarrow> If (Succ n) N P \<rightarrow> P"
| Let : "val V \<Longrightarrow> val W \<Longrightarrow> dset xy \<inter> FVars V = {} \<Longrightarrow> Let xy (Pair V W) M \<rightarrow> M[V <- dfst xy][W <- dsnd xy]"
| PredZ: "Pred Zero \<rightarrow> Zero"
| PredS: "num n \<Longrightarrow> Pred (Succ n) \<rightarrow> n"
| FixBeta: "val V \<Longrightarrow> f \<notin> FVars V \<Longrightarrow> App (Fix f x M) V \<rightarrow> M[V <- x][Fix f x M <- f]"
text \<open>NB: the freshness side conditions on @{text Let} and @{text FixBeta} are ESSENTIAL. The paper's
  (Fix\<beta>) rule uses simultaneous substitution @{text "M[V/x, fix f(x).M/f]"} under the implicit
  alpha-convention that the bound names are fresh for @{text V}. The sequential
  @{text "M[V <- x][Fix f x M <- f]"} equals it only when @{text "f \<notin> FVars V"}: otherwise the second
  substitution captures the @{text f}-occurrences inside the inserted @{text V}-copies. Without the
  side condition the relation is provably NON-deterministic (e.g. @{text "App (Fix f x (Var x)) (Pair (Var f) Zero)"}
  reduces both to @{text "Pair (Fix f x (Var x)) Zero"} and, via the alpha-equal representative
  @{text "Fix g x (Var x)"}, to @{text "Pair (Var f) Zero"}), and the binder_inductive refreshability
  obligation is false. Same for the @{text dsnd}-capture in @{text Let}. The side conditions do not
  restrict the relation up to alpha: binders can always be renamed to satisfy them.\<close>

inductive betas :: "'var::var term \<Rightarrow> nat \<Rightarrow> 'var::var term \<Rightarrow> bool"  ("_ \<rightarrow>[_] _" [70, 0, 70] 70) where
  refl: "M \<rightarrow>[0] M"
| step: "\<lbrakk> M \<rightarrow> N; N \<rightarrow>[n] P \<rbrakk> \<Longrightarrow> M \<rightarrow>[Suc n] P"

definition beta_star :: "'var::var term \<Rightarrow> 'var::var term \<Rightarrow> bool" (infix "\<rightarrow>*" 70) where
  "M \<rightarrow>* N = (\<exists>n. M \<rightarrow>[n] N)"

coinductive diverge :: "'var::var term \<Rightarrow> bool" ("_ \<Up>" 80) where
  "M \<rightarrow> N \<Longrightarrow> N \<Up> \<Longrightarrow> M \<Up>"

definition normal :: "'var::var term \<Rightarrow> bool" where
  "normal N \<equiv> (\<not>(\<exists>N'. N \<rightarrow> N'))"

definition normalizes :: "'var::var term \<Rightarrow> bool" where
  "normalizes M \<equiv> \<exists>N. normal N \<and> M \<rightarrow>* N"

definition "is_Fix V = (\<exists>f x Q. V = Fix f x Q)"
definition "is_Pair V = (\<exists>V1 V2. V = Pair V1 V2)"

inductive stuckEx :: "'var::var term \<Rightarrow> bool" where
  "val V \<Longrightarrow> \<not> num V \<Longrightarrow> stuckEx (Succ V)"
| "val V \<Longrightarrow> \<not> num V \<Longrightarrow> stuckEx (If V N P)"
| "val V \<Longrightarrow> \<not> is_Fix V \<Longrightarrow> stuckEx (App V M)"
| "val V \<Longrightarrow> \<not> is_Pair V \<Longrightarrow> stuckEx (Let xy V M)"
| "val V \<Longrightarrow> \<not> num V \<Longrightarrow> stuckEx (Pred V)"
text \<open>The @{text Pred} rule was missing in the original formalization, although the paper's
  Def.\ B.1 lists \<open>pred V\<close> with \<open>V \<notin> NatV\<close> among the stuck expressions. Without it
  \<open>Pred (Fix f x M)\<close> is normal but neither a value nor stuck, so the progress lemma
  @{text val_stuck_step} is false. It is appended last to keep the numbering of
  @{text "stuckEx.intros(1-4)"} used elsewhere.\<close>

lemma normals_normalizes: "normal N \<Longrightarrow> normalizes N"
  by(auto simp add: normalizes_def beta_star_def intro: betas.refl[of N])

lemma nums_are_normal: "num V \<Longrightarrow> normal V"
  apply(induction rule:num.induct)
   apply(auto elim:beta.cases simp add:normal_def)
  done

lemma vals_are_normal: "val V \<Longrightarrow> normal V"
  apply(induction rule:val.induct)
  apply(auto elim:nums_are_normal)
  apply(auto elim:beta.cases simp add:normal_def)
  done

lemma num_permute:
  "num n \<Longrightarrow> bij (\<sigma>::'a::var\<Rightarrow>'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> num (permute_term \<sigma> n)"
  by (induct rule: num.induct) (auto intro: num.intros)

binder_inductive (no_auto_equiv) val
  subgoal premises prems for R B \<sigma> x \<comment> \<open>equivariance\<close>
    using prems(3)
    apply (elim disjE exE)
    subgoal by (auto simp: prems(1,2))
    subgoal by (auto simp: prems(1,2) num_permute)
    subgoal by (auto simp: prems(1,2) term.permute_comp supp_inv_bound term.permute_id)
    subgoal for f xa M
      apply (intro disjI2)
      apply (elim conjE)
      apply (rule exI[of _ "\<sigma> f"], rule exI[of _ "\<sigma> xa"], rule exI[of _ "permute_term \<sigma> M"])
      apply (simp add: prems(1,2))
      done
    done
  subgoal premises prems for R B x \<comment> \<open>refreshability\<close>
    apply (rule exI[of _ B], rule conjI)
    subgoal using prems(3) by (elim disjE exE) auto
    apply (rule prems(3))
    done
  done

thm val.strong_induct

lemma subst_comp:
  assumes "|SSupp Var f| <o |UNIV :: 'var set|" "|SSupp Var g| <o |UNIV :: 'var set|"
  shows "subst f (subst g t) = subst (subst f o g) (t :: 'var :: var term)"
  unfolding term.Sb_comp[OF assms(2,1), symmetric] o_apply ..

text \<open>General commutation of permutation with unary substitution (needed for @{text beta} equivariance).
  Proved via the Sb route (@{thm term.map_is_Sb}), avoiding induction and the Let-distribution side
  condition of @{thm usubst_simps}. NB the @{text "(t::'a term)"} annotation is essential: without it
  @{text \<sigma>}'s type is inferred disconnected from @{text bs}, and @{text "term.permute[OF bs]"} fails to unify.\<close>
lemma permute_usubst:
  assumes bs: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a::var set|"
  shows "permute_term \<sigma> ((t::'a term)[s <- y]) = (permute_term \<sigma> t)[(permute_term \<sigma> s) <- \<sigma> y]"
proof -
  have permSb: "permute_term \<sigma> = subst (Var \<circ> \<sigma>)"
    using term.vvsubst_permute[OF bs] term.map_is_Sb[OF bs(2)] by metis
  have b\<sigma>: "|SSupp Var (Var \<circ> \<sigma>) :: 'a set| <o |UNIV::'a set|"
  proof -
    have "SSupp Var (Var \<circ> \<sigma>) = supp \<sigma>" by (auto simp: SSupp_def supp_def)
    then show ?thesis using bs(2) by simp
  qed
  have b1: "\<And>x u::'a term. |SSupp Var (Var(x := u)) :: 'a set| <o |UNIV::'a set|"
    by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_term_fun_upd]])
       (auto intro!: finite_ordLess_infinite2)
  have fun_eq: "subst (Var \<circ> \<sigma>) \<circ> Var(y := s) = subst (Var (\<sigma> y := subst (Var \<circ> \<sigma>) s)) \<circ> (Var \<circ> \<sigma>)"
  proof (rule ext)
    fix z show "(subst (Var \<circ> \<sigma>) \<circ> Var(y := s)) z = (subst (Var (\<sigma> y := subst (Var \<circ> \<sigma>) s)) \<circ> (Var \<circ> \<sigma>)) z"
      using bs by (cases "z = y") (auto simp: term.Sb_Inj bij_implies_inject)
  qed
  show ?thesis
    unfolding usubst_def permSb
    apply (subst subst_comp[OF b\<sigma> b1])
    apply (subst subst_comp[OF b1 b\<sigma>])
    unfolding fun_eq ..
qed

lemma finite_dset: "finite (dset (xy :: 'a::var dpair))"
  by transfer auto

lemma permute_term_inv:
  assumes s: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
  shows "permute_term (inv \<sigma>) (permute_term \<sigma> (V::'a::var term)) = V"
proof -
  have "inv \<sigma> \<circ> \<sigma> = id" using bij_is_inj[OF s(1)] by (simp add: inj_iff)
  then show ?thesis
    by (simp add: term.permute_comp[OF s(1,2) bij_imp_bij_inv[OF s(1)] supp_inv_bound[OF s(1,2)]] term.permute_id)
qed

lemma num_permute_iff:
  "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> num (permute_term \<sigma> (V::'a::var term)) = num V"
  by (metis num_permute permute_term_inv supp_inv_bound bij_imp_bij_inv)

lemma val_permute_iff:
  "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> val (permute_term \<sigma> (V::'a::var term)) = val V"
  by (metis val.equiv permute_term_inv supp_inv_bound bij_imp_bij_inv)

lemma is_Fix_permute:
  "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> is_Fix (permute_term \<sigma> (V::'a::var term)) = is_Fix V"
  unfolding is_Fix_def
  by (metis permute_term_inv term.permute(7) bij_imp_bij_inv supp_inv_bound)

lemma is_Pair_permute:
  "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> is_Pair (permute_term \<sigma> (V::'a::var term)) = is_Pair V"
  unfolding is_Pair_def
  by (metis permute_term_inv term.permute(8) bij_imp_bij_inv supp_inv_bound)

lemma stuckEx_equiv_ob:
  fixes \<sigma> :: "'a::var \<Rightarrow> 'a" and x :: "'a term"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
    and "(\<exists>V. B = {} \<and> x = Succ V \<and> val V \<and> \<not> num V) \<or>
         (\<exists>V N P. B = {} \<and> x = term.If V N P \<and> val V \<and> \<not> num V) \<or>
         (\<exists>V M. B = {} \<and> x = App V M \<and> val V \<and> \<not> is_Fix V) \<or>
         (\<exists>V xy M. B = dset xy \<and> x = term.Let xy V M \<and> val V \<and> \<not> is_Pair V) \<or>
         (\<exists>V. B = {} \<and> x = Pred V \<and> val V \<and> \<not> num V)"
  shows "(\<exists>V. \<sigma> ` B = {} \<and> permute_term \<sigma> x = Succ V \<and> val V \<and> \<not> num V) \<or>
         (\<exists>V N P. \<sigma> ` B = {} \<and> permute_term \<sigma> x = term.If V N P \<and> val V \<and> \<not> num V) \<or>
         (\<exists>V M. \<sigma> ` B = {} \<and> permute_term \<sigma> x = App V M \<and> val V \<and> \<not> is_Fix V) \<or>
         (\<exists>V xy M. \<sigma> ` B = dset xy \<and> permute_term \<sigma> x = term.Let xy V M \<and> val V \<and> \<not> is_Pair V) \<or>
         (\<exists>V. \<sigma> ` B = {} \<and> permute_term \<sigma> x = Pred V \<and> val V \<and> \<not> num V)"
  using assms(3)
  apply (elim disjE exE)
  subgoal by (auto simp: assms(1,2) num_permute_iff val_permute_iff is_Fix_permute is_Pair_permute)
  subgoal by (auto simp: assms(1,2) num_permute_iff val_permute_iff is_Fix_permute is_Pair_permute)
  subgoal by (auto simp: assms(1,2) num_permute_iff val_permute_iff is_Fix_permute is_Pair_permute)
  subgoal for V xy M
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (elim conjE)
    apply (rule exI[of _ "permute_term \<sigma> V"], rule exI[of _ "dmap \<sigma> xy"], rule exI[of _ "permute_term \<sigma> M"])
    apply (simp add: assms(1,2) dpair.set_map val_permute_iff is_Pair_permute)
    done
  subgoal by (auto simp: assms(1,2) num_permute_iff val_permute_iff is_Fix_permute is_Pair_permute)
  done

lemma stuckEx_refresh_ob:
  fixes x :: "'a::var term"
  assumes "(\<exists>V. B = {} \<and> x = Succ V \<and> val V \<and> \<not> num V) \<or>
           (\<exists>V N P. B = {} \<and> x = term.If V N P \<and> val V \<and> \<not> num V) \<or>
           (\<exists>V M. B = {} \<and> x = App V M \<and> val V \<and> \<not> is_Fix V) \<or>
           (\<exists>V xy M. B = dset xy \<and> x = term.Let xy V M \<and> val V \<and> \<not> is_Pair V) \<or>
           (\<exists>V. B = {} \<and> x = Pred V \<and> val V \<and> \<not> num V)"
  shows "\<exists>B'. B' \<inter> FVars x = {} \<and>
         ((\<exists>V. B' = {} \<and> x = Succ V \<and> val V \<and> \<not> num V) \<or>
          (\<exists>V N P. B' = {} \<and> x = term.If V N P \<and> val V \<and> \<not> num V) \<or>
          (\<exists>V M. B' = {} \<and> x = App V M \<and> val V \<and> \<not> is_Fix V) \<or>
          (\<exists>V xy M. B' = dset xy \<and> x = term.Let xy V M \<and> val V \<and> \<not> is_Pair V) \<or>
          (\<exists>V. B' = {} \<and> x = Pred V \<and> val V \<and> \<not> num V))"
  using assms
proof (elim disjE exE)
  fix V assume "B = {} \<and> x = Succ V \<and> val V \<and> \<not> num V"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V N P assume "B = {} \<and> x = term.If V N P \<and> val V \<and> \<not> num V"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V M assume "B = {} \<and> x = App V M \<and> val V \<and> \<not> is_Fix V"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V xy M assume H: "B = dset xy \<and> x = term.Let xy V M \<and> val V \<and> \<not> is_Pair V"
  then have hx: "x = term.Let xy V M" and hv: "val V" and hp: "\<not> is_Pair V" by auto
  have b1: "|dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|FVars V \<union> FVars M \<union> dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
  obtain \<rho> where r: "bij \<rho>" "|supp \<rho>| <o |UNIV::'a set|"
      "\<rho> ` dset xy \<inter> (FVars V \<union> FVars M \<union> dset xy) = {}"
      "id_on (FVars M - dset xy) \<rho>" "\<rho> \<circ> \<rho> = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M - dset xy"] by auto
  have eq: "term.Let xy V M = term.Let (dmap \<rho> xy) V (permute_term \<rho> M)"
    using r by (auto intro!: exI[of _ \<rho>])
  have disj: "dset (dmap \<rho> xy) \<inter> FVars x = {}"
    using r(3) unfolding hx term.set(9) dpair.set_map[OF r(1,2)] by blast
  show ?thesis
    apply (rule exI[of _ "dset (dmap \<rho> xy)"], rule conjI[OF disj])
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (rule exI[of _ V], rule exI[of _ "dmap \<rho> xy"], rule exI[of _ "permute_term \<rho> M"])
    using eq hv hp hx by auto
next
  fix V assume "B = {} \<and> x = Pred V \<and> val V \<and> \<not> num V"
  then show ?thesis by (intro exI[of _ "{}"]) auto
qed

binder_inductive (no_auto_equiv) stuckEx
  subgoal premises prems for R B \<sigma> x by (rule stuckEx_equiv_ob[OF prems(1,2,3)])
  subgoal premises prems for R B x by (rule stuckEx_refresh_ob[OF prems(3)])
  done

section \<open>Basic Lemmas\<close>

lemma term_strong_induct: "\<forall>\<rho>. |K \<rho> :: 'a ::var set| <o |UNIV :: 'a set| \<Longrightarrow>
(\<And>\<rho>. P Zero \<rho>) \<Longrightarrow>
(\<And>x \<rho>. \<forall>\<rho>. P x \<rho> \<Longrightarrow> P (Succ x) \<rho>) \<Longrightarrow>
(\<And>x \<rho>. \<forall>\<rho>. P x \<rho> \<Longrightarrow> P (Pred x) \<rho>) \<Longrightarrow>
(\<And>x1 x2 x3 \<rho>. \<forall>\<rho>. P x1 \<rho> \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> \<forall>\<rho>. P x3 \<rho> \<Longrightarrow> P (term.If x1 x2 x3) \<rho>) \<Longrightarrow>
(\<And>x \<rho>. P (Var x) \<rho>) \<Longrightarrow>
(\<And>x1 x2 \<rho>. \<forall>\<rho>. P x1 \<rho> \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> P (App x1 x2) \<rho>) \<Longrightarrow>
(\<And>x1 x2 x3 \<rho>. {x1, x2} \<inter> K \<rho> = {} \<Longrightarrow> \<forall>\<rho>. P x3 \<rho> \<Longrightarrow> P (Fix x1 x2 x3) \<rho>) \<Longrightarrow>
(\<And>x1 x2 \<rho>. \<forall>\<rho>. P x1 \<rho> \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> P (term.Pair x1 x2) \<rho>) \<Longrightarrow>
(\<And>x1 x2 x3 \<rho>. dset x1 \<inter> K \<rho> = {} \<Longrightarrow> \<forall>\<rho>. P x2 \<rho> \<Longrightarrow> \<forall>\<rho>. P x3 \<rho> \<Longrightarrow> P (term.Let x1 x2 x3) \<rho>) \<Longrightarrow> \<forall>\<rho>. P t \<rho>"
  by (rule term.strong_induct) auto

lemma premute_term_usubst: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a ::var set| \<Longrightarrow> id_on (FVars M - {x::'a}) \<sigma> \<Longrightarrow>
  (permute_term \<sigma> M)[V <- \<sigma> x] = M[V <- x]"
  apply (binder_induction M avoiding: M V x "supp \<sigma>" rule: term_strong_induct)
           apply (auto simp: Un_Diff id_on_Un bij_implies_inject)
  apply (smt (verit, best) Diff_iff Diff_insert2 Diff_insert_absorb bij_id_imsupp
      id_on_def in_imsupp not_in_imsupp_same not_in_supp_alt usubst_simps(7))
  apply (smt (verit, del_insts) Diff_iff Diff_insert2 Diff_triv Int_Un_emptyI1 Int_commute
      Int_emptyD Int_image_imsupp One_nat_def Sup_UNIV Sup_UNIV bij_imsupp_supp_ne
      disjoint_iff_not_equal dmap_def dmap_def dpair.map_id0 dpair.rel_Grp dpair.set_map
      dset_def fun.rel_eq fun.rel_eq id_on_def in_imsupp not_in_imsupp_same
      not_in_supp_alt set_diff_eq term.FVars_permute term.inject(8) term.map(9)
      term.permute(9) term.vvsubst_permute usubst_simps(9))
  done

lemma fresh_usubst[simp]: "x \<notin> FVars t \<Longrightarrow> x \<notin> FVars s \<Longrightarrow> x \<notin> FVars (t[s <- y])"
  by (binder_induction t avoiding: t s y rule: term_strong_induct)
    (auto simp: Int_Un_distrib)

lemma subst_idle[simp]: "y \<notin> FVars t \<Longrightarrow> t[s <- y] = t"
  by (binder_induction t avoiding: t s y rule: term_strong_induct) (auto simp: Int_Un_distrib)

lemma FVars_usubst: "FVars M[N <- z] = FVars M - {z} \<union> (if z \<in> FVars M then FVars N else {})"
  unfolding usubst_def
  by (auto simp: term.Vrs_Sb split: if_splits)

lemma usubst_usubst: "y1 \<noteq> y2 \<Longrightarrow> y1 \<notin> FVars s2 \<Longrightarrow> t[s1 <- y1][s2 <- y2] = t[s2 <- y2][s1[s2 <- y2] <- y1]"
  apply (binder_induction t avoiding: t y1 y2 s1 s2 rule: term_strong_induct)
          apply (auto simp: Int_Un_distrib FVars_usubst split: if_splits)
  apply (subst (1 2) usubst_simps; auto simp: FVars_usubst split: if_splits)
  done

lemma dsel_dset[simp]: "dfst xy \<in> dset xy" "dsnd xy \<in> dset xy"
  by (transfer; auto)+

lemma premute_term_usubst2: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a ::var set| \<Longrightarrow> id_on (FVars M - {x::'a, y}) \<sigma> \<Longrightarrow> {y, \<sigma> y} \<inter> FVars V = {} \<Longrightarrow>
  (permute_term \<sigma> M)[V <- \<sigma> x][W <- \<sigma> y] = M[V <- x][W <- y]"
  apply (binder_induction M avoiding: M V W x y "supp \<sigma>" rule: term_strong_induct)
           apply (auto simp: Un_Diff id_on_Un bij_implies_inject)
  apply (smt (verit, best) Diff_iff Diff_insert2 Diff_insert_absorb bij_id_imsupp
      id_on_def in_imsupp not_in_imsupp_same not_in_supp_alt usubst_simps(7))
  apply (subst (1 2) usubst_simps; (simp add: dpair.set_map term.FVars_permute)?)
  apply blast
  apply (meson not_imageI)
    apply (metis Int_commute id_on_image supp_id_on)
  apply (meson Int_Un_emptyI1 image_Int_empty)
  apply (subst (1 2) usubst_simps; (simp add: dpair.set_map term.FVars_permute)?)
  apply (metis Int_Un_emptyI1 disjoint_iff_not_equal fresh_usubst)
  apply (meson not_imageI)
    apply (metis Int_commute id_on_image supp_id_on)
   apply (smt (verit, best) Int_Un_emptyI1 disjoint_iff_not_equal fresh_usubst id_on_def imageE image_Int_empty supp_id_on term.FVars_permute)
  apply (rule exI[of _ "id"])
  apply (auto simp: supp_id_bound id_on_def dpair.map_comp dpair.map_id term.permute_id
    intro!: dpair.map_cong[THEN trans[OF _ dpair.map_id]])
  apply (meson disjoint_iff_not_equal not_in_supp_alt)
  apply (metis disjoint_iff_not_equal not_in_supp_alt)
  done

lemma dfst_dmap[simp]: "bij f \<Longrightarrow> dfst (dmap f xy) = f (dfst xy)"
  by transfer auto
lemma dsnd_dmap[simp]: "bij f \<Longrightarrow> dsnd (dmap f xy) = f (dsnd xy)"
  by transfer auto
lemma dset_alt: "dset xy = {dfst xy, dsnd xy}"
  by transfer auto

abbreviation (input) beta_D where
  "beta_D R x1 x2 B \<equiv>
    (\<exists>N N' f x M. B = {f} \<union> {x} \<and> x1 = App (Fix f x M) N \<and> x2 = App (Fix f x M) N' \<and> R N N') \<or>
    (\<exists>M M' N. B = {} \<and> x1 = App M N \<and> x2 = App M' N \<and> R M M') \<or>
    (\<exists>M M'. B = {} \<and> x1 = Succ M \<and> x2 = Succ M' \<and> R M M') \<or>
    (\<exists>M M'. B = {} \<and> x1 = Pred M \<and> x2 = Pred M' \<and> R M M') \<or>
    (\<exists>M M' N. B = {} \<and> x1 = term.Pair M N \<and> x2 = term.Pair M' N \<and> R M M') \<or>
    (\<exists>V N N'. B = {} \<and> x1 = term.Pair V N \<and> x2 = term.Pair V N' \<and> val V \<and> R N N') \<or>
    (\<exists>M M' xy N. B = dset xy \<and> x1 = term.Let xy M N \<and> x2 = term.Let xy M' N \<and> R M M') \<or>
    (\<exists>M M' N P. B = {} \<and> x1 = term.If M N P \<and> x2 = term.If M' N P \<and> R M M') \<or>
    (\<exists>N P. B = {} \<and> x1 = term.If Zero N P \<and> x2 = N) \<or>
    (\<exists>n N P. B = {} \<and> x1 = term.If (Succ n) N P \<and> x2 = P \<and> num n) \<or>
    (\<exists>V W xy M. B = dset xy \<and> x1 = term.Let xy (term.Pair V W) M \<and> x2 = M[V <- dfst xy][W <- dsnd xy] \<and> val V \<and> val W \<and> dset xy \<inter> FVars V = {}) \<or>
    (B = {} \<and> x1 = Pred Zero \<and> x2 = Zero) \<or>
    (\<exists>n. B = {} \<and> x1 = Pred (Succ n) \<and> x2 = n \<and> num n) \<or>
    (\<exists>V f x M. B = {f} \<union> {x} \<and> x1 = App (Fix f x M) V \<and> x2 = M[V <- x][Fix f x M <- f] \<and> val V \<and> f \<notin> FVars V)"

lemma beta_equiv_ob:
  assumes s: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a::var set|"
    and D: "beta_D R (x1::'a term) x2 B"
  shows "beta_D (\<lambda>a b. R (permute_term (inv \<sigma>) a) (permute_term (inv \<sigma>) b)) (permute_term \<sigma> x1) (permute_term \<sigma> x2) (\<sigma> ` B)"
  supply SET[simp] = s term.permute[OF s(1) s(2)] permute_term_inv[OF s] image_Un
      permute_usubst[OF s] dfst_dmap[OF s(1)] dsnd_dmap[OF s(1)] dpair.set_map[OF s(1)]
      val_permute_iff[OF s] num_permute_iff[OF s] term.FVars_permute[OF s(1) s(2)]
      inj_image_mem_iff[OF bij_is_inj[OF s(1)]] image_Int[OF bij_is_inj[OF s(1)], symmetric]
  using D
  apply (elim disjE exE conjE)
  subgoal for N N' f x M by (rule disjI1, rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ "permute_term \<sigma> N'"], rule exI[of _ "\<sigma> f"], rule exI[of _ "\<sigma> x"], rule exI[of _ "permute_term \<sigma> M"]) auto
  subgoal by (rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal for M M' xy N by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1, rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "permute_term \<sigma> M'"], rule exI[of _ "dmap \<sigma> xy"], rule exI[of _ "permute_term \<sigma> N"]) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal for V W xy M by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1, rule exI[of _ "permute_term \<sigma> V"], rule exI[of _ "permute_term \<sigma> W"], rule exI[of _ "dmap \<sigma> xy"], rule exI[of _ "permute_term \<sigma> M"]) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1) auto
  subgoal for V f x M by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule exI[of _ "permute_term \<sigma> V"], rule exI[of _ "\<sigma> f"], rule exI[of _ "\<sigma> x"], rule exI[of _ "permute_term \<sigma> M"]) auto
  done

lemma beta_refresh_ob:
  fixes x1 x2 :: "'a::var term"
  assumes "beta_D R x1 x2 B"
  shows "\<exists>B'. B' \<inter> (FVars x1 \<union> FVars x2) = {} \<and> beta_D R x1 x2 B'"
  using assms
proof (elim disjE exE)
  fix N N' f x M
  assume H: "B = {f} \<union> {x} \<and> x1 = App (Fix f x M) N \<and> x2 = App (Fix f x M) N' \<and> R N N'"
  then have hx1: "x1 = App (Fix f x M) N" and hx2: "x2 = App (Fix f x M) N'" and hR: "R N N'" by auto
  have b1: "|{f} \<union> {x}| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  have b2: "|FVars M \<union> FVars x1 \<union> FVars x2 \<union> {f} \<union> {x}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` ({f} \<union> {x}) \<inter> (FVars M \<union> FVars x1 \<union> FVars x2 \<union> {f} \<union> {x}) = {}"
      "id_on (FVars M - ({f} \<union> {x})) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M - ({f} \<union> {x})"] by auto
  have eq: "Fix f x M = Fix (g f) (g x) (permute_term g M)"
    using g by (auto intro!: exI[of _ g])
  have disj: "({g f} \<union> {g x}) \<inter> (FVars x1 \<union> FVars x2) = {}" using g(3) by auto
  show ?thesis
    apply (rule exI[of _ "{g f} \<union> {g x}"], rule conjI[OF disj], rule disjI1)
    apply (rule exI[of _ N], rule exI[of _ N'], rule exI[of _ "g f"], rule exI[of _ "g x"], rule exI[of _ "permute_term g M"])
    using hx1 hx2 eq hR by auto
next
  fix M M' N assume "B = {} \<and> x1 = App M N \<and> x2 = App M' N \<and> R M M'"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix M M' assume "B = {} \<and> x1 = Succ M \<and> x2 = Succ M' \<and> R M M'"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix M M' assume "B = {} \<and> x1 = Pred M \<and> x2 = Pred M' \<and> R M M'"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix M M' N assume "B = {} \<and> x1 = term.Pair M N \<and> x2 = term.Pair M' N \<and> R M M'"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V N N' assume "B = {} \<and> x1 = term.Pair V N \<and> x2 = term.Pair V N' \<and> val V \<and> R N N'"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix M M' xy N
  assume H: "B = dset xy \<and> x1 = term.Let xy M N \<and> x2 = term.Let xy M' N \<and> R M M'"
  then have hx1: "x1 = term.Let xy M N" and hx2: "x2 = term.Let xy M' N" and hR: "R M M'" by auto
  have b1: "|dset xy| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|FVars N \<union> FVars x1 \<union> FVars x2 \<union> dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> (FVars N \<union> FVars x1 \<union> FVars x2 \<union> dset xy) = {}"
      "id_on (FVars N - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars N - dset xy"] by auto
  have eq1: "term.Let xy M N = term.Let (dmap g xy) M (permute_term g N)"
    using g by (auto intro!: exI[of _ g])
  have eq2: "term.Let xy M' N = term.Let (dmap g xy) M' (permute_term g N)"
    using g by (auto intro!: exI[of _ g])
  have disj: "dset (dmap g xy) \<inter> (FVars x1 \<union> FVars x2) = {}"
    using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  show ?thesis
    apply (rule exI[of _ "dset (dmap g xy)"], rule conjI[OF disj])
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (rule exI[of _ M], rule exI[of _ M'], rule exI[of _ "dmap g xy"], rule exI[of _ "permute_term g N"])
    using hx1 hx2 eq1 eq2 hR by auto
next
  fix M M' N P assume "B = {} \<and> x1 = term.If M N P \<and> x2 = term.If M' N P \<and> R M M'"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix N P assume "B = {} \<and> x1 = term.If Zero N P \<and> x2 = N"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix n N P assume "B = {} \<and> x1 = term.If (Succ n) N P \<and> x2 = P \<and> num n"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V W xy M
  assume H: "B = dset xy \<and> x1 = term.Let xy (term.Pair V W) M \<and> x2 = M[V <- dfst xy][W <- dsnd xy] \<and> val V \<and> val W \<and> dset xy \<inter> FVars V = {}"
  then have hx1: "x1 = term.Let xy (term.Pair V W) M" and hx2: "x2 = M[V <- dfst xy][W <- dsnd xy]"
    and hV: "val V" and hW: "val W" and hfr: "dset xy \<inter> FVars V = {}" by auto
  have b1: "|dset xy| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|FVars M \<union> FVars x1 \<union> FVars x2 \<union> dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> (FVars M \<union> FVars x1 \<union> FVars x2 \<union> dset xy) = {}"
      "id_on (FVars M - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M - dset xy"] by auto
  have eq: "term.Let xy (term.Pair V W) M = term.Let (dmap g xy) (term.Pair V W) (permute_term g M)"
    using g by (auto intro!: exI[of _ g])
  have fr': "dsnd xy \<notin> FVars V" using hfr dsel_dset(2) by blast
  have gfr: "g (dsnd xy) \<notin> FVars V"
    using g(3) dsel_dset(2) unfolding hx1 term.set by blast
  have subst_eq: "(permute_term g M)[V <- dfst (dmap g xy)][W <- dsnd (dmap g xy)] = M[V <- dfst xy][W <- dsnd xy]"
    unfolding dfst_dmap[OF g(1)] dsnd_dmap[OF g(1)]
    apply (rule premute_term_usubst2[OF g(1) g(2)])
    subgoal using g(4) unfolding id_on_def dset_alt by auto
    subgoal using fr' gfr by auto
    done
  have side: "dset (dmap g xy) \<inter> FVars V = {}"
    using g(3) unfolding dpair.set_map[OF g(1) g(2)] hx1 term.set by blast
  have disj: "dset (dmap g xy) \<inter> (FVars x1 \<union> FVars x2) = {}"
    using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  show ?thesis
    apply (rule exI[of _ "dset (dmap g xy)"], rule conjI[OF disj])
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (rule exI[of _ V], rule exI[of _ W], rule exI[of _ "dmap g xy"], rule exI[of _ "permute_term g M"])
    using hx1 hx2 eq subst_eq hV hW side by auto
next
  assume "B = {} \<and> x1 = Pred Zero \<and> x2 = Zero"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix n assume "B = {} \<and> x1 = Pred (Succ n) \<and> x2 = n \<and> num n"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V f x M
  assume H: "B = {f} \<union> {x} \<and> x1 = App (Fix f x M) V \<and> x2 = M[V <- x][Fix f x M <- f] \<and> val V \<and> f \<notin> FVars V"
  then have hx1: "x1 = App (Fix f x M) V" and hx2: "x2 = M[V <- x][Fix f x M <- f]"
    and hV: "val V" and hfr: "f \<notin> FVars V" by auto
  have b1: "|{f} \<union> {x}| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  have b2: "|FVars M \<union> FVars x1 \<union> FVars x2 \<union> {f} \<union> {x}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` ({f} \<union> {x}) \<inter> (FVars M \<union> FVars x1 \<union> FVars x2 \<union> {f} \<union> {x}) = {}"
      "id_on (FVars M - ({f} \<union> {x})) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M - ({f} \<union> {x})"] by auto
  have eq: "Fix f x M = Fix (g f) (g x) (permute_term g M)"
    using g by (auto intro!: exI[of _ g])
  have gfr: "g f \<notin> FVars V"
    using g(3) unfolding hx1 term.set by auto
  have subst_eq: "(permute_term g M)[V <- g x][Fix f x M <- g f] = M[V <- x][Fix f x M <- f]"
    apply (rule premute_term_usubst2[OF g(1) g(2)])
    subgoal using g(4) unfolding id_on_def by auto
    subgoal using hfr gfr by auto
    done
  have disj: "({g f} \<union> {g x}) \<inter> (FVars x1 \<union> FVars x2) = {}" using g(3) by auto
  have px1: "x1 = App (Fix (g f) (g x) (permute_term g M)) V"
    unfolding hx1 eq[symmetric] by simp
  have px2: "x2 = (permute_term g M)[V <- g x][Fix (g f) (g x) (permute_term g M) <- g f]"
    unfolding eq[symmetric] hx2 subst_eq by simp
  show ?thesis
    apply (rule exI[of _ "{g f} \<union> {g x}"], rule conjI[OF disj])
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2)
    apply (rule exI[of _ V], rule exI[of _ "g f"], rule exI[of _ "g x"], rule exI[of _ "permute_term g M"])
    using px1 px2 hV gfr by auto
qed

binder_inductive (no_auto_equiv) beta
  subgoal premises prems for R B \<sigma> x1 x2 by (rule beta_equiv_ob[OF prems(1) prems(2) prems(3)])
  subgoal premises prems for R B x1 x2 by (rule beta_refresh_ob[OF prems(3)])
  done

lemma beta_deterministic:
  fixes M :: "'a::var term"
  shows "M \<rightarrow> N \<Longrightarrow> M \<rightarrow> N' \<Longrightarrow> N = N'"
  apply(binder_induction M N arbitrary: N' avoiding: M N N' rule: beta.strong_induct)
  subgoal premises prems for M N f x Q N' using prems(6)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-5) elim:beta.cases)
    using prems(4) vals_are_normal[of M]
    using normal_def apply blast
    done
  subgoal premises prems for M N M' N' using prems(3)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-2) elim:beta.cases)
    using beta.cases prems(1) apply force
    using normal_def prems(1) val.intros(4) vals_are_normal apply blast
    using normal_def prems(1) val.intros(4) vals_are_normal apply blast
    done
  subgoal for M M' N'
    by(erule beta.cases) (auto elim:beta.cases)
  subgoal  premises prems for M M' N' using prems(3)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-2) elim:beta.cases)
    using normal_def num.intros(1) nums_are_normal prems(1) apply blast
    using normal_def num.intros(2) nums_are_normal prems(1) apply blast
    done
  subgoal premises prems for M N M' N' using prems(3)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-2) elim:beta.cases)
    using normal_def prems(1) vals_are_normal apply blast
    using normal_def prems(1) vals_are_normal apply blast
    done
  subgoal premises prems for M N M' N' using prems(4)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-3) elim:beta.cases)
    using normal_def prems(1) vals_are_normal apply blast
    using normal_def prems(1) vals_are_normal apply blast
    done
  subgoal premises prems for M N xy M' N' using prems(6)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-5) elim:beta.cases)
    using normal_def prems(4) val.intros(3) vals_are_normal apply blast
    done
  subgoal premises prems for M M' N P N' using prems(3)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-2) elim:beta.cases)
    using normal_def num.intros(1) nums_are_normal prems(1) apply blast
    using normal_def num.intros(2) nums_are_normal prems(1) apply blast
    done
  subgoal for N P N'
    by(erule beta.cases) (auto elim:beta.cases)
  subgoal for n N P N'
    apply (erule beta.cases)
    apply (auto elim:beta.cases)
    using normal_def num.intros(2) nums_are_normal apply blast
    done
  subgoal premises prems for V W xy M N'
  proof -
    have PVW: "val (term.Pair V W)" using prems(4,5) by (auto intro: val.intros)
    show ?thesis using prems(7)
    proof (cases rule: beta.cases)
      case (OrdLet M0 M0' xy2 N0)
      have "M0 = term.Pair V W" using OrdLet(1) by auto
      then show ?thesis using OrdLet(3) PVW vals_are_normal normal_def by metis
    next
      case (Let V2 W2 xy2 M2)
      have V2: "V2 = V" and W2: "W2 = W" using Let(1) by auto
      obtain h where h: "bij h" "|supp h| <o |UNIV::'a set|" "id_on (FVars M - dset xy) h"
          "dmap h xy = xy2" "permute_term h M = M2"
        using Let(1) unfolding term.inject(8) by auto
      have hfst: "h (dfst xy) = dfst xy2" and hsnd: "h (dsnd xy) = dsnd xy2"
        using h(4) dfst_dmap[OF h(1)] dsnd_dmap[OF h(1)] by auto
      have fresh: "{dsnd xy, h (dsnd xy)} \<inter> FVars V = {}"
      proof -
        have "dsnd xy \<notin> FVars V" using prems(6) dsel_dset(2) by blast
        moreover have "h (dsnd xy) \<notin> FVars V"
          using Let(5) V2 hsnd dsel_dset(2) by force
        ultimately show ?thesis by blast
      qed
      have "N' = (permute_term h M)[V <- h (dfst xy)][W <- h (dsnd xy)]"
        using Let(2) h(5) V2 W2 hfst hsnd by auto
      moreover have "(permute_term h M)[V <- h (dfst xy)][W <- h (dsnd xy)] = M[V <- dfst xy][W <- dsnd xy]"
        apply (rule premute_term_usubst2[OF h(1) h(2)])
        subgoal using h(3) unfolding id_on_def dset_alt by auto
        subgoal using fresh .
        done
      ultimately show ?thesis by simp
    qed auto
  qed
  subgoal for N'
    apply (erule beta.cases)
    apply (auto elim:beta.cases)
    done
  subgoal for n N'
    apply (erule beta.cases)
                 apply (auto elim:beta.cases)
    using normal_def num.intros(2) nums_are_normal apply blast
    done
  subgoal premises prems for V f x M N'
  proof -
    have vF: "val (Fix f x M)" by (rule val.intros(4))
    show ?thesis using prems(6)
    proof (cases rule: beta.cases)
      case (OrdApp2 N0 N0' f2 x2 M2)
      have "N0 = V" using OrdApp2(1) by auto
      then show ?thesis using OrdApp2(3) prems(4) vals_are_normal normal_def by metis
    next
      case (OrdApp1 M0 M0' N0)
      have "M0 = Fix f x M" using OrdApp1(1) by auto
      then show ?thesis using OrdApp1(3) vF vals_are_normal normal_def by metis
    next
      case (FixBeta V2 f2 x2 M2)
      have eqF: "Fix f x M = Fix f2 x2 M2" and V2: "V2 = V" using FixBeta(1) by auto
      obtain h where h: "bij h" "|supp h| <o |UNIV::'a set|" "id_on (FVars M - {x, f}) h"
          "h f = f2" "h x = x2" "permute_term h M = M2"
        using eqF unfolding term.inject(6) by auto
      have fresh: "{f, h f} \<inter> FVars V = {}"
        using prems(5) FixBeta(4) h(4) V2 by auto
      have "N' = (permute_term h M)[V <- h x][Fix f x M <- h f]"
        unfolding h(4) h(5) h(6) eqF V2[symmetric] by (rule FixBeta(2))
      moreover have "(permute_term h M)[V <- h x][Fix f x M <- h f] = M[V <- x][Fix f x M <- f]"
        apply (rule premute_term_usubst2[OF h(1) h(2)])
        subgoal using h(3) unfolding id_on_def by auto
        subgoal using fresh .
        done
      ultimately show ?thesis by simp
    qed auto
  qed
  done

lemma betas_pets:
  "M \<rightarrow>[m] N \<Longrightarrow> N \<rightarrow> P \<Longrightarrow> M \<rightarrow>[Suc m] P"
  apply(induction rule:betas.induct)
   apply(auto intro:betas.intros)
  done

lemma betas_path_sum:
  "M \<rightarrow>[m] N \<Longrightarrow> N \<rightarrow>[n] P \<Longrightarrow> M \<rightarrow>[m + n] P"
  apply(induction rule:betas.induct)
   apply(auto intro:betas.intros)
  done

corollary beta_star_sums:
  "M \<rightarrow>* N \<Longrightarrow> N \<rightarrow>* P \<Longrightarrow> M \<rightarrow>* P"
  using betas_path_sum beta_star_def by metis

lemma betas_deterministic: 
  "M \<rightarrow>[n] N \<Longrightarrow> M \<rightarrow>[n] N' \<Longrightarrow> N = N'"
proof(induction n arbitrary: M)
  case (Suc n)
  then obtain P P' where "M \<rightarrow> P" and "P \<rightarrow>[n] N" and "M \<rightarrow> P'" and "P' \<rightarrow>[n] N'"
    using betas.cases nat.distinct(1) nat.inject
    by metis
  moreover then have "P = P'" using beta_deterministic by auto
  ultimately show ?case using Suc.IH by simp
qed(auto elim:betas.cases)

lemma normalizes_stepsTo_normalizes: "M \<rightarrow> N \<Longrightarrow> normalizes N \<Longrightarrow> normalizes M"
  using normalizes_def beta_star_def betas.intros by blast

definition less_defined :: "'var::var term \<Rightarrow> 'var term \<Rightarrow> bool" (infix "\<lesssim>" 90) where
  "P \<lesssim> Q \<equiv> normalizes P \<longrightarrow> (\<exists>N. normal N \<and> P \<rightarrow>* N \<and> Q \<rightarrow>* N)"
                                                                      
lemma diverge_or_normalizes: "diverge M \<or> normalizes M"
proof(rule disjCI)
  assume "\<not> normalizes M"
  then show "M \<Up>"
  proof (coinduction arbitrary: M rule:diverge.coinduct)
    case diverge
    have "\<not> normal M" 
      using \<open>\<not> normalizes M\<close> normalizes_def beta_star_def betas.intros by blast
    then obtain N where "M \<rightarrow> N" using normal_def by auto
    then have "\<not> normalizes N" 
      using normalizes_stepsTo_normalizes diverge by auto
    then show ?case using \<open>M \<rightarrow> N\<close> by auto
  qed
qed

lemma betas_diverge_back:
  assumes "M \<rightarrow>[n] N" and "N \<Up>" shows "M \<Up>"
  using assms
proof(induction rule:betas.induct)
  case (step M N n P)
  then show ?case using diverge.intros by blast
qed

corollary beta_star_diverge_back:
  "M \<rightarrow>* N \<Longrightarrow> N \<Up> \<Longrightarrow> M \<Up>"
  using betas_diverge_back beta_star_def by blast


lemma beta_diverge_forw:
  assumes "M \<rightarrow> N" and "M \<Up>" shows "N \<Up>"
proof -
  obtain N' where "M \<rightarrow> N'" and "diverge N'" using \<open>diverge M\<close> diverge.cases by auto
  then have "N = N'" using \<open>M \<rightarrow> N\<close> beta_deterministic by auto
  then show "diverge N" using \<open>diverge N'\<close> by auto
qed

lemma betas_diverge_forw:
  "M \<rightarrow>[k] N \<Longrightarrow> M \<Up> \<Longrightarrow> N \<Up>"
proof(induction rule: betas.induct)
  case (step M N n P)
  then have "diverge N" using beta_diverge_forw by auto
  then show ?case using \<open>diverge N \<Longrightarrow> diverge P\<close> by auto
qed

corollary beta_star_diverge_forw:
  "M \<rightarrow>* N \<Longrightarrow> M \<Up> \<Longrightarrow> N \<Up>" 
  unfolding beta_star_def using betas_diverge_forw by auto

lemma num_usubst[simp]: "num M \<Longrightarrow> M[V <- x] = M"
  by (induct M rule: num.induct) auto

lemma val_usubst[simp]: "val M \<Longrightarrow> val V \<Longrightarrow> val (M[V <- x])"
  by (binder_induction M avoiding: V x rule: val.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
    (auto intro: val.intros)

lemma beta_usubst: "M \<rightarrow> N \<Longrightarrow> val V \<Longrightarrow> M[V <- x] \<rightarrow> N[V <- x]"
  apply (binder_induction M N avoiding: M N V x rule: beta.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
  apply (auto intro: beta.intros simp: Int_Un_distrib usubst_usubst[of _ x V])
  apply (subst usubst_usubst[of _ x V])
    apply auto
   apply (metis Int_emptyD dsel_dset(2))
  apply (subst usubst_usubst[of _ x V])
    apply auto
   apply (metis Int_emptyD dsel_dset(1))
  apply (auto intro: beta.intros)
  apply (rule beta.Let)
    apply (auto simp: FVars_usubst disjoint_iff split: if_splits)
  done

lemma FVars_beta: "M \<rightarrow> N \<Longrightarrow> FVars N \<subseteq> FVars M"
  apply(binder_induction M N avoiding: "App M N" rule:beta.strong_induct)
               apply(auto)
  subgoal premises prems for V f x M z
  proof -
    have "FVars M[V <- x][Fix f x M <- f] \<subseteq> FVars M \<union> FVars V"
      using FVars_usubst fresh_usubst by fastforce
    then have "z \<in> FVars M" using prems by auto
    then show ?thesis by auto
  qed
  done

corollary FVars_betas: "M \<rightarrow>[n] N \<Longrightarrow> FVars N \<subseteq> FVars M"
  apply(induction rule:betas.induct)
  using FVars_beta by auto

corollary FVars_beta_star: "M \<rightarrow>* N \<Longrightarrow> FVars N \<subseteq> FVars M"
  using beta_star_def FVars_betas by blast

lemma subst_iden[simp]: "M[Var x <- x] = M"
  apply(binder_induction M avoiding: x M rule:term_strong_induct)
          apply(auto simp add: Int_Un_distrib)
  done

section \<open>Contexts\<close>

inductive eval_ctx :: "'var :: var \<Rightarrow> 'var term \<Rightarrow> bool" where
  "eval_ctx hole (Var hole)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars M \<Longrightarrow> eval_ctx hole (App (Fix f x M) E)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> eval_ctx hole (App E N)"
| "eval_ctx hole E \<Longrightarrow> eval_ctx hole (Succ E)"
| "eval_ctx hole E \<Longrightarrow> eval_ctx hole (Pred E)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> eval_ctx hole (Pair E N)"
| "val V \<Longrightarrow> eval_ctx hole E \<Longrightarrow> hole \<notin> FVars V \<Longrightarrow> eval_ctx hole (Pair V E)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> hole \<notin> dset xy \<Longrightarrow> eval_ctx hole (Let xy E N)"
| "eval_ctx hole E \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> hole \<notin> FVars P \<Longrightarrow> eval_ctx hole (If E N P)"

lemma eval_ctx_refresh_ob:
  fixes x1 :: "'a::var" and x2 :: "'a term"
  assumes "(\<exists>hole. B = {} \<and> x1 = hole \<and> x2 = Var hole) \<or>
           (\<exists>hole E M f x. B = {f} \<union> {x} \<and> x1 = hole \<and> x2 = App (Fix f x M) E \<and> R hole E \<and> hole \<notin> FVars M) \<or>
           (\<exists>hole E N. B = {} \<and> x1 = hole \<and> x2 = App E N \<and> R hole E \<and> hole \<notin> FVars N) \<or>
           (\<exists>hole E. B = {} \<and> x1 = hole \<and> x2 = Succ E \<and> R hole E) \<or>
           (\<exists>hole E. B = {} \<and> x1 = hole \<and> x2 = Pred E \<and> R hole E) \<or>
           (\<exists>hole E N. B = {} \<and> x1 = hole \<and> x2 = term.Pair E N \<and> R hole E \<and> hole \<notin> FVars N) \<or>
           (\<exists>V hole E. B = {} \<and> x1 = hole \<and> x2 = term.Pair V E \<and> val V \<and> R hole E \<and> hole \<notin> FVars V) \<or>
           (\<exists>hole E N xy. B = dset xy \<and> x1 = hole \<and> x2 = term.Let xy E N \<and> R hole E \<and> hole \<notin> FVars N \<and> hole \<notin> dset xy) \<or>
           (\<exists>hole E N P. B = {} \<and> x1 = hole \<and> x2 = term.If E N P \<and> R hole E \<and> hole \<notin> FVars N \<and> hole \<notin> FVars P)"
  shows "\<exists>B'. B' \<inter> ({x1} \<union> FVars x2) = {} \<and>
         ((\<exists>hole. B' = {} \<and> x1 = hole \<and> x2 = Var hole) \<or>
          (\<exists>hole E M f x. B' = {f} \<union> {x} \<and> x1 = hole \<and> x2 = App (Fix f x M) E \<and> R hole E \<and> hole \<notin> FVars M) \<or>
          (\<exists>hole E N. B' = {} \<and> x1 = hole \<and> x2 = App E N \<and> R hole E \<and> hole \<notin> FVars N) \<or>
          (\<exists>hole E. B' = {} \<and> x1 = hole \<and> x2 = Succ E \<and> R hole E) \<or>
          (\<exists>hole E. B' = {} \<and> x1 = hole \<and> x2 = Pred E \<and> R hole E) \<or>
          (\<exists>hole E N. B' = {} \<and> x1 = hole \<and> x2 = term.Pair E N \<and> R hole E \<and> hole \<notin> FVars N) \<or>
          (\<exists>V hole E. B' = {} \<and> x1 = hole \<and> x2 = term.Pair V E \<and> val V \<and> R hole E \<and> hole \<notin> FVars V) \<or>
          (\<exists>hole E N xy. B' = dset xy \<and> x1 = hole \<and> x2 = term.Let xy E N \<and> R hole E \<and> hole \<notin> FVars N \<and> hole \<notin> dset xy) \<or>
          (\<exists>hole E N P. B' = {} \<and> x1 = hole \<and> x2 = term.If E N P \<and> R hole E \<and> hole \<notin> FVars N \<and> hole \<notin> FVars P))"
  using assms
proof (elim disjE exE)
  fix hole assume "B = {} \<and> x1 = hole \<and> x2 = Var hole"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix hole E M f x assume H: "B = {f} \<union> {x} \<and> x1 = hole \<and> x2 = App (Fix f x M) E \<and> R hole E \<and> hole \<notin> FVars M"
  then have hx1: "x1 = hole" and hx2: "x2 = App (Fix f x M) E" and hR: "R hole E" and hf: "hole \<notin> FVars M" by auto
  have b1: "|{f} \<union> {x}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  have b2: "|{hole} \<union> FVars M \<union> FVars E \<union> {f} \<union> {x}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` ({f} \<union> {x}) \<inter> ({hole} \<union> FVars M \<union> FVars E \<union> {f} \<union> {x}) = {}"
      "id_on (FVars M - ({f} \<union> {x})) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M - ({f} \<union> {x})"] by auto
  have eq: "Fix f x M = Fix (g f) (g x) (permute_term g M)"
    using g by (auto intro!: exI[of _ g])
  have holeM: "hole \<notin> FVars (permute_term g M)"
  proof
    assume "hole \<in> FVars (permute_term g M)"
    then obtain y where y: "y \<in> FVars M" "g y = hole" unfolding term.FVars_permute[OF g(1,2)] by auto
    show False
    proof (cases "y \<in> {f} \<union> {x}")
      case True then show False using g(3) y(2) by auto
    next
      case False then have "g y = y" using g(4) y(1) unfolding id_on_def by auto
      then show False using y hf by auto
    qed
  qed
  have disj: "({g f} \<union> {g x}) \<inter> ({x1} \<union> FVars x2) = {}"
    using g(3) unfolding hx1 hx2 term.set(6,7) by auto
  show ?thesis
    apply (rule exI[of _ "{g f} \<union> {g x}"], rule conjI[OF disj])
    apply (rule disjI2, rule disjI1)
    apply (rule exI[of _ hole], rule exI[of _ E], rule exI[of _ "permute_term g M"], rule exI[of _ "g f"], rule exI[of _ "g x"])
    using hx1 hx2 eq hR holeM by auto
next
  fix hole E N assume "B = {} \<and> x1 = hole \<and> x2 = App E N \<and> R hole E \<and> hole \<notin> FVars N"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix hole E assume "B = {} \<and> x1 = hole \<and> x2 = Succ E \<and> R hole E"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix hole E assume "B = {} \<and> x1 = hole \<and> x2 = Pred E \<and> R hole E"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix hole E N assume "B = {} \<and> x1 = hole \<and> x2 = term.Pair E N \<and> R hole E \<and> hole \<notin> FVars N"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix V hole E assume "B = {} \<and> x1 = hole \<and> x2 = term.Pair V E \<and> val V \<and> R hole E \<and> hole \<notin> FVars V"
  then show ?thesis by (intro exI[of _ "{}"]) auto
next
  fix hole E N xy assume H: "B = dset xy \<and> x1 = hole \<and> x2 = term.Let xy E N \<and> R hole E \<and> hole \<notin> FVars N \<and> hole \<notin> dset xy"
  then have hx1: "x1 = hole" and hx2: "x2 = term.Let xy E N" and hR: "R hole E"
    and hfN: "hole \<notin> FVars N" and hfd: "hole \<notin> dset xy" by auto
  have b1: "|dset xy| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|{hole} \<union> FVars E \<union> FVars N \<union> dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> ({hole} \<union> FVars E \<union> FVars N \<union> dset xy) = {}"
      "id_on (FVars N - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars N - dset xy"] by auto
  have eq: "term.Let xy E N = term.Let (dmap g xy) E (permute_term g N)"
    using g by (auto intro!: exI[of _ g])
  have holed: "hole \<notin> dset (dmap g xy)" using g(3) unfolding dpair.set_map[OF g(1,2)] by auto
  have holeN: "hole \<notin> FVars (permute_term g N)"
  proof
    assume "hole \<in> FVars (permute_term g N)"
    then obtain y where y: "y \<in> FVars N" "g y = hole" unfolding term.FVars_permute[OF g(1,2)] by auto
    show False
    proof (cases "y \<in> dset xy")
      case True then show False using g(3) y(2) by auto
    next
      case False then have "g y = y" using g(4) y(1) unfolding id_on_def by auto
      then show False using y hfN by auto
    qed
  qed
  have disj: "dset (dmap g xy) \<inter> ({x1} \<union> FVars x2) = {}"
    using g(3) unfolding hx1 hx2 term.set(9) dpair.set_map[OF g(1,2)] by auto
  show ?thesis
    apply (rule exI[of _ "dset (dmap g xy)"], rule conjI[OF disj])
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (rule exI[of _ hole], rule exI[of _ E], rule exI[of _ "permute_term g N"], rule exI[of _ "dmap g xy"])
    using hx1 hx2 eq hR holeN holed by auto
next
  fix hole E N P assume "B = {} \<and> x1 = hole \<and> x2 = term.If E N P \<and> R hole E \<and> hole \<notin> FVars N \<and> hole \<notin> FVars P"
  then show ?thesis by (intro exI[of _ "{}"]) auto
qed

binder_inductive eval_ctx
  subgoal premises prems for R B x1 x2 by (rule eval_ctx_refresh_ob[OF prems(3)])
  done

lemma eval_ctx_strong_induct[consumes 1]: "eval_ctx (x1 :: 'a) x2 \<Longrightarrow>
(\<And>p. |K p :: 'a set| <o |UNIV :: 'a :: var set| ) \<Longrightarrow>
(\<And>hole p. P hole (Var hole) p) \<Longrightarrow>
(\<And>hole E M f x p. {f, x} \<inter> K p = {} \<Longrightarrow> eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> hole \<notin> FVars M \<Longrightarrow> P hole (App (Fix f x M) E) p) \<Longrightarrow>
(\<And>hole E N p. eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> P hole (App E N) p) \<Longrightarrow>
(\<And>hole E p. eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> P hole (Succ E) p) \<Longrightarrow>
(\<And>hole E p. eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> P hole (Pred E) p) \<Longrightarrow>
(\<And>hole E N p. eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> P hole (term.Pair E N) p) \<Longrightarrow>
(\<And>V hole E p. val V \<Longrightarrow> eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> hole \<notin> FVars V \<Longrightarrow> P hole (term.Pair V E) p) \<Longrightarrow>
(\<And>hole E N xy p. dset xy \<inter> K p = {} \<Longrightarrow> eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> hole \<notin> dset xy \<Longrightarrow> P hole (term.Let xy E N) p) \<Longrightarrow>
(\<And>hole E N Pa p. eval_ctx hole E \<Longrightarrow> \<forall>p. P hole E p \<Longrightarrow> hole \<notin> FVars N \<Longrightarrow> hole \<notin> FVars Pa \<Longrightarrow> P hole (term.If E N Pa) p) \<Longrightarrow> \<forall>p. P x1 x2 p"
  by (rule eval_ctx.strong_induct[where K=K]) simp_all

definition blocked :: "'var :: var \<Rightarrow> 'var term \<Rightarrow> bool" where 
  "blocked z M = (\<exists> hole E. eval_ctx hole E \<and> (M = E[Var z <- hole]))"

text \<open>@{text blocked_fresh_hole} and @{text eval_ctx_fresh} have moved further down
  (after @{text usubst_Let} and the substitution-push lemmas their proofs require).\<close>

lemma eval_subst: "eval_ctx x E \<Longrightarrow> y \<notin> FVars E \<Longrightarrow> eval_ctx y E[Var y <- x]"
  apply(binder_induction x E avoiding: y E rule: eval_ctx_strong_induct)
          apply(auto intro: eval_ctx.intros)
  apply (subst usubst_simps)
     apply (auto intro: eval_ctx.intros)
  done

thm eval_ctx.strong_induct[no_vars]

lemma eval_ctxt_FVars:
  "eval_ctx x E \<Longrightarrow> x \<in> FVars E"
  by (induct x E rule: eval_ctx.induct) auto

lemma SSupp_term_Var[simp]: "SSupp Var Var = {}"
  unfolding SSupp_def by auto

lemma IImsupp_term_Var[simp]: "IImsupp Var FVars Var = {}"
  unfolding IImsupp_def by auto

lemma subst_Var: "subst Var t = (t :: 'var :: var term)"
  by (rule term.strong_induct[where P = "\<lambda>t p. p = t \<longrightarrow> subst Var t = (t :: 'var :: var term)" and K = FVars, simplified])
    (auto simp: Int_Un_distrib intro!: ordLess_ordLeq_trans[OF term.set_bd var_class.large'])

lemma IImsupp_term_bound:
  fixes f ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  shows "|IImsupp Var FVars f| <o |UNIV::'a set|"
  unfolding IImsupp_def using assms
  by (simp add: UN_bound Un_bound ordLess_ordLeq_trans[OF term.set_bd var_class.large'])

lemma SSupp_term_subst:
  fixes f g ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  shows "SSupp Var (subst f \<circ> g) \<subseteq> SSupp Var f \<union> SSupp Var g"
  using assms by (auto simp: SSupp_def)

lemmas FVars_subst = term.Vrs_Sb

lemma IImsupp_term_subst:
  fixes f g ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  shows "IImsupp Var FVars (subst f \<circ> g) \<subseteq> IImsupp Var FVars f \<union> IImsupp Var FVars g"
  using assms using SSupp_term_subst[of f g]
  apply (auto simp: IImsupp_def FVars_subst)
  by (metis (mono_tags, lifting) SSupp_def comp_apply mem_Collect_eq singletonD term.set(5) term.subst(5))

lemma SSupp_term_subst_bound:
  fixes f g ::"'a::var \<Rightarrow> 'a term"
  assumes "|SSupp Var f| <o |UNIV::'a set|"
  assumes "|SSupp Var g| <o |UNIV::'a set|"
  shows "|SSupp Var (subst f \<circ> g)| <o |UNIV :: 'a set|"
  using SSupp_term_subst[of f g] assms
  by (simp add: card_of_subset_bound Un_bound)

lemmas subst_cong = term.Sb_cong

lemma subst_subst: "eval_ctx x E \<Longrightarrow> y \<notin> FVars E \<Longrightarrow> E[Var y <- x][Var z <- y] = E[Var z <- x]"
  apply (cases "x = z")
  subgoal
    by (auto simp add: usubst_def subst_comp intro!: subst_cong SSupp_term_subst_bound)
  subgoal by (subst usubst_usubst) (auto dest: eval_ctxt_FVars)
  done

lemma blocked_inductive: 
  "blocked z (Var z)"
  "blocked z N \<Longrightarrow> blocked z (App (Fix f x M) N)"
  "blocked z M \<Longrightarrow> blocked z (App M N)"
  "blocked z M \<Longrightarrow> blocked z (Succ M)"
  "blocked z M \<Longrightarrow> blocked z (Pred M)"
  "blocked z M \<Longrightarrow> blocked z (Pair M N)"
  "val V \<Longrightarrow> blocked z M \<Longrightarrow> blocked z (Pair V M)"
  "blocked z M \<Longrightarrow> z \<notin> dset xy \<Longrightarrow> dset xy \<inter> FVars M = {} \<Longrightarrow> blocked z (Let xy M N)"
  "blocked z M \<Longrightarrow> blocked z (If M N P)"
  apply(simp_all add: blocked_def)
  using eval_ctx.intros(1) apply fastforce
  subgoal
proof (erule exE)+
  fix hole E
  assume "eval_ctx hole E \<and> N = E[Var z <- hole]"
  then have "eval_ctx hole E" and "N = E[Var z <- hole]" by auto
  moreover obtain hole' where "hole' \<notin> FVars (App M E)"
    using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="App M E"]
    by auto
  moreover obtain E' where "E' = App (Fix f x M) E[Var hole'<-hole]" by simp
  ultimately have "eval_ctx hole' E'" using eval_subst[of hole E hole'] eval_ctx.intros(2)
    by (metis Un_iff term.set(6))
  have "App (Fix f x M) N = E'[Var z <- hole']" 
    using subst_subst \<open>E' = App (Fix f x M) E[Var hole' <- hole]\<close> \<open>N = E[Var z <- hole]\<close>
      \<open>eval_ctx hole E\<close> \<open>hole' \<notin> FVars (App M E)\<close> 
    by fastforce
  show "\<exists>hole' E'. eval_ctx hole' E' \<and> App (Fix f x M) N = E'[Var z <- hole']"
    using \<open>eval_ctx hole' E'\<close> \<open>App (Fix f x M) N = E'[Var z <- hole']\<close>
    by auto
qed
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="App E N"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
      apply (rule exI[of _ "App E[Var hole' <- hole] N"])
        apply (auto intro!: eval_ctx.intros(3) dest: eval_subst[of hole E hole'] simp: subst_subst)
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="Succ E"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
      apply (rule exI[of _ "Succ (E[Var hole' <- hole])"])
        apply (auto intro!: eval_ctx.intros(4) dest: eval_subst[of hole E hole'] simp: subst_subst)
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="Pred E"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
      apply (rule exI[of _ "Pred (E[Var hole' <- hole])"])
        apply (auto intro!: eval_ctx.intros(5) dest: eval_subst[of hole E hole'] simp: subst_subst)
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="Pair E N"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
      apply (rule exI[of _ "Pair (E[Var hole' <- hole]) N"])
        apply (auto intro!: eval_ctx.intros(6) dest: eval_subst[of hole E hole'] simp: subst_subst)
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="Pair V E"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
        apply (rule exI[of _ "Pair V (E[Var hole' <- hole])"])
        apply (auto intro!: eval_ctx.intros(7) dest: eval_subst[of hole E hole'] simp: subst_subst)
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="Pair E (Pair N (Pair (Var (dfst xy)) (Var (dsnd xy))))"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
        apply (rule exI[of _ "Let xy (E[Var hole' <- hole]) N"])
        apply (auto intro!: eval_ctx.intros(8) dest: eval_subst[of hole E hole'] simp: subst_subst dset_alt)
        apply (subst usubst_simps)
        apply (auto simp: dset_alt FVars_usubst term.permute_id subst_subst dest: eval_subst[of hole E hole'] intro!: exI[of _ id])
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for hole E
      using exists_fresh[OF ordLess_ordLeq_trans[OF term.set_bd var_class.large'], where ?x3="If E N P"]
      apply (elim exE)
      subgoal for hole'
      apply (rule exI[of _ hole'])
        apply (rule exI[of _ "If (E[Var hole' <- hole]) N P"])
        apply (auto intro!: eval_ctx.intros(9) dest: eval_subst[of hole E hole'] simp: subst_subst)
        done
      done
    done
  done

definition stuck :: "'var::var term \<Rightarrow> bool" where
  "stuck M = (\<exists>E hole N. eval_ctx hole E \<and> E[N <- hole] = M \<and> stuckEx N)"

definition getStuck :: "'var::var term \<Rightarrow> bool" where
  "getStuck M = (\<exists>N. stuck N \<and> M \<rightarrow>* N)"

lemma stuckEx_imp_stuck: "stuckEx M \<Longrightarrow> stuck M"
  unfolding stuck_def by (metis eval_ctx.intros(1) usubst_simps(5))

text \<open>Re-holing infrastructure for the progress lemma: a stuck term can always be
  decomposed with a hole avoiding any given finite set (choose a fresh hole and rename).\<close>

lemma subst_subst2: "y \<notin> FVars E \<Longrightarrow> E[Var y <- x][s <- y] = (E[s <- x] :: 'a::var term)"
  by (auto simp add: usubst_def subst_comp intro!: subst_cong SSupp_term_subst_bound)

lemma stuck_fresh_hole:
  fixes M :: "'a::var term"
  assumes "stuck M" and "finite A"
  shows "\<exists>hole E s. eval_ctx hole E \<and> M = E[s <- hole] \<and> stuckEx s \<and> hole \<notin> A"
proof -
  from assms(1) obtain E hole s where ctx: "eval_ctx hole E" and M: "E[s <- hole] = M" and st: "stuckEx s"
    unfolding stuck_def by blast
  obtain hole' :: 'a where h': "hole' \<notin> A \<union> {hole} \<union> FVars E"
    using arb_element[of "A \<union> {hole} \<union> FVars E"] assms(2) by auto
  define E' where "E' \<equiv> E[Var hole' <- hole]"
  have ctx': "eval_ctx hole' E'" unfolding E'_def by (rule eval_subst[OF ctx]) (use h' in auto)
  have M': "M = E'[s <- hole']"
    unfolding E'_def using subst_subst2[of hole' E hole s] h' M by auto
  show ?thesis using ctx' M' st h' by auto
qed

text \<open>Alpha-refreshing the binders of @{text Fix} and @{text Let} away from a finite set,
  needed to apply the (freshness-conditioned) @{text FixBeta} and @{text Let} beta rules.\<close>

lemma Fix_refresh:
  fixes Q :: "'a::var term"
  assumes "finite A"
  shows "\<exists>f' x' Q'. Fix f x Q = Fix f' x' Q' \<and> f' \<notin> A \<and> x' \<notin> A"
proof -
  have b1: "|{f, x}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  have b2: "|{f, x} \<union> FVars Q \<union> A| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: assms)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` {f, x} \<inter> ({f, x} \<union> FVars Q \<union> A) = {}"
      "id_on (FVars Q - {x, f}) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars Q - {x, f}"]
    by (auto simp: insert_commute)
  have eq: "Fix f x Q = Fix (g f) (g x) (permute_term g Q)"
    using g by (auto intro!: exI[of _ g])
  show ?thesis
    by (rule exI[of _ "g f"], rule exI[of _ "g x"], rule exI[of _ "permute_term g Q"])
      (use eq g(3) in auto)
qed

lemma Let_refresh:
  fixes M1 M2 :: "'a::var term"
  assumes "finite A"
  shows "\<exists>xy' M2'. term.Let xy M1 M2 = term.Let xy' M1 M2' \<and> dset xy' \<inter> A = {}"
proof -
  have b1: "|dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|dset xy \<union> FVars M2 \<union> A| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: assms finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> (dset xy \<union> FVars M2 \<union> A) = {}"
      "id_on (FVars M2 - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M2 - dset xy"] by auto
  have eq: "term.Let xy M1 M2 = term.Let (dmap g xy) M1 (permute_term g M2)"
    using g by (auto intro!: exI[of _ g])
  have disj: "dset (dmap g xy) \<inter> A = {}"
    using g(3) unfolding dpair.set_map[OF g(1,2)] by blast
  show ?thesis using eq disj by blast
qed

text \<open>Progress: every term is a value, stuck, or steps. The original (never-compiling)
  proof attempt used the nonexistent \<open>stuck.intros\<close>; moreover the lemma was FALSE before
  the missing @{text Pred} rule was added to @{text stuckEx} (see above). The @{text FixBeta}
  and @{text Let} cases alpha-refresh the binders to satisfy the freshness side conditions.\<close>

lemma val_stuck_step: "val M \<or> stuck M \<or> (\<exists>N. M \<rightarrow> N)"
proof (binder_induction M avoiding: M rule: term_strong_induct, goal_cases)
  case 1
  show ?case using val.intros(2) num.intros(1) by blast
next
  case (2 M1)
  then consider (v) "val M1" | (s) "stuck M1" | (r) N where "M1 \<rightarrow> N" by blast
  then show ?case
  proof cases
    case v
    show ?thesis
    proof (cases "num M1")
      case True
      then show ?thesis using val.intros(2) num.intros(2) by blast
    next
      case False
      then show ?thesis using v stuckEx.intros(1) stuckEx_imp_stuck by blast
    qed
  next
    case s
    then obtain E hole st where "eval_ctx hole E" "E[st <- hole] = M1" "stuckEx st"
      unfolding stuck_def by blast
    then have "eval_ctx hole (Succ E)" "(Succ E)[st <- hole] = Succ M1"
      using eval_ctx.intros(4) by auto
    then show ?thesis using \<open>stuckEx st\<close> unfolding stuck_def by blast
  next
    case r
    then show ?thesis using beta.OrdSucc by blast
  qed
next
  case (3 M1)
  then consider (v) "val M1" | (s) "stuck M1" | (r) N where "M1 \<rightarrow> N" by blast
  then show ?case
  proof cases
    case v
    show ?thesis
    proof (cases "num M1")
      case True
      then show ?thesis by (metis beta.PredS beta.PredZ num.cases)
    next
      case False
      then show ?thesis using v stuckEx.intros(5) stuckEx_imp_stuck by blast
    qed
  next
    case s
    then obtain E hole st where "eval_ctx hole E" "E[st <- hole] = M1" "stuckEx st"
      unfolding stuck_def by blast
    then have "eval_ctx hole (Pred E)" "(Pred E)[st <- hole] = Pred M1"
      using eval_ctx.intros(5) by auto
    then show ?thesis using \<open>stuckEx st\<close> unfolding stuck_def by blast
  next
    case r
    then show ?thesis using beta.OrdPred by blast
  qed
next
  case (4 M1 N1 P1)
  then consider (v) "val M1" | (s) "stuck M1" | (r) N where "M1 \<rightarrow> N" by blast
  then show ?case
  proof cases
    case v
    show ?thesis
    proof (cases "num M1")
      case True
      then show ?thesis by (metis beta.Ifs beta.Ifz num.cases)
    next
      case False
      then show ?thesis using v stuckEx.intros(2) stuckEx_imp_stuck by blast
    qed
  next
    case s
    then obtain hole E st where h: "eval_ctx hole E" "M1 = E[st <- hole]" "stuckEx st"
        "hole \<notin> FVars N1 \<union> FVars P1"
      using stuck_fresh_hole[of M1 "FVars N1 \<union> FVars P1"] by auto
    then have "eval_ctx hole (If E N1 P1)" "(If E N1 P1)[st <- hole] = If M1 N1 P1"
      using eval_ctx.intros(9) by auto
    then show ?thesis using h(3) unfolding stuck_def by blast
  next
    case r
    then show ?thesis using beta.OrdIf by blast
  qed
next
  case (5 x)
  show ?case using val.intros(1) by blast
next
  case (6 M1 M2)
  from 6(1) consider (v) "val M1" | (s) "stuck M1" | (r) N where "M1 \<rightarrow> N" by blast
  then show ?case
  proof cases
    case r
    then show ?thesis using beta.OrdApp1 by blast
  next
    case s
    then obtain hole E st where h: "eval_ctx hole E" "M1 = E[st <- hole]" "stuckEx st"
        "hole \<notin> FVars M2"
      using stuck_fresh_hole[of M1 "FVars M2"] by auto
    then have "eval_ctx hole (App E M2)" "(App E M2)[st <- hole] = App M1 M2"
      using eval_ctx.intros(3) by auto
    then show ?thesis using h(3) unfolding stuck_def by blast
  next
    case v
    show ?thesis
    proof (cases "is_Fix M1")
      case False
      then show ?thesis using v stuckEx.intros(3) stuckEx_imp_stuck by blast
    next
      case True
      then obtain f x Q where fix1: "M1 = Fix f x Q" unfolding is_Fix_def by blast
      from 6(2) consider (v2) "val M2" | (s2) "stuck M2" | (r2) N where "M2 \<rightarrow> N" by blast
      then show ?thesis
      proof cases
        case r2
        then show ?thesis using beta.OrdApp2 fix1 by blast
      next
        case s2
        then obtain hole E st where h: "eval_ctx hole E" "M2 = E[st <- hole]" "stuckEx st"
            "hole \<notin> FVars Q"
          using stuck_fresh_hole[of M2 "FVars Q"] by auto
        then have "hole \<notin> FVars (Fix f x Q)" by auto
        then have "eval_ctx hole (App (Fix f x Q) E)"
            "(App (Fix f x Q) E)[st <- hole] = App M1 M2"
          using eval_ctx.intros(2)[OF h(1), of Q f x] h fix1 by auto
        then show ?thesis using h(3) unfolding stuck_def by blast
      next
        case v2
        obtain f' x' Q' where r: "Fix f x Q = Fix f' x' Q'" "f' \<notin> FVars M2" "x' \<notin> FVars M2"
          using Fix_refresh[of "FVars M2" f x Q] by auto
        then have "App M1 M2 \<rightarrow> Q'[M2 <- x'][Fix f' x' Q' <- f']"
          using beta.FixBeta[OF v2 r(2)] fix1 by metis
        then show ?thesis by blast
      qed
    qed
  qed
next
  case (7 f x Q)
  show ?case using val.intros(4) by blast
next
  case (8 M1 M2)
  from 8(1) consider (v) "val M1" | (s) "stuck M1" | (r) N where "M1 \<rightarrow> N" by blast
  then show ?case
  proof cases
    case r
    then show ?thesis using beta.OrdPair1 by blast
  next
    case s
    then obtain hole E st where h: "eval_ctx hole E" "M1 = E[st <- hole]" "stuckEx st"
        "hole \<notin> FVars M2"
      using stuck_fresh_hole[of M1 "FVars M2"] by auto
    then have "eval_ctx hole (Pair E M2)" "(Pair E M2)[st <- hole] = Pair M1 M2"
      using eval_ctx.intros(6) by auto
    then show ?thesis using h(3) unfolding stuck_def by blast
  next
    case v
    from 8(2) consider (v2) "val M2" | (s2) "stuck M2" | (r2) N where "M2 \<rightarrow> N" by blast
    then show ?thesis
    proof cases
      case r2
      then show ?thesis using beta.OrdPair2[OF v] by blast
    next
      case s2
      then obtain hole E st where h: "eval_ctx hole E" "M2 = E[st <- hole]" "stuckEx st"
          "hole \<notin> FVars M1"
        using stuck_fresh_hole[of M2 "FVars M1"] by auto
      then have "eval_ctx hole (Pair M1 E)" "(Pair M1 E)[st <- hole] = Pair M1 M2"
        using eval_ctx.intros(7)[OF v] by auto
      then show ?thesis using h(3) unfolding stuck_def by blast
    next
      case v2
      then show ?thesis using val.intros(3)[OF v v2] by blast
    qed
  qed
next
  case (9 xy M1 M2)
  from 9(2) consider (v) "val M1" | (s) "stuck M1" | (r) N where "M1 \<rightarrow> N" by blast
  then show ?case
  proof cases
    case r
    then show ?thesis using beta.OrdLet by blast
  next
    case s
    obtain xy' M2' where eq: "term.Let xy M1 M2 = term.Let xy' M1 M2'"
        and fresh: "dset xy' \<inter> (FVars M1 \<union> FVars M2) = {}"
      using Let_refresh[of "FVars M1 \<union> FVars M2" xy M1 M2] by auto
    obtain hole E st where h: "eval_ctx hole E" "M1 = E[st <- hole]" "stuckEx st"
        "hole \<notin> FVars M2' \<union> dset xy' \<union> FVars M1"
      using stuck_fresh_hole[OF s, of "FVars M2' \<union> dset xy' \<union> FVars M1"] finite_dset by auto
    have stM1: "FVars st \<subseteq> FVars M1" and EM1: "FVars E \<subseteq> FVars M1 \<union> {hole}"
      using h(2) eval_ctxt_FVars[OF h(1)] by (auto simp: FVars_usubst)
    have ctxL: "eval_ctx hole (term.Let xy' E M2')"
      by (rule eval_ctx.intros(8)[OF h(1)]) (use h(4) in auto)
    have push: "(term.Let xy' E M2')[st <- hole] = term.Let xy' M1 M2'"
      by (subst usubst_simps(9)) (use h(2,4) stM1 EM1 fresh in \<open>auto simp: disjoint_iff\<close>)
    show ?thesis using ctxL push h(3) eq unfolding stuck_def by metis
  next
    case v
    show ?thesis
    proof (cases "is_Pair M1")
      case False
      then show ?thesis using v stuckEx.intros(4) stuckEx_imp_stuck by blast
    next
      case True
      then obtain V W where pair1: "M1 = Pair V W" unfolding is_Pair_def by blast
      have vVW: "val V" "val W"
        using v unfolding pair1 by (auto 0 3 elim: val.cases num.cases)
      obtain xy' M2' where eq: "term.Let xy M1 M2 = term.Let xy' M1 M2'"
          and fresh: "dset xy' \<inter> FVars V = {}"
        using Let_refresh[of "FVars V" xy M1 M2] by auto
      have "term.Let xy' M1 M2' \<rightarrow> M2'[V <- dfst xy'][W <- dsnd xy']"
        using beta.Let[OF vVW fresh] unfolding pair1 by blast
      then show ?thesis using eq by metis
    qed
  qed
qed


section \<open>Judgements\<close>

type_synonym 'var typing = "'var term \<times> type"
notation Product_Type.Pair (infix ":." 70)

inductive disjunction :: "type \<Rightarrow> type \<Rightarrow> bool" (infix "||" 70) where
  "Nat || Prod _ _"
| "Nat || To _  _"
| "Nat || OnlyTo _  _"
| "Prod _ _ || To _ _"
| "Prod _ _ || OnlyTo _  _"
| "A || B \<Longrightarrow> B || A"

notation finsert (infixr ";" 50)

text \<open>Free variables of a context (an fset of typings): the union of the free variables of the
  term components, i.e.\ \<open>\<Union> (FVars ` fst ` fset \<Gamma>)\<close>. This is exactly the support that the
  \<open>binder_inductive\<close> refreshability obligation for the \<open>judgement\<close> relation (defined below) computes
  for its \<open>'a typing fset\<close> arguments.\<close>
definition FVarsC :: "('v::var) typing fset \<Rightarrow> 'v set" where
  "FVarsC G = \<Union> (FVars ` fst ` fset G)"

lemma FVarsC_simps[simp]:
  "FVarsC {||} = {}"
  "FVarsC (finsert (t, ty) G) = FVars t \<union> FVarsC G"
  by (auto simp: FVarsC_def)

lemma FVarsC_raw: "\<Union> (FVars ` fst ` fset G) = FVarsC G"
  by (simp add: FVarsC_def)

inductive judgement :: "'var::var typing fset \<Rightarrow> 'var::var typing fset \<Rightarrow> bool" (infix "\<turnstile>" 10) where
  Id : "(Var x :. A) ; \<Gamma> \<turnstile> (Var x :. A) ; \<Delta>"
| ZeroR : "\<Gamma> \<turnstile> (Zero :. Nat) ; \<Delta>"
| SuccR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Succ M :. Nat) ; \<Delta>"
| PredR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Pred M :. Nat) ; \<Delta>"
| FixsR: "(Var f :. To A B) ; (Var x :. A) ; \<Gamma> \<turnstile> (M :. B) ; \<Delta> \<Longrightarrow> {f, x} \<inter> (FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> \<Gamma> \<turnstile> (Fix f x M :. To A B) ; \<Delta>"
| FixnR: "(Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma> \<turnstile> (Var x :. A) ; \<Delta> \<Longrightarrow> {f, x} \<inter> (FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> \<Gamma> \<turnstile> (Fix f x M :. OnlyTo A B) ; \<Delta>"
| AppR: "(M :. To B A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. B) ; \<Delta> \<Longrightarrow>  \<Gamma>  \<turnstile> (App M N :. A) ; \<Delta>"
| PairR: "\<Gamma> \<turnstile> (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. B) ; \<Delta> \<Longrightarrow>  \<Gamma>  \<turnstile> (Pair M N :. Prod A B) ; \<Delta>"
| LetR: "(M :. Prod B C) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma> \<turnstile> (N :. A) ; \<Delta> \<Longrightarrow> dset x \<inter> (FVarsC \<Gamma> \<union> FVarsC \<Delta> \<union> FVars M) = {} \<Longrightarrow> \<Gamma> \<turnstile> (Let x M N :. A) ; \<Delta>"
| IfzR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (P :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (If M N P :. A) ; \<Delta>"
| Dis: "A || B \<Longrightarrow> \<Gamma> \<turnstile> (M :. B) ; \<Delta> \<Longrightarrow> (M :. A); \<Gamma> \<turnstile> \<Delta>"
| PairL1: "(M :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M N :. Prod A B) ; \<Gamma> \<turnstile> \<Delta>"
| AppL: "(M :. OnlyTo B A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. B) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| SuccL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Succ M :. Nat) ; \<Gamma> \<turnstile> \<Delta>"
| PredL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pred M :. Nat) ; \<Gamma> \<turnstile> \<Delta>"
| IfzL1: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile> \<Delta>"
| IfzL2: "(N :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (P :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL1: "(N :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> dset x \<inter> (FVars M \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL2_1: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. A) ; \<Gamma> \<turnstile> (Var (dfst x) :. B1) ; \<Delta> \<Longrightarrow> dset x \<inter> (FVars M \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL2_2: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. A) ; \<Gamma> \<turnstile> (Var (dsnd x) :. B1) ; \<Delta> \<Longrightarrow> dset x \<inter> (FVars M \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| OkVarR: "\<Gamma> \<turnstile> (Var x :. Ok) ; \<Delta>"
| OkL: "(M :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile> \<Delta>"
| OkR: "\<Gamma> \<turnstile> (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (M :. Ok) ; \<Delta>"
| OkApL1: "(M :. OnlyTo Ok A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkApL2: "(N :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkSL: "(M :. Nat); \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Succ M :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pred M :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPrL_1: "(M1 :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPrL_2: "(M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta>"

lemmas [equiv] = term.permute map_prod_simp

lemma finsert_map_prod_equiv[equiv]:
  fixes f :: "'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "fimage (map_prod (permute_term f) id) (finsert p G)
       = finsert (map_prod (permute_term f) id p) (fimage (map_prod (permute_term f) id) G)"
  by simp

lemma fimage_map_prod_cancel[equiv]:
  fixes f :: "'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "fimage (map_prod (permute_term (inv f)) id) (fimage (map_prod (permute_term f) id) G) = G"
proof -
  have "(map_prod (permute_term (inv f)) id \<circ> map_prod (permute_term f) id) x = id x"
    for x :: "'a typing"
    by (cases x)
       (simp add: term.permute_comp[OF assms bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
          inv_o_simp1[OF assms(1)] term.permute_id)
  then have "map_prod (permute_term (inv f)) id \<circ> map_prod (permute_term f) id = id" by auto
  then show ?thesis by (metis fset.map_comp fset.map_id)
qed

text \<open>Composed-image variant of @{thm fimage_map_prod_cancel}: during the equivariance proof the
  two @{const fimage}s get fused by @{thm fset.map_comp} into a single \<open>(g \<circ> h) |`| G\<close>, which
  no longer matches the nested form, so we need this shape too.\<close>
lemma fimage_map_prod_o_cancel[equiv]:
  fixes f :: "'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "(map_prod (permute_term (inv f)) id \<circ> map_prod (permute_term f) id) |`| G = G"
  by (metis fimage_map_prod_cancel[OF assms] fset.map_comp)

lemma permute_term_inv_cancel[equiv]:
  fixes f :: "'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_term (inv f) (permute_term f N) = N"
  by (simp add: term.permute_comp[OF assms bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
        inv_o_simp1[OF assms(1)] term.permute_id)

lemmas [equiv] = dfst_dmap dsnd_dmap

text \<open>Equivariance of the context free-variable operator, needed so that the automatic
  equivariance proof can discharge the freshness side conditions of the binding rules.\<close>
lemma FVarsC_permute[equiv]:
  fixes \<sigma> :: "'v::var \<Rightarrow> 'v"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'v set|"
  shows "FVarsC (map_prod (permute_term \<sigma>) id |`| \<Gamma>) = \<sigma> ` FVarsC \<Gamma>"
  unfolding FVarsC_def
  by (auto simp: term.FVars_permute[OF assms] image_image map_prod_def split_beta image_UN)

text \<open>Refreshability holds trivially with @{term "B' = B"}: the freshness side conditions on the
  binding rules (@{text FixsR}, @{text FixnR}, @{text LetR}, @{text LetL1}, @{text LetL2_1},
  @{text LetL2_2}) state exactly that the bound variables avoid the free variables of the ambient
  context, i.e.\ that @{term B} is already disjoint from the support the obligation computes. For the
  non-binding rules @{term "B = {}"}. Equivariance is discharged automatically via the @{text equiv}
  simp set.\<close>
binder_inductive (no_auto_equiv) judgement
  subgoal premises prems for R B \<sigma> x1 x2 \<comment> \<open>equivariance\<close>
    supply SET = prems(1,2) term.permute[OF prems(1,2)]
        term.permute[OF bij_imp_bij_inv[OF prems(1)] supp_inv_bound[OF prems(1,2)]]
        term.FVars_permute[OF prems(1,2)] FVarsC_permute[OF prems(1,2)]
        finsert_map_prod_equiv[OF prems(1,2)] fimage_map_prod_cancel[OF prems(1,2)]
        fimage_map_prod_o_cancel[OF prems(1,2)]
        permute_term_inv_cancel[OF prems(1,2)] dpair.set_map[OF prems(1)]
        dfst_dmap[OF prems(1)] dsnd_dmap[OF prems(1)]
        inj_image_mem_iff[OF bij_is_inj[OF prems(1)]] inj_eq[OF bij_is_inj[OF prems(1)]]
        image_Int[OF bij_is_inj[OF prems(1)], symmetric] inv_f_f[OF bij_is_inj[OF prems(1)]]
    unfolding Tperm2_judgement_def Tperm1_judgement_def
    \<comment> \<open>Insert the rule disjunction as a goal premise, then split it incrementally with
      @{method erule}~@{text disjE}, proving each rule case before splitting off the next. This keeps
      the (huge) transported goal in at most two subgoals at a time, avoiding the blow-up of a single
      @{method elim} into 29 copies. (@{method erule} needs the disjunction among the goal premises,
      not merely chained, hence the @{method insert} rather than \<open>using\<close>.)\<close>
    apply (insert prems(3))
    apply (erule disjE) subgoal \<comment> \<open>Id\<close>
      apply (elim exE conjE) subgoal for x A \<Gamma> \<Delta>
        by (rule disjI1, rule exI[of _ "\<sigma> x"], rule exI[of _ A],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>ZeroR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> \<Delta>
        by (rule disjI2, rule disjI1, rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>SuccR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> M \<Delta>
        by (rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "permute_term \<sigma> M"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>PredR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> M \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "permute_term \<sigma> M"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>FixsR\<close>
      apply (elim exE conjE) subgoal for f A Ba x \<Gamma> M \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "\<sigma> f"], rule exI[of _ A], rule exI[of _ Ba], rule exI[of _ "\<sigma> x"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "permute_term \<sigma> M"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>FixnR\<close>
      apply (elim exE conjE) subgoal for f A Ba M \<Gamma> x \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "\<sigma> f"], rule exI[of _ A], rule exI[of _ Ba], rule exI[of _ "permute_term \<sigma> M"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "\<sigma> x"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>AppR\<close>
      apply (elim exE conjE) subgoal for M Ba A \<Gamma> \<Delta> N
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ Ba], rule exI[of _ A],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"],
            rule exI[of _ "permute_term \<sigma> N"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>PairR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> M A \<Delta> N Ba
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ A],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ Ba]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>LetR\<close>
      apply (elim exE conjE) subgoal for M Ba C \<Gamma> \<Delta> x N A
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ Ba], rule exI[of _ C],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"],
            rule exI[of _ "dmap \<sigma> x"], rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ A]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>IfzR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> M \<Delta> P A N
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "permute_term \<sigma> M"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> P"], rule exI[of _ A],
            rule exI[of _ "permute_term \<sigma> N"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>Dis\<close>
      apply (elim exE conjE) subgoal for A Ba \<Gamma> M \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ A], rule exI[of _ Ba], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>PairL1\<close>
      apply (elim exE conjE) subgoal for M A \<Gamma> \<Delta> N Ba
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ A], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ Ba]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>AppL\<close>
      apply (elim exE conjE) subgoal for M Ba A \<Gamma> \<Delta> N
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ Ba], rule exI[of _ A], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> N"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>SuccL\<close>
      apply (elim exE conjE) subgoal for M \<Gamma> \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>PredL\<close>
      apply (elim exE conjE) subgoal for M \<Gamma> \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>IfzL1\<close>
      apply (elim exE conjE) subgoal for M \<Gamma> \<Delta> N P A
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> N"],
            rule exI[of _ "permute_term \<sigma> P"], rule exI[of _ A]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>IfzL2\<close>
      apply (elim exE conjE) subgoal for N A \<Gamma> \<Delta> P M
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ A], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> P"],
            rule exI[of _ "permute_term \<sigma> M"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>LetL1\<close>
      apply (elim exE conjE) subgoal for N A \<Gamma> \<Delta> x M
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ A],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"],
            rule exI[of _ "dmap \<sigma> x"], rule exI[of _ "permute_term \<sigma> M"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>LetL2_1\<close>
      apply (elim exE conjE) subgoal for M B1 B2 \<Gamma> \<Delta> N A x
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ B1], rule exI[of _ B2],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"],
            rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ A], rule exI[of _ "dmap \<sigma> x"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>LetL2_2\<close>
      apply (elim exE conjE) subgoal for M B1 B2 \<Gamma> \<Delta> N A x
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ B1], rule exI[of _ B2],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"],
            rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ A], rule exI[of _ "dmap \<sigma> x"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkVarR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> x \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "\<sigma> x"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkL\<close>
      apply (elim exE conjE) subgoal for M \<Gamma> \<Delta> A
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ A]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkR\<close>
      apply (elim exE conjE) subgoal for \<Gamma> M A \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"], rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ A],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkApL1\<close>
      apply (elim exE conjE) subgoal for M A \<Gamma> \<Delta> N
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ A], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> N"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkApL2\<close>
      apply (elim exE conjE) subgoal for N \<Gamma> \<Delta> M
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> N"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> M"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkSL\<close>
      apply (elim exE conjE) subgoal for M \<Gamma> \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkPL\<close>
      apply (elim exE conjE) subgoal for M \<Gamma> \<Delta>
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"]) (auto simp: SET) done
    apply (erule disjE) subgoal \<comment> \<open>OkPrL_1\<close>
      apply (elim exE conjE) subgoal for M1 \<Gamma> \<Delta> M2
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1,
            rule exI[of _ "permute_term \<sigma> M1"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> M2"]) (auto simp: SET) done
    subgoal \<comment> \<open>OkPrL_2\<close>
      apply (elim exE conjE) subgoal for M2 \<Gamma> \<Delta> M1
        by (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2,
            rule exI[of _ "permute_term \<sigma> M2"], rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Gamma>"],
            rule exI[of _ "map_prod (permute_term \<sigma>) id |`| \<Delta>"], rule exI[of _ "permute_term \<sigma> M1"]) (auto simp: SET) done
    done
  subgoal premises prems for R B x1 x2 \<comment> \<open>refreshability\<close>
    apply (rule exI[of _ B])
    apply (rule conjI)
    subgoal
      using prems(3) by (elim disjE exE conjE) (auto simp: FVarsC_def)
    subgoal
      by (rule prems(3))
    done
  done

thm judgement.strong_induct judgement.equiv

lemma weakenL: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile> \<Delta>"
  apply (binder_induction \<Gamma> \<Delta> avoiding: M rule: judgement.strong_induct)
  apply (auto intro: judgement.intros simp add: finsert_commute[of "M :. A" _] FVarsC_def Int_Un_distrib)
  \<comment> \<open>the four @{const Let} cases: @{method auto} does not pick the right rule among the 29 intros,
    so apply it explicitly (premises are already in the induction hypotheses; the freshness of the
    binder w.r.t. the extra @{term M} comes from @{text avoiding})\<close>
  subgoal by (rule judgement.LetR) (auto simp: FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetL1) (auto simp: FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetL2_1) (auto simp: FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetL2_2) (auto simp: FVarsC_def Int_Un_distrib)
  done

lemma weakenR: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma>  \<turnstile> (M :. A) ; \<Delta>"
  apply (binder_induction \<Gamma> \<Delta> avoiding: M rule: judgement.strong_induct)
  apply (auto intro: judgement.intros simp add: finsert_commute[of "M :. A" _] FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetR) (auto simp: FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetL1) (auto simp: FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetL2_1) (auto simp: FVarsC_def Int_Un_distrib)
  subgoal by (rule judgement.LetL2_2) (auto simp: FVarsC_def Int_Un_distrib)
  done

section \<open>Semantics\<close>

definition "Vals0 = {V. val V}"

fun
  type_semantics :: "type \<Rightarrow> 'var :: var term set" ("\<lblot>_\<rblot>" 90) and
  tau_semantics :: "type \<Rightarrow> 'var :: var term set" ("\<T>\<lblot>_\<rblot>" 90) and 
  bottom_semantics :: "type \<Rightarrow> 'var :: var term set" ("\<T>\<^sub>\<bottom>\<lblot>_\<rblot>" 90) where
  "\<lblot>Ok\<rblot> = Vals0"
| "\<lblot>Nat\<rblot> = {V. num V}"
| "\<lblot>Prod A B\<rblot> = case_prod Pair ` (\<lblot>A\<rblot> \<times> \<lblot>B\<rblot>)"
| "\<lblot>To A B\<rblot> = {Fix f x M | f x M. \<forall>V \<in> Vals0. FVars V = {} \<longrightarrow> V \<in> \<lblot>A\<rblot> \<longrightarrow> M[V <- x][Fix f x M <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>}"
| "\<lblot>OnlyTo A B\<rblot> = {Fix f x M | f x M. \<forall>V \<in> Vals0. FVars V = {} \<longrightarrow> M[V <- x][Fix f x M <- f] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> V \<in> \<lblot>A\<rblot>}"
| "\<T>\<lblot>A\<rblot> = {M. \<exists>V \<in> \<lblot>A\<rblot>. M \<rightarrow>* V \<and> val V}"
| "\<T>\<^sub>\<bottom>\<lblot>A\<rblot> = {M. M \<in> \<T>\<lblot>A\<rblot> \<or> (M \<Up>)}"

type_synonym 'var valuation = "('var \<times> 'var term) list"

fun eval :: "'var::var valuation \<Rightarrow> 'var term \<Rightarrow> 'var term" where
  "eval Nil M = M"
| "eval ((x,t) # ps) M = eval ps (M[t <- x])"

text \<open>Definition 4.2 (Semantics of Judgements). A valuation is a substitution mapping variables to
  \<^emph>\<open>closed values\<close> (the proof of the @{text OkVarR} case of Theorem 4.8 requires that \<open>x\<theta>\<close> is a
  value, and the whole semantics lives on closed terms); it is applied sequentially, which is
  unproblematic since the images are closed. A valuation satisfies a formula \<open>M : A\<close> on the left
  if \<open>M\<theta> \<in> \<T>\<lblot>A\<rblot>\<close>, and on the right if \<open>M\<theta> \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>\<close>. It satisfies \<open>\<Gamma>\<close> on the left if it
  satisfies \<^emph>\<open>every\<close> formula of \<open>\<Gamma>\<close> on the left, and \<open>\<Delta>\<close> on the right if it satisfies \<^emph>\<open>some\<close>
  formula of \<open>\<Delta>\<close> on the right (the two sides of a sequent are conjunctive resp.\ disjunctive).
  Following the paper, only valuations that close all the terms involved are considered.\<close>

definition closed_val_subst :: "'var::var valuation \<Rightarrow> bool" where
  "closed_val_subst \<theta> \<longleftrightarrow> (\<forall>p \<in> set \<theta>. val (snd p) \<and> FVars (snd p) = {})"

definition satL :: "'var::var valuation \<Rightarrow> 'var typing \<Rightarrow> bool" where
  "satL \<theta> \<tau> \<longleftrightarrow> eval \<theta> (fst \<tau>) \<in> \<T>\<lblot>snd \<tau>\<rblot>"

definition satR :: "'var::var valuation \<Rightarrow> 'var typing \<Rightarrow> bool" where
  "satR \<theta> \<tau> \<longleftrightarrow> eval \<theta> (fst \<tau>) \<in> \<T>\<^sub>\<bottom>\<lblot>snd \<tau>\<rblot>"

definition closes :: "'var::var valuation \<Rightarrow> 'var typing fset \<Rightarrow> bool" where
  "closes \<theta> G \<longleftrightarrow> (\<forall>\<tau>. \<tau> |\<in>| G \<longrightarrow> FVars (eval \<theta> (fst \<tau>)) = {})"

definition semantic_judgement :: "'var::var typing fset \<Rightarrow> 'var typing fset \<Rightarrow> bool"
  (infix "\<Turnstile>" 10) where
  "(L \<Turnstile> R) \<longleftrightarrow> (\<forall>\<theta>. closed_val_subst \<theta> \<longrightarrow> closes \<theta> (L |\<union>| R) \<longrightarrow>
     (\<forall>\<tau>. \<tau> |\<in>| L \<longrightarrow> satL \<theta> \<tau>) \<longrightarrow> (\<exists>\<tau>. \<tau> |\<in>| R \<and> satR \<theta> \<tau>))"

section \<open>B2\<close>

lemma subst_Zero_inversion:
  assumes "M[t <- x] = Zero" and "\<not> M = Var x"
  shows "M = Zero"
  using assms
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros Int_Un_distrib split:if_splits)
  done

lemma subst_Var_inversion:
  assumes "M[t <- x] = Var y" and "\<not> M = Var x"
  shows "M = Var y"
  using assms
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
          apply(auto simp add:eval_ctx.intros Int_Un_distrib split:if_splits)
  done

lemma subst_Succ_inversion: 
  assumes "M[t <- x] = Succ N" and "\<not> M = Var x"
  obtains N' where "M = Succ N'" and "N = N'[t <- x]"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros Int_Un_distrib split:if_splits)
  done

lemma subst_Pred_inversion: 
  assumes "M[t <- x] = Pred N" and "\<not> M = Var x"
  obtains N' where "M = Pred N'" and "N = N'[t <- x]"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
  apply(auto simp add:eval_ctx.intros Int_Un_distrib split:if_splits)
  done

lemma subst_App_inversion:
  assumes "M[t <- x] = App R Q" and "\<not> M = Var x"
  obtains R' Q' where "M = App R' Q'" and "R'[t <- x] = R" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term_strong_induct)
  apply(auto simp add:eval_ctx.intros Int_Un_distrib split:if_splits)
  done

lemma subst_Pair_inversion:
  assumes "M[t <- x] = Pair Q1 Q2" and "\<not> M = Var x"
  obtains Q1' Q2' where "M = Pair Q1' Q2'" and "Q1'[t <- x] = Q1" and "Q2'[t <- x] = Q2"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  done

lemma subst_If_inversion:
  assumes "M[t <- x] = If Q0 Q1 Q2" and "\<not> M = Var x"
  obtains Q0' Q1' Q2'
  where "M = If Q0' Q1' Q2'" and "Q0'[t <- x] = Q0" and "Q1'[t <- x] = Q1" and "Q2'[t <- x] = Q2"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  done

lemma subst_Fix_inversion:
  fixes M :: "'a::var term"
  assumes "M[t <- x] = Fix f z Q" and "\<not> M = Var x"
  assumes "f \<noteq> x" and "f \<notin> FVars t" and "x \<noteq> z" and "z \<notin> FVars t"
  obtains Q' where "M = Fix f z Q'" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x f z Q rule:term.strong_induct)
          apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  subgoal premises prems for x1 x2 x3 fa
  proof -
    note bfa = prems(16) and sfa = prems(17) and idfa = prems(18)
    have injfa: "\<And>a b. fa a = fa b \<Longrightarrow> a = b" using bfa by (simp add: bij_implies_inject)
    define \<sigma> where "\<sigma> \<equiv> x \<leftrightarrow> fa x"
    have bs: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
      unfolding \<sigma>_def by auto
    define f' where "f' \<equiv> \<sigma> \<circ> fa"
    have bf': "bij f'" unfolding f'_def using bfa bs(1) by (rule bij_comp)
    have sf': "|supp f'| <o |UNIV::'a set|"
      unfolding f'_def using sfa bs(2) by (metis supp_comp_bound infinite_UNIV)
    have faid: "\<And>y. y \<in> FVars x3 \<Longrightarrow> y \<noteq> x \<Longrightarrow> y \<notin> {x1, x2} \<Longrightarrow> fa y = y"
      using idfa unfolding id_on_def by (auto simp: FVars_usubst)
    have f'x1: "f' x1 = fa x1"
      unfolding f'_def \<sigma>_def using prems(12) injfa[of x1 x] prems(2) by (metis comp_apply swap_simps(3))
    have f'x2: "f' x2 = fa x2"
      unfolding f'_def \<sigma>_def using prems(14) injfa[of x2 x] prems(7) by (metis comp_apply swap_simps(3))
    have f'x: "f' x = x" unfolding f'_def \<sigma>_def by simp
    have f'other: "\<And>w. w \<in> FVars x3 \<Longrightarrow> w \<noteq> x \<Longrightarrow> w \<notin> {x1, x2} \<Longrightarrow> f' w = w"
    proof -
      fix w assume w: "w \<in> FVars x3" "w \<noteq> x" "w \<notin> {x1, x2}"
      then have faw: "fa w = w" using faid by auto
      have "w \<noteq> fa x" using injfa[of w x] faw w(2) by auto
      then show "f' w = w" unfolding f'_def \<sigma>_def using faw w(2) by simp
    qed
    have f'id: "id_on (FVars x3 - {x2, x1}) f'"
      unfolding id_on_def using f'other f'x by auto
    define Q' where "Q' \<equiv> permute_term f' x3"
    have ss_id: "\<sigma> \<circ> \<sigma> = id" unfolding \<sigma>_def by (rule ext) auto
    have comp_eq: "\<sigma> \<circ> f' = fa" unfolding f'_def comp_assoc[symmetric] ss_id by simp
    have pQ': "permute_term \<sigma> Q' = permute_term fa x3"
      unfolding Q'_def using term.permute_comp bs bf' sf' comp_eq by metis
    have faxQ': "fa x \<in> f' ` FVars x3 \<Longrightarrow> fa x = x"
    proof -
      assume "fa x \<in> f' ` FVars x3"
      then obtain w where w: "w \<in> FVars x3" and eq: "f' w = fa x" by auto
      show "fa x = x"
      proof (rule ccontr)
        assume nfx: "fa x \<noteq> x"
        have w1: "w \<noteq> x1" using f'x1 eq injfa[of x1 x] prems(2) by auto
        have w2: "w \<noteq> x2" using f'x2 eq injfa[of x2 x] prems(7) by auto
        have wx: "w \<noteq> x" using f'x eq nfx by auto
        have "f' w = w" using f'other w wx w1 w2 by auto
        then have "w = fa x" using eq by simp
        moreover have "fa w = w" using faid w wx w1 w2 by auto
        ultimately show False using injfa[of w x] wx by auto
      qed
    qed
    have idQ': "id_on (FVars Q' - {x}) \<sigma>"
    proof -
      have "\<And>y. y \<in> FVars Q' \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<sigma> y = y"
      proof -
        fix y assume y: "y \<in> FVars Q'" "y \<noteq> x"
        then have y3: "y \<in> f' ` FVars x3" unfolding Q'_def term.FVars_permute[OF bf' sf'] by auto
        show "\<sigma> y = y"
        proof (cases "fa x = x")
          case True then show ?thesis unfolding \<sigma>_def using y(2) by simp
        next
          case False
          then have "y \<noteq> fa x" using faxQ' y3 by metis
          then show ?thesis unfolding \<sigma>_def using y(2) by simp
        qed
      qed
      then show ?thesis unfolding id_on_def by auto
    qed
    have sx: "\<sigma> x = fa x" unfolding \<sigma>_def by simp
    have stepA: "(permute_term fa x3)[t <- fa x] = permute_term fa (x3[t <- x])"
    proof (cases "x \<in> FVars x3")
      case True
      have fat: "permute_term fa t = t"
      proof (rule term.permute_cong_id[OF bfa sfa])
        fix a assume "a \<in> FVars t"
        then have "a \<in> FVars (x3[t <- x]) - {x2, x1}" using True prems(1,6) by (auto simp: FVars_usubst)
        then show "fa a = a" using idfa unfolding id_on_def by auto
      qed
      show ?thesis unfolding permute_usubst[OF bfa sfa] fat ..
    next
      case False
      then have idle: "x3[t <- x] = x3" by simp
      have "fa x \<notin> FVars (permute_term fa x3)"
        unfolding term.FVars_permute[OF bfa sfa] using False injfa by auto
      then show ?thesis unfolding idle by simp
    qed
    have chain: "Q'[t <- x] = permute_term fa (x3[t <- x])"
      using premute_term_usubst[OF bs(1) bs(2) idQ'] pQ' sx stepA by metis
    show ?thesis
      apply (rule exI[of _ Q'], rule conjI)
       apply (rule exI[of _ f'])
       using bf' sf' f'id f'x1 f'x2 Q'_def apply blast
      using chain by simp
  qed
  done

lemma dpair_eqI: "dfst a = dfst b \<Longrightarrow> dsnd a = dsnd b \<Longrightarrow> a = (b::'a::infinite dpair)"
  by transfer auto

lemma subst_Let_inversion:
  fixes M :: "'a::var term"
  assumes "M[t <- x] = Let xy P Q" and "\<not> M = Var x"
  assumes "x \<notin> dset xy" and "FVars t \<inter> dset xy = {}"
  obtains P' Q' where "M = Let xy P' Q'" and "P'[t <- x] = P" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x "dfst xy" "dsnd xy" P Q rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  subgoal premises prems for x1 x2 x3 f
  proof -
    note bf = prems(12) and sf = prems(13) and idf = prems(14)
    have injf: "\<And>a b. f a = f b \<Longrightarrow> a = b" using bf by (simp add: bij_implies_inject)
    define \<sigma> where "\<sigma> \<equiv> x \<leftrightarrow> f x"
    have bs: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
      unfolding \<sigma>_def by auto
    define f' where "f' \<equiv> \<sigma> \<circ> f"
    have bf': "bij f'" unfolding f'_def using bf bs(1) by (rule bij_comp)
    have sf': "|supp f'| <o |UNIV::'a set|"
      unfolding f'_def using sf bs(2) by (metis supp_comp_bound infinite_UNIV)
    have fid: "\<And>y. y \<in> FVars x3 \<Longrightarrow> y \<noteq> x \<Longrightarrow> y \<notin> dset x1 \<Longrightarrow> f y = y"
      using idf unfolding id_on_def by (auto simp: FVars_usubst)
    have fd1x: "f (dfst x1) \<noteq> x" using prems(10) dsel_dset(1) dfst_dmap[OF bf] by metis
    have fd2x: "f (dsnd x1) \<noteq> x" using prems(10) dsel_dset(2) dsnd_dmap[OF bf] by metis
    have d1x: "dfst x1 \<noteq> x" and d2x: "dsnd x1 \<noteq> x" using prems(3) dsel_dset by blast+
    have f'd1: "f' (dfst x1) = f (dfst x1)"
      unfolding f'_def \<sigma>_def using fd1x injf[of "dfst x1" x] d1x by (metis comp_apply swap_simps(3))
    have f'd2: "f' (dsnd x1) = f (dsnd x1)"
      unfolding f'_def \<sigma>_def using fd2x injf[of "dsnd x1" x] d2x by (metis comp_apply swap_simps(3))
    have f'x: "f' x = x" unfolding f'_def \<sigma>_def by simp
    have f'other: "\<And>w. w \<in> FVars x3 \<Longrightarrow> w \<noteq> x \<Longrightarrow> w \<notin> dset x1 \<Longrightarrow> f' w = w"
    proof -
      fix w assume w: "w \<in> FVars x3" "w \<noteq> x" "w \<notin> dset x1"
      then have fw: "f w = w" using fid by auto
      have "w \<noteq> f x" using injf[of w x] fw w(2) by auto
      then show "f' w = w" unfolding f'_def \<sigma>_def using fw w(2) by simp
    qed
    have f'id: "id_on (FVars x3 - dset x1) f'"
      unfolding id_on_def using f'other f'x by auto
    have dm: "dmap f' x1 = dmap f x1"
      by (rule dpair_eqI) (simp_all add: dfst_dmap[OF bf'] dsnd_dmap[OF bf'] dfst_dmap[OF bf] dsnd_dmap[OF bf] f'd1 f'd2)
    define Q' where "Q' \<equiv> permute_term f' x3"
    have ss_id: "\<sigma> \<circ> \<sigma> = id" unfolding \<sigma>_def by (rule ext) auto
    have comp_eq: "\<sigma> \<circ> f' = f" unfolding f'_def comp_assoc[symmetric] ss_id by simp
    have pQ': "permute_term \<sigma> Q' = permute_term f x3"
      unfolding Q'_def using term.permute_comp bs bf' sf' comp_eq by metis
    have fxQ': "f x \<in> f' ` FVars x3 \<Longrightarrow> f x = x"
    proof -
      assume "f x \<in> f' ` FVars x3"
      then obtain w where w: "w \<in> FVars x3" and eq: "f' w = f x" by auto
      show "f x = x"
      proof (rule ccontr)
        assume nfx: "f x \<noteq> x"
        have w1: "w \<noteq> dfst x1" using f'd1 eq injf[of "dfst x1" x] d1x by auto
        have w2: "w \<noteq> dsnd x1" using f'd2 eq injf[of "dsnd x1" x] d2x by auto
        have wx: "w \<noteq> x" using f'x eq nfx by auto
        have wd: "w \<notin> dset x1" using w1 w2 dset_alt by auto
        have "f' w = w" using f'other w wx wd by auto
        then have "w = f x" using eq by simp
        moreover have "f w = w" using fid w wx wd by auto
        ultimately show False using injf[of w x] wx by auto
      qed
    qed
    have idQ': "id_on (FVars Q' - {x}) \<sigma>"
    proof -
      have "\<And>y. y \<in> FVars Q' \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<sigma> y = y"
      proof -
        fix y assume y: "y \<in> FVars Q'" "y \<noteq> x"
        then have y3: "y \<in> f' ` FVars x3" unfolding Q'_def term.FVars_permute[OF bf' sf'] by auto
        show "\<sigma> y = y"
        proof (cases "f x = x")
          case True then show ?thesis unfolding \<sigma>_def using y(2) by simp
        next
          case False
          then have "y \<noteq> f x" using fxQ' y3 by metis
          then show ?thesis unfolding \<sigma>_def using y(2) by simp
        qed
      qed
      then show ?thesis unfolding id_on_def by auto
    qed
    have sx: "\<sigma> x = f x" unfolding \<sigma>_def by simp
    have stepA: "(permute_term f x3)[t <- f x] = permute_term f (x3[t <- x])"
    proof (cases "x \<in> FVars x3")
      case True
      have ft: "permute_term f t = t"
      proof (rule term.permute_cong_id[OF bf sf])
        fix a assume "a \<in> FVars t"
        then have "a \<in> FVars (x3[t <- x]) - dset x1" using True prems(2) by (auto simp: FVars_usubst)
        then show "f a = a" using idf unfolding id_on_def by auto
      qed
      show ?thesis unfolding permute_usubst[OF bf sf] ft ..
    next
      case False
      then have idle: "x3[t <- x] = x3" by simp
      have "f x \<notin> FVars (permute_term f x3)"
        unfolding term.FVars_permute[OF bf sf] using False injf by auto
      then show ?thesis unfolding idle by simp
    qed
    have chain: "Q'[t <- x] = permute_term f (x3[t <- x])"
      using premute_term_usubst[OF bs(1) bs(2) idQ'] pQ' sx stepA by metis
    show ?thesis
      apply (rule exI[of _ x2], rule exI[of _ Q'], rule conjI)
       apply (rule exI[of _ f'])
       using bf' sf' f'id dm Q'_def apply blast
      using chain by simp
  qed
  done

lemma subst_num_inversion: "num m \<Longrightarrow> \<not> blocked z n \<Longrightarrow> n[N <- z] = m \<Longrightarrow> n = m"
proof (induction arbitrary: n rule:num.induct)
  case 1
  moreover have "n \<noteq> Var z" using blocked_inductive(1) \<open>\<not> blocked z n\<close> by auto
  ultimately show ?case using subst_Zero_inversion by auto
next
  case (2 m')
  obtain n' where "n = Succ n'" and "n'[N <- z] = m'" and "\<not> blocked z n'"
    using subst_Succ_inversion
    by (metis "2.prems"(1,2) blocked_inductive(1,4))
  then have "n' = m'" using "2.IH"[of n'] by auto 
  then show ?case
    by (simp add: \<open>n = Succ n'\<close>)
qed

lemma subst_val_inversion:
  assumes "val V" and "\<not> blocked z V'" and "V'[N <- z] = V"
  shows "val V'"
  using assms
proof(binder_induction V arbitrary: V' avoiding: N z rule:val.strong_induct)
  case (1 x V')
  then obtain y where "V' = Var y" using subst_Var_inversion by blast
  then show ?case using val.intros by auto
next
  case (2 n V')
  then show ?case using subst_num_inversion
    by (metis val.simps)
next
  case (3 V1 V2 V')
  obtain V1' V2' where "V' = Pair V1' V2'" and "V1'[N <- z] = V1" and "V2'[N <- z] = V2"
    using \<open>\<not> blocked z V'\<close>  subst_Pair_inversion 3 blocked_inductive(1) by blast
  then have "\<not> blocked z V1'"
    using blocked_inductive(6) \<open>\<not> blocked z V'\<close> by metis
  then have "val V1'" using \<open>V1'[N <- z] = V1\<close> "3.IH"(1)[of V1'] by auto
  then have "\<not> blocked z V2'"
    using blocked_inductive(7) \<open>\<not> blocked z V'\<close> \<open>V' = term.Pair V1' V2'\<close> by metis
  then have "val V2'" using \<open>V2'[N <- z] = V2\<close> "3.IH"(2)[of V2'] by auto
  show ?case using \<open>val V1'\<close> \<open>val V2'\<close> \<open>V' = Pair V1' V2'\<close> val.intros by auto
next
  case (4 f x M V')
  then obtain M' where "V' = Fix f x M'" and "M'[N <- z] = M"
    using subst_Fix_inversion[of V' N z f x M] blocked_inductive(1)
    by (metis Un_empty_right Un_insert_right insertCI insert_disjoint(2))
  then show ?case using val.intros by auto
qed

lemma FVars_subst_inversion: "(FVars M[N <- z] \<union> {z}) \<supseteq> FVars M"
  unfolding usubst_def
  by (auto simp: FVars_subst)

thm eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P) \<longrightarrow> M[N <- z] = E[P <- x] \<longrightarrow>
    x \<noteq> z \<longrightarrow>
    x \<notin> FVars M \<union> FVars P \<union> FVars N \<longrightarrow>
    \<not> blocked z M \<longrightarrow> (\<exists>F P'. M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z])"
    and K = "\<lambda>(z, N, M, E, x, P). {z,x} \<union> FVars N \<union> FVars M  \<union> FVars E \<union> FVars P",
    rule_format, rotated -5, of "(z, N, M, E, x, P)" M E x,
    simplified prod.inject simp_thms True_implies_equals]

lemma b2:
  assumes "eval_ctx x E"
    and "M[N <- z] = E[P <- x]"
    and "x \<noteq> z"
    and "x \<notin> FVars M \<union> FVars P \<union> FVars N"
    and "\<not> (blocked z M)"
  shows "\<exists>F P'. eval_ctx x F \<and> M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z]"
proof (rule eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P) \<longrightarrow> M[N <- z] = E[P <- x] \<longrightarrow>
    x \<noteq> z \<longrightarrow>
    x \<notin> FVars M \<union> FVars P \<union> FVars N \<longrightarrow>
    \<not> blocked z M \<longrightarrow> (\<exists>F P'. eval_ctx x F \<and> M = F[P' <- x] \<and> E = F[N <- z] \<and> P = P'[N <- z])"
    and K = "\<lambda>(z, N, M, E, x, P). {z,x} \<union> FVars N \<union> FVars M  \<union> FVars E \<union> FVars P",
    rule_format, rotated -5, of "(z, N, M, E, x, P)" M E x, OF _ assms(2,3,4,5,1),
    simplified prod.inject simp_thms True_implies_equals prod.case], goal_cases card 1 2 3 4 5 6 7 8 9)
case (card p)
then show ?case
  unfolding split_beta
  by (intro Un_bound infinite_UNIV ordLess_ordLeq_trans[OF term.set_bd var_class.large']) auto
next
  case (1 x p M)
  have "M[N <- z] = P" by (simp add: 1(2))
  obtain F P' where "F = Var x" "P' = M" by simp
  show ?case
    by (metis "1"(3) \<open>M[N <- z] = P\<close> eval_ctx.intros(1) usubst_simps(5))
next
  case (2 hole E Q f a p M)
  have "M[N <- z] = App (Fix f a Q) (E[P <- hole])" 
    using "2" by auto
  then obtain F R where "M = App F R" and "F[N <- z] = Fix f a Q" and "R[N <- z] = E[P <- hole]"
    using subst_App_inversion[of M N z "Fix f a Q" "E[P <- hole]"] "2"(9) blocked_inductive(1) by blast
  moreover have "\<not> blocked z F" using "2"(9) blocked_inductive(3) \<open>M = App F R\<close> by auto
  ultimately obtain Q' where "M = App (Fix f a Q') R" and "Q'[N <- z] = Q"
     using subst_Fix_inversion[of F N z f a Q] 2 blocked_inductive(1)[of z] by auto
  then have "\<not> blocked z R"
    using \<open>\<not> blocked z M\<close> blocked_inductive(2) by blast
  then obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- hole]" and "eval_ctx hole E'"
    using \<open>R[N <- z] = E[P <- hole]\<close> 2(3)[of "(z, N, R, E, hole, P)" R] 2(8) \<open>M = App F R\<close>
    by auto
  moreover have "hole \<notin> FVars Q'"
    using 2 \<open>hole \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = App (Fix f a Q') R\<close>
    by simp
  ultimately have "M = (App (Fix f a Q') E')[P' <- hole] \<and> App (Fix f a Q) E = (App (Fix f a Q') E')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = App (Fix f a Q') R\<close> \<open>Q'[N <- z] = Q\<close> \<open>R[N <- z] = E[P <- hole]\<close>
    by (metis "2"(8) Un_iff \<open>F[N <- z] = Fix f a Q\<close> \<open>M = App F R\<close> subst_idle
        term.inject(5) usubst_simps(6))
  also have "eval_ctx hole (App (Fix f a Q') E')" 
    using \<open>eval_ctx hole E'\<close> \<open>hole \<notin> FVars Q'\<close> eval_ctx.intros(2)[of hole E' Q'] by simp
  ultimately show ?case by metis
next
  case (3 x E Q p M)
  have "M[N <- z] = App (E[P <- x]) Q" using 3 by simp
  then obtain R Q' where "M = App R Q'" and "R[N <- z] = E[P <- x]" and "Q'[N <- z] = Q"
    using subst_App_inversion 3 blocked_inductive(1) by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z R"
    using \<open>M = App R Q'\<close> eval_ctx.intros(3) blocked_def blocked_inductive(3) by blast
  ultimately obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- x]" and "eval_ctx x E'"
    using 3(2)[where M = R] 3 by force
  moreover have "x \<notin> FVars Q'"
    using 3 \<open>x \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = App R Q'\<close>
    by simp
  ultimately have "M = (App E' Q')[P' <- x] \<and> App E Q = (App E' Q')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = App R Q'\<close> \<open>Q'[N <- z] = Q\<close> by simp
  also have "eval_ctx x (App E' Q')" using eval_ctx.intros \<open>eval_ctx x E'\<close> \<open>x \<notin> FVars Q'\<close> by blast
  ultimately show ?case by blast
next                                                                       
  case (4 x E p M)
  have "M[N <- z] = Succ(E[P <- x])" by (simp add: 4)
  then obtain Q where "M = Succ Q" and "Q[N <- z] = E[P <- x]" using subst_Succ_inversion 4
    blocked_inductive(1) by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using \<open>M = Succ Q\<close> eval_ctx.intros(4) blocked_def by (metis usubst_simps(2))
  ultimately
  obtain F' P' where "P'[N <- z] = P" and "E = F'[N <- z]" and "Q = F'[P' <- x]" and "eval_ctx x F'"
    using 4(2)[where M = Q] 4(1,3-) by auto
  then have "M = (Succ F')[P' <- x] \<and> Succ E = (Succ F')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = Succ Q\<close> by simp
  also have "eval_ctx x (Succ F')" using \<open>eval_ctx x F'\<close> eval_ctx.intros by blast
  ultimately show ?case by blast
next
  case (5 x E p M)
  have "M[N <- z] = Pred(E[P <- x])" by (simp add: 5)
  then obtain Q where "M = Pred Q" and "Q[N <- z] = E[P <- x]" using subst_Pred_inversion 5
    blocked_inductive(1) by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q" 
    using \<open>M = Pred Q\<close> eval_ctx.intros(5) blocked_def by (metis usubst_simps(3))
  ultimately
  obtain F' P' where "P'[N <- z] = P" and "E = F'[N <- z]" and "Q = F'[P' <- x]" and "eval_ctx x F'"
    using 5(2)[where M = Q] 5(1,3-) by auto
  then have "M = (Pred F')[P' <- x] \<and> Pred E = (Pred F')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = Pred Q\<close> by simp
  also have "eval_ctx x (Pred F')" using \<open>eval_ctx x F'\<close> eval_ctx.intros by blast
  ultimately show ?case by blast
next
  case (6 x E Q p M)
  have "M[N <- z] = Pair (E[P <- x]) Q"
    by (simp add: 6)
  then obtain Q1 Q2 where "M = Pair Q1 Q2" and "E[P <- x] = Q1[N <- z]" and "Q = Q2[N <- z]"
    using subst_Pair_inversion 6 blocked_inductive(1) by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q1" 
    using blocked_inductive(6) \<open>M = Pair Q1 Q2\<close> by metis
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q1 = E'[P' <- x]" and "eval_ctx x E'"
    using 6(2)[where M = Q] 6 by fastforce
   moreover have "x \<notin> FVars Q2"
    using 6 \<open>x \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = Pair Q1 Q2\<close>
    by simp
  ultimately have "M = (Pair E' Q2)[P' <- x] \<and> Pair E Q = (Pair E' Q2)[N <- z] \<and> P = P'[N <- z]"
    by (simp add: \<open>M = term.Pair Q1 Q2\<close> \<open>Q = Q2[N <- z]\<close>)
  also have "eval_ctx x (Pair E' Q2)" using \<open>eval_ctx x E'\<close> \<open>x \<notin> FVars Q2\<close> eval_ctx.intros(6) by metis
  ultimately show ?case by blast
next
  case (7 V x E p M)
  have "M[N <- z] = Pair V E[P <- x]"
    by(simp add: 7)
  then obtain V' Q where "M = Pair V' Q" and "V = V'[N <- z]" and "E[P <- x] = Q[N <- z]"
    using subst_Pair_inversion 7 blocked_inductive(1) by metis
  moreover have "\<not> blocked z Q" and "val V'"
    using blocked_inductive(7) \<open>M = Pair V' Q\<close> \<open>\<not> blocked z M\<close> subst_val_inversion
    using "7"(1) blocked_inductive(6) calculation(2)
     apply blast
    using "7"(1,9) blocked_inductive(6) calculation(1,2) subst_val_inversion by blast
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q = E'[P' <- x]" and "eval_ctx x E'"
    using 7(3)[where M = Q] 7 by fastforce
  moreover have "x \<notin> FVars V'"
    using 7 \<open>x \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = Pair V' Q\<close>
    by simp
  ultimately have "M = (Pair V' E')[P' <- x] \<and> Pair V E = (Pair V' E')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = term.Pair V' Q\<close> \<open>V = V'[N <- z]\<close> \<open>Q = E'[P' <- x]\<close> by simp
  also have "eval_ctx x (Pair V' E')" using \<open>eval_ctx x E'\<close> \<open>x \<notin> FVars V'\<close> \<open>val V'\<close> eval_ctx.intros(7) by metis
  ultimately show ?case by blast
next
  case (8 hole E Q x p M)
  have "M[N <- z] = Let x E[P <- hole] Q"
    using "8" usubst_simps(9)[of hole x P E Q]
    by fastforce
  then obtain R Q' where "M = Let x R Q'" and "Q'[N <- z] = Q" and "R[N <- z] = E[P <- hole]"
    using subst_Let_inversion[of M N z x "E[P <- hole]" Q] "8"(9,10) "8"(1) blocked_inductive(1)[of z]
    by blast
  moreover have "\<not> blocked z R" using "8"(1,9,10) blocked_inductive \<open>M = Let x R Q'\<close>
    by fastforce
  ultimately obtain E' P' where "P = P'[N <- z]" and "E = E'[N <- z]" and "R = E'[P' <- hole]" and "eval_ctx hole E'"
    using 8(3)[of "(z, N, R, E, hole, P)" R] 8(8,9)
    by (metis Un_iff term.set(9))
  moreover have "hole \<notin> FVars Q'"
    using 8 \<open>hole \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = Let x R Q'\<close>
    by simp
  moreover have "dset x \<inter> FVars E' = {}" and "dset x \<inter> FVars P' = {}"
    using FVars_subst_inversion[of E' N z] FVars_subst_inversion[of P' N z] 8(1) \<open>E = E'[N <- z]\<close> \<open>P = P'[N <- z]\<close>
    by auto
  ultimately have "M = (Let x E' Q')[P' <- hole]" 
    using usubst_simps(9)[of hole x P' E' Q'] 8(1) \<open>M = Let x R Q'\<close> by auto
  moreover have "Let x E Q = (Let x E' Q')[N <- z]"
    using usubst_simps(9)[of z x N E' Q'] \<open>dset x \<inter> FVars E' = {}\<close> 8(1)
    using \<open>E = E'[N <- z]\<close> \<open>Q'[N <- z] = Q\<close>
    by fastforce
  ultimately have *: "M = (Let x E' Q')[P' <- hole] \<and> Let x E Q = (Let x E' Q')[N <- z] \<and> P = P'[N <- z]"
    using \<open>P = P'[N <- z]\<close> by blast
  also have "eval_ctx hole (Let x E' Q')"
    using \<open>eval_ctx hole E'\<close> \<open>hole \<notin> FVars Q'\<close> 8(5) eval_ctx.intros(8)[of hole E' Q' x] by blast
  ultimately show ?case by auto
next
  case (9 x E Q1 Q2 p M)
  have "M[N <- z] = If E[P <- x] Q1 Q2"
    by(simp add: 9)
  then obtain Q0 Q1' Q2' where "M = If Q0 Q1' Q2'" and "E[P <- x] = Q0[N <- z]" and "Q1 = Q1'[N <- z]" and "Q2 = Q2'[N <- z]"
    using subst_If_inversion 9 blocked_inductive(1) by metis
  moreover from \<open>\<not> blocked z M\<close> have "\<not> blocked z Q0"
    using blocked_inductive(9) \<open>M = If Q0 Q1' Q2'\<close> by auto
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q0 = E'[P' <- x]" and ctxxE: "eval_ctx x E'"
    using 9(2)[where M = Q0] 9 by fastforce
  moreover have q1: "x \<notin> FVars Q1'" and q2: "x \<notin> FVars Q2'"
    using 9 \<open>x \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = If Q0 Q1' Q2'\<close>
    by auto
  ultimately have "M = (If E' Q1' Q2')[P' <- x] \<and> (If E Q1 Q2) = (If E' Q1' Q2')[N <- z] \<and> P = P'[N <- z]"
    using \<open>M = If Q0 Q1' Q2'\<close> \<open>Q1 = Q1'[N <- z]\<close> \<open>Q2 = Q2'[N <- z]\<close> \<open>Q0 = E'[P' <- x]\<close> by simp
  also have "eval_ctx x (If E' Q1' Q2')" using q1 q2 ctxxE eval_ctx.intros(9) by metis
  ultimately show ?case by blast
qed

text \<open>Substitution distributes over Let without any freshness condition on the scrutinee:
  the @{text "dset xy \<inter> FVars t1 = {}"} hypothesis of @{thm usubst_simps(9)} is an artifact
  (the scrutinee is not under the binder). Proved by renaming the binder fresh, pushing, and
  renaming back.\<close>
lemma usubst_Let:
  fixes A :: "'a::var term"
  assumes zd: "z \<notin> dset xy" and dN: "dset xy \<inter> FVars N = {}"
  shows "(term.Let xy A B)[N <- z] = term.Let xy (A[N <- z]) (B[N <- z])"
proof -
  have b1: "|dset xy| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z]) \<union> FVars (B[N <- z]) \<union> dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> (FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z]) \<union> FVars (B[N <- z]) \<union> dset xy) = {}"
      "id_on ((FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z]) \<union> FVars (B[N <- z])) - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV,
        of "(FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z]) \<union> FVars (B[N <- z])) - dset xy"] by auto
  have gz: "g z = z" using g(4) zd unfolding id_on_def by auto
  have gN: "permute_term g N = N"
    by (rule term.permute_cong_id[OF g(1) g(2)]) (use g(4) dN in \<open>auto simp: id_on_def disjoint_iff\<close>)
  have alpha_out: "term.Let xy A B = term.Let (dmap g xy) A (permute_term g B)"
    using g by (auto intro!: exI[of _ g] simp: id_on_def)
  have zd': "z \<notin> dset (dmap g xy)" using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  have dN': "dset (dmap g xy) \<inter> FVars N = {}" using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  have dA': "dset (dmap g xy) \<inter> FVars A = {}" using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  have push: "(term.Let (dmap g xy) A (permute_term g B))[N <- z]
      = term.Let (dmap g xy) (A[N <- z]) ((permute_term g B)[N <- z])"
    by (rule usubst_simps(9)[OF zd' dN' dA'])
  have body: "(permute_term g B)[N <- z] = permute_term g (B[N <- z])"
    unfolding permute_usubst[OF g(1) g(2)] gN gz ..
  have alpha_back: "term.Let (dmap g xy) (A[N <- z]) (permute_term g (B[N <- z])) = term.Let xy (A[N <- z]) (B[N <- z])"
  proof -
    have inv1: "bij (inv g)" "|supp (inv g)| <o |UNIV::'a set|"
      using g(1,2) by (auto simp: supp_inv_bound)
    have dmap_inv: "dmap (inv g) (dmap g xy) = xy"
      by (rule dpair_eqI) (simp_all add: g(1) inv1(1))
    have perm_inv: "permute_term (inv g) (permute_term g (B[N <- z])) = B[N <- z]"
      using permute_term_inv[OF g(1,2)] .
    have idon: "id_on (FVars (permute_term g (B[N <- z])) - dset (dmap g xy)) (inv g)"
    proof -
      have "\<And>y. y \<in> FVars (permute_term g (B[N <- z])) \<Longrightarrow> y \<notin> dset (dmap g xy) \<Longrightarrow> inv g y = y"
      proof -
        fix y assume "y \<in> FVars (permute_term g (B[N <- z]))" and yd: "y \<notin> dset (dmap g xy)"
        then obtain w where w: "w \<in> FVars (B[N <- z])" and yw: "y = g w"
          unfolding term.FVars_permute[OF g(1) g(2)] by auto
        show "inv g y = y"
        proof (cases "w \<in> dset xy")
          case True
          then have "g w \<in> dset (dmap g xy)" unfolding dpair.set_map[OF g(1) g(2)] by auto
          then show ?thesis using yd yw by simp
        next
          case False
          then have "g w = w" using g(4) w unfolding id_on_def by auto
          then show ?thesis using yw g(1) by (metis bij_is_inj inv_f_f)
        qed
      qed
      then show ?thesis unfolding id_on_def by auto
    qed
    show ?thesis
      using inv1 idon dmap_inv perm_inv by (auto intro!: exI[of _ "inv g"])
  qed
  show ?thesis
    unfolding alpha_out push body alpha_back ..
qed

lemma blocked_Let:
  fixes R :: "'a::var term"
  assumes "blocked z R" and "z \<notin> dset xy"
  shows "blocked z (term.Let xy R S)"
proof -
  from assms obtain hole E where ctx: "eval_ctx hole E" and R: "R = E[Var z <- hole]"
    unfolding blocked_def by blast
  obtain hole' :: 'a where h': "hole' \<notin> {z, hole} \<union> FVars E \<union> FVars S \<union> dset xy"
    using arb_element[of "{z, hole} \<union> FVars E \<union> FVars S \<union> dset xy"] finite_FVars finite_dset by auto
  define E' where "E' \<equiv> E[Var hole' <- hole]"
  have ctx': "eval_ctx hole' E'" unfolding E'_def by (rule eval_subst[OF ctx]) (use h' in auto)
  have R': "R = E'[Var z <- hole']"
    unfolding E'_def R using subst_subst[OF ctx, of hole' z] h' by auto
  have ctxL: "eval_ctx hole' (term.Let xy E' S)"
    by (rule eval_ctx.intros(8)[OF ctx']) (use h' in auto)
  have hz: "hole' \<noteq> z" using h' by auto
  have push: "(term.Let xy E' S)[Var z <- hole'] = term.Let xy (E'[Var z <- hole']) (S[Var z <- hole'])"
    by (rule usubst_Let) (use h' hz assms(2) in auto)
  have Sidle: "S[Var z <- hole'] = S" using h' by auto
  show ?thesis unfolding blocked_def
    apply (rule exI[of _ hole'], rule exI[of _ "term.Let xy E' S"])
    using ctxL push Sidle R' by auto
qed

text \<open>The root case of Lemma B.3: a step of @{term "M[N <- z]"} at the root is reflected by a step
  of @{term M}, provided @{term M} is not blocked by @{term z}. Proved standalone with @{term M}
  generalized, so the congruence cases can use their induction hypotheses (the previous inline
  formulation fixed @{term M}, leaving the IHs with unsatisfiable guards).\<close>
lemma b3_root:
  fixes M :: "'a::var term"
  shows "P1 \<rightarrow> P2 \<Longrightarrow> M[N <- z] = P1 \<Longrightarrow> \<not> blocked z M \<Longrightarrow> \<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = P2"
proof (binder_induction P1 P2 arbitrary: M avoiding: z N rule: beta.strong_induct)
  case (OrdApp2 Na Na' f x Q M)
  have fz: "f \<noteq> z" "x \<noteq> z" and fN: "f \<notin> FVars N" "x \<notin> FVars N"
    using \<open>z \<notin> {f} \<union> {x}\<close> \<open>({f} \<union> {x}) \<inter> FVars N = {}\<close> by auto
  from \<open>M[N <- z] = App (Fix f x Q) Na\<close> \<open>\<not> blocked z M\<close>
  obtain R S where MRS: "M = App R S" and R: "R[N <- z] = Fix f x Q" and S: "S[N <- z] = Na" and nbR: "\<not> blocked z R"
    using subst_App_inversion blocked_inductive(1,3) by metis
  obtain Q' where RQ: "R = Fix f x Q'" and Q': "Q'[N <- z] = Q"
    using subst_Fix_inversion[of R N z f x Q] R nbR blocked_inductive(1) fz fN by metis
  have nbS: "\<not> blocked z S" using \<open>\<not> blocked z M\<close> MRS RQ blocked_inductive(2) by metis
  obtain S' where SS: "S \<rightarrow> S'" and S': "S'[N <- z] = Na'"
    using OrdApp2(6)[OF S nbS] by blast
  have step: "M \<rightarrow> App (Fix f x Q') S'" unfolding MRS RQ by (rule beta.OrdApp2[OF SS])
  have sub: "(App (Fix f x Q') S')[N <- z] = App (Fix f x Q) Na'"
    using R RQ S' by auto
  show ?case using step sub by blast
next
  case (OrdApp1 Ma Ma' Na M)
  from \<open>M[N <- z] = App Ma Na\<close> \<open>\<not> blocked z M\<close>
  obtain R S where MRS: "M = App R S" and R: "R[N <- z] = Ma" and S: "S[N <- z] = Na" and nbR: "\<not> blocked z R"
    using subst_App_inversion blocked_inductive(1,3) by metis
  obtain R' where RR: "R \<rightarrow> R'" and R': "R'[N <- z] = Ma'" using OrdApp1(4)[OF R nbR] by blast
  show ?case using beta.OrdApp1[OF RR, of S] MRS R' S by auto
next
  case (OrdSucc Ma Ma' M)
  from \<open>M[N <- z] = Succ Ma\<close> \<open>\<not> blocked z M\<close>
  obtain R where MR: "M = Succ R" and nbR: "\<not> blocked z R" and R: "R[N <- z] = Ma"
    using subst_Succ_inversion blocked_inductive(1,4) by metis
  obtain R' where "R \<rightarrow> R'" "R'[N <- z] = Ma'" using OrdSucc(4)[OF R nbR] by blast
  then show ?case using MR beta.OrdSucc by fastforce
next
  case (OrdPred Ma Ma' M)
  from \<open>M[N <- z] = Pred Ma\<close> \<open>\<not> blocked z M\<close>
  obtain R where MR: "M = Pred R" and nbR: "\<not> blocked z R" and R: "R[N <- z] = Ma"
    using subst_Pred_inversion blocked_inductive(1,5) by metis
  obtain R' where "R \<rightarrow> R'" "R'[N <- z] = Ma'" using OrdPred(4)[OF R nbR] by blast
  then show ?case using MR beta.OrdPred by fastforce
next
  case (OrdPair1 Ma Ma' Na M)
  from \<open>M[N <- z] = term.Pair Ma Na\<close> \<open>\<not> blocked z M\<close>
  obtain R S where MRS: "M = term.Pair R S" and R: "R[N <- z] = Ma" and S: "S[N <- z] = Na" and nbR: "\<not> blocked z R"
    using subst_Pair_inversion blocked_inductive(1,6) by metis
  obtain R' where RR: "R \<rightarrow> R'" and R': "R'[N <- z] = Ma'" using OrdPair1(4)[OF R nbR] by blast
  show ?case using beta.OrdPair1[OF RR, of S] MRS R' S by auto
next
  case (OrdPair2 V Na Na' M)
  from \<open>M[N <- z] = term.Pair V Na\<close> \<open>\<not> blocked z M\<close>
  obtain R S where MRS: "M = term.Pair R S" and R: "R[N <- z] = V" and S: "S[N <- z] = Na" and nbR: "\<not> blocked z R"
    using subst_Pair_inversion blocked_inductive(1,6) by metis
  have vR: "val R" using subst_val_inversion nbR \<open>val V\<close> R by auto
  have nbS: "\<not> blocked z S" using \<open>\<not> blocked z M\<close> MRS vR blocked_inductive(7) by metis
  obtain S' where SS: "S \<rightarrow> S'" and S': "S'[N <- z] = Na'" using OrdPair2(5)[OF S nbS] by blast
  show ?case using beta.OrdPair2[OF vR SS] MRS R S' by auto
next
  case (OrdLet Ma Ma' xy Na M)
  from \<open>M[N <- z] = term.Let xy Ma Na\<close> \<open>\<not> blocked z M\<close>
  obtain R S where MRS: "M = term.Let xy R S" and R: "R[N <- z] = Ma" and S: "S[N <- z] = Na"
    using subst_Let_inversion[of M N z xy Ma Na] blocked_inductive(1) \<open>z \<notin> dset xy\<close> \<open>dset xy \<inter> FVars N = {}\<close>
    by (metis Int_commute)
  have nbR: "\<not> blocked z R" using \<open>\<not> blocked z M\<close> MRS blocked_Let \<open>z \<notin> dset xy\<close> by metis
  obtain R' where RR: "R \<rightarrow> R'" and R': "R'[N <- z] = Ma'" using OrdLet(6)[OF R nbR] by blast
  have push: "(term.Let xy R' S)[N <- z] = term.Let xy (R'[N <- z]) (S[N <- z])"
    by (rule usubst_Let[OF \<open>z \<notin> dset xy\<close> \<open>dset xy \<inter> FVars N = {}\<close>])
  show ?case using beta.OrdLet[OF RR, of xy S] MRS push R' S by auto
next
  case (OrdIf Ma Ma' Na P M)
  from \<open>M[N <- z] = term.If Ma Na P\<close> \<open>\<not> blocked z M\<close>
  obtain R S T where MRS: "M = term.If R S T" and R: "R[N <- z] = Ma" and S: "S[N <- z] = Na" and T: "T[N <- z] = P" and nbR: "\<not> blocked z R"
    using subst_If_inversion[of M N z Ma Na P] blocked_inductive(1,9) by metis
  obtain R' where RR: "R \<rightarrow> R'" and R': "R'[N <- z] = Ma'" using OrdIf(4)[OF R nbR] by blast
  show ?case using beta.OrdIf[OF RR, of S T] MRS R' S T by auto
next
  case (Ifz Na P M)
  from \<open>M[N <- z] = term.If Zero Na P\<close> \<open>\<not> blocked z M\<close>
  obtain Q0 Q1 Q2 where MI: "M = term.If Q0 Q1 Q2" and Q0: "Q0[N <- z] = Zero" and Q1: "Q1[N <- z] = Na" and Q2: "Q2[N <- z] = P" and nb0: "\<not> blocked z Q0"
    using subst_If_inversion[of M N z Zero Na P] blocked_inductive(1,9) by metis
  have "Q0 = Zero" using Q0 nb0 subst_Zero_inversion blocked_inductive(1) by blast
  then show ?case using MI Q1 beta.Ifz by auto
next
  case (Ifs n Na P M)
  from \<open>M[N <- z] = term.If (Succ n) Na P\<close> \<open>\<not> blocked z M\<close>
  obtain Q0 Q1 Q2 where MI: "M = term.If Q0 Q1 Q2" and Q0: "Q0[N <- z] = Succ n" and Q1: "Q1[N <- z] = Na" and Q2: "Q2[N <- z] = P" and nb0: "\<not> blocked z Q0"
    using subst_If_inversion[of M N z "Succ n" Na P] blocked_inductive(1,9) by metis
  have "Q0 = Succ n" using \<open>num n\<close> num.intros(2) subst_num_inversion Q0 nb0 by blast
  then show ?case using MI Q2 \<open>num n\<close> beta.Ifs by metis
next
  case (Let V W xy Ma M)
  from \<open>M[N <- z] = term.Let xy (term.Pair V W) Ma\<close> \<open>\<not> blocked z M\<close>
  obtain P' Q' where MPQ: "M = term.Let xy P' Q'" and P': "P'[N <- z] = term.Pair V W" and Q': "Q'[N <- z] = Ma"
    using subst_Let_inversion[of M N z xy "term.Pair V W" Ma] blocked_inductive(1) \<open>z \<notin> dset xy\<close> \<open>dset xy \<inter> FVars N = {}\<close>
    by (metis Int_commute)
  have nbP': "\<not> blocked z P'" using \<open>\<not> blocked z M\<close> MPQ blocked_Let \<open>z \<notin> dset xy\<close> by metis
  obtain V' W' where P'VW: "P' = term.Pair V' W'" and V': "V'[N <- z] = V" and W': "W'[N <- z] = W" and nbV': "\<not> blocked z V'"
    using subst_Pair_inversion P' nbP' blocked_inductive(1,6) by metis
  have vV': "val V'" using subst_val_inversion nbV' \<open>val V\<close> V' by auto
  have nbW': "\<not> blocked z W'" using nbP' P'VW vV' blocked_inductive(7) by metis
  have vW': "val W'" using subst_val_inversion nbW' \<open>val W\<close> W' by auto
  have subst_eq: "(Q'[V' <- dfst xy][W' <- dsnd xy])[N <- z] = Ma[V <- dfst xy][W <- dsnd xy]"
    using usubst_usubst[of "dsnd xy" z N "Q'[V' <- dfst xy]" W'] usubst_usubst[of "dfst xy" z N Q' V']
    using \<open>z \<notin> dset xy\<close> \<open>dset xy \<inter> FVars N = {}\<close> Q' V' W'
    by (metis Int_emptyD dsel_dset(1,2))
  have fresh: "dset xy \<inter> FVars V' = {}"
    using \<open>dset xy \<inter> FVars V = {}\<close> \<open>z \<notin> dset xy\<close> FVars_usubst[of V' N z] V'
    by (fastforce simp: disjoint_iff split: if_splits)
  have step: "term.Let xy (term.Pair V' W') Q' \<rightarrow> Q'[V' <- dfst xy][W' <- dsnd xy]"
    by (rule beta.Let[OF vV' vW' fresh])
  show ?case using step subst_eq MPQ P'VW by metis
next
  case (PredZ M)
  from \<open>M[N <- z] = Pred Zero\<close> \<open>\<not> blocked z M\<close>
  obtain Q where MP: "M = Pred Q" and nbQ: "\<not> blocked z Q" and Q: "Q[N <- z] = Zero"
    using subst_Pred_inversion blocked_inductive(1,5) by metis
  have "Q = Zero" using Q nbQ subst_Zero_inversion blocked_inductive(1) by blast
  then show ?case using MP beta.PredZ by auto
next
  case (PredS n M)
  from \<open>M[N <- z] = Pred (Succ n)\<close> \<open>\<not> blocked z M\<close>
  obtain Q where MP: "M = Pred Q" and nbQ: "\<not> blocked z Q" and Q: "Q[N <- z] = Succ n"
    using subst_Pred_inversion blocked_inductive(1,5) by metis
  obtain Q' where QS: "Q = Succ Q'" and nbQ': "\<not> blocked z Q'" and Q': "Q'[N <- z] = n"
    using subst_Succ_inversion Q nbQ blocked_inductive(1,4) by metis
  have "num Q'" using subst_num_inversion Q' nbQ' \<open>num n\<close> by metis
  then show ?case using MP QS Q' beta.PredS by fastforce
next
  case (FixBeta V f x Ma M)
  have fz: "f \<noteq> z" "x \<noteq> z" and fN: "f \<notin> FVars N" "x \<notin> FVars N"
    using \<open>z \<notin> {f} \<union> {x}\<close> \<open>({f} \<union> {x}) \<inter> FVars N = {}\<close> by auto
  from \<open>M[N <- z] = App (Fix f x Ma) V\<close> \<open>\<not> blocked z M\<close>
  obtain R V' where MRV: "M = App R V'" and R: "R[N <- z] = Fix f x Ma" and V': "V'[N <- z] = V" and nbR: "\<not> blocked z R"
    using subst_App_inversion blocked_inductive(1,3) by metis
  obtain Q' where RQ: "R = Fix f x Q'" and Q': "Q'[N <- z] = Ma"
    using subst_Fix_inversion[of R N z f x Ma] R nbR blocked_inductive(1) fz fN by metis
  have FixEq: "(Fix f x Q')[N <- z] = Fix f x Ma" using R RQ by auto
  have *: "Q'[V' <- x][Fix f x Q' <- f][N <- z] = Ma[V <- x][Fix f x Ma <- f]"
    using usubst_usubst[of f z N "Q'[V' <- x]" "Fix f x Q'"] usubst_usubst[of x z N Q' V']
    using fz fN Q' V' FixEq by metis
  have nbV': "\<not> blocked z V'" using blocked_inductive(2) \<open>\<not> blocked z M\<close> MRV RQ by metis
  have vV': "val V'" using subst_val_inversion \<open>val V\<close> V' nbV' by auto
  have fV': "f \<notin> FVars V'"
    using \<open>f \<notin> FVars V\<close> fz(1) V' FVars_usubst[of V' N z] by (auto split: if_splits)
  have step: "App (Fix f x Q') V' \<rightarrow> Q'[V' <- x][Fix f x Q' <- f]"
    using vV' fV' by (rule beta.FixBeta)
  show ?case using step * MRV RQ by metis
qed

section \<open>B3\<close>

thm eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P1, P2) \<longrightarrow> M[N <- z] = E[P1 <- x] \<longrightarrow>
    P1 \<rightarrow> P2 \<longrightarrow> \<not> blocked z M \<longrightarrow> (\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x])"
    and K = "\<lambda>(z, N, M, E, x, P1, P2). {z,x} \<union> FVars N \<union> FVars M  \<union> FVars E \<union> FVars P1 \<union> FVars P2",
    rule_format, rotated -4, of "(z, N, M, E, x, P1, P2)" M E x,
    simplified prod.inject simp_thms True_implies_equals]

lemma b3_1: 
  assumes "eval_ctx x E" and "M[N <- z] = E[P1 <- x]" and "P1 \<rightarrow> P2" and "\<not> blocked z M"
  shows "\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x]"
proof (rule eval_ctx.strong_induct[where P = "\<lambda>x E p. \<forall>M.
    p = (z, N, M, E, x, P1, P2) \<longrightarrow> M[N <- z] = E[P1 <- x] \<longrightarrow>
    P1 \<rightarrow> P2 \<longrightarrow> \<not> blocked z M \<longrightarrow> (\<exists>M'. M \<rightarrow> M' \<and> M'[N <- z] = E[P2 <- x])"
    and K = "\<lambda>(z, N, M, E, x, P1, P2). {z,x} \<union> FVars N \<union> FVars M \<union> FVars E \<union> FVars P1 \<union> FVars P2",
    rule_format, rotated -4, of "(z, N, M, E, x, P1, P2)" M E x, OF _ assms(2,3,4,1),
    simplified prod.inject simp_thms True_implies_equals], 
    goal_cases card 1 2 3 4 5 6 7 8 9)
  case (card p)
  then show ?case
    by (cases p) (auto intro!: finite_ordLess_infinite2[OF _ infinite_UNIV])
next
  case (1 hole p' M)
  then show ?case using b3_root[of P1 P2 M N z] by auto
next
  case (2 hole E Q f x p M)
  then have "M[N <- z] = App (Fix f x Q) E[P1 <- hole]"
   using subst_idle usubst_simps(6) by auto
  then obtain F R where "M = App F R" and "R[N <- z] = E[P1 <- hole]" and "F[N <- z] = Fix f x Q"
    using \<open>\<not> blocked z M\<close> subst_App_inversion  blocked_inductive(1) by blast
  then have "\<not> blocked z F" using blocked_inductive \<open>\<not> blocked z M\<close> by blast
  then obtain Q' where "F = Fix f x Q'" and "Q'[N <- z] = Q"
    using \<open>F[N <- z] = Fix f x Q\<close> 2(1) subst_Fix_inversion[of F N z f x Q] blocked_inductive(1)[of z] by auto
  then have "\<not> blocked z R" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = App F R\<close> by blast
  then obtain R' where "R \<rightarrow> R'" and "R'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> "2"(3)[of _  R] \<open>R[N <- z] = E[P1 <- hole]\<close> by auto
  have "(App (Fix f x Q') R')[N <- z] = (App (Fix f x Q) E)[P2 <- hole]"
    using "2"(1, 4) \<open>Q'[N <- z] = Q\<close> \<open>R'[N <- z] = E[P2 <- hole]\<close> by auto
  then show ?case
    using OrdApp2 \<open>F = Fix f x Q'\<close> \<open>M = App F R\<close> \<open>R \<rightarrow> R'\<close> by blast
next
  case (3 hole E Q p M)
  then have "M[N <- z] = App E[P1 <- hole] Q"
   using subst_idle usubst_simps(6) by auto
  then obtain R Q' where "M = App R Q'" and "R[N <- z] = E[P1 <- hole]" and "Q'[N <- z] = Q"
    using \<open>\<not> blocked z M\<close> subst_App_inversion blocked_inductive(1) by blast
  then have "\<not> blocked z R" using blocked_inductive \<open>\<not> blocked z M\<close> by blast
  then obtain R' where "R \<rightarrow> R'" and "R'[N <- z] = E[P2 <- hole]" 
    using \<open>P1 \<rightarrow> P2\<close> "3"(2)[where M = R] \<open>R[N <- z] = E[P1 <- hole]\<close> by auto
  have "(App R' Q')[N <- z] = (App E Q)[P2 <- hole]"
    using "3"(3) \<open>Q'[N <- z] = Q\<close> \<open>R'[N <- z] = E[P2 <- hole]\<close> by simp
  then show ?case
    using OrdApp1 \<open>M = App R Q'\<close> \<open>R \<rightarrow> R'\<close> by blast
next
  case (4 hole E p M)
  obtain Q where "M = Succ Q" and "Q[N <- z] = E[P1 <- hole]"
    using \<open>M[N <- z] = (Succ E)[P1 <- hole]\<close> \<open>\<not> blocked z M\<close> subst_Succ_inversion blocked_inductive(1) by force
  moreover have "\<not> blocked z Q" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Succ Q\<close> by blast
  ultimately obtain Q' where "Q \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> "4"(2)[where M = Q] by auto
  have "(Succ Q')[N <- z] = (Succ E)[P2 <- hole]"
    by (simp add: \<open>Q'[N <- z] = E[P2 <- hole]\<close>)
  then show ?case
    using OrdSucc \<open>M = Succ Q\<close> \<open>Q \<rightarrow> Q'\<close> by blast
next
  case (5 hole E p M)
  obtain Q where "M = Pred Q" and "Q[N <- z] = E[P1 <- hole]"
    using \<open>M[N <- z] = (Pred E)[P1 <- hole]\<close> \<open>\<not> blocked z M\<close> subst_Pred_inversion blocked_inductive(1) by force
  moreover have "\<not> blocked z Q" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Pred Q\<close> by blast
  ultimately obtain Q' where "Q \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]" 
    using \<open>P1 \<rightarrow> P2\<close> "5"(2)[of _ Q] by auto
  have "(Pred Q')[N <- z] = (Pred E)[P2 <- hole]"
    by (simp add: \<open>Q'[N <- z] = E[P2 <- hole]\<close>)
  then show ?case
    using OrdPred \<open>M = Pred Q\<close> \<open>Q \<rightarrow> Q'\<close> by blast
next
  case (6 hole E Q2 p M)
  have "M[N <- z] = (Pair E[P1 <- hole] Q2)"
    by (simp add: "6"(3, 5))
  then obtain Q1' Q2' where "M = Pair Q1' Q2'" and "Q1'[N <- z] = E[P1 <- hole]" and "Q2'[N <- z] = Q2"
    using \<open>\<not> blocked z M\<close> subst_Pair_inversion blocked_inductive(1) by blast
  moreover have "\<not> blocked z Q1'" using blocked_inductive(6) \<open>\<not> blocked z M\<close> \<open>M = Pair Q1' Q2'\<close> by metis
  ultimately obtain Q' where "Q1' \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]" 
    using \<open>P1 \<rightarrow> P2\<close> "6"(2)[of _ Q1'] by blast
  have "(Pair Q' Q2')[N <- z] = (Pair E Q2)[P2 <- hole]"
    by (simp add: "6"(3) \<open>Q'[N <- z] = E[P2 <- hole]\<close> \<open>Q2'[N <- z] = Q2\<close>)
  then show ?case
    using OrdPair1 \<open>M = term.Pair Q1' Q2'\<close> \<open>Q1' \<rightarrow> Q'\<close> by blast
next
  case (7 V hole E p M)
  have "M[N <- z] = (Pair V E[P1 <- hole])"
    using "7" by simp
  then obtain V' Q where "M = Pair V' Q" and "V'[N <- z] = V" and "Q[N <- z] = E[P1 <- hole]"
    using \<open>\<not> blocked z M\<close> subst_Pair_inversion[of M N z V "E[P1 <- hole]"] blocked_inductive(1) by blast
  then have "val V'" using 7(1) \<open>\<not> blocked z M\<close> blocked_inductive(6) subst_val_inversion
    by metis
  then have "\<not> blocked z Q" using blocked_inductive(7) \<open>\<not> blocked z M\<close> \<open>M = Pair V' Q\<close> by metis
  then obtain Q' where "Q \<rightarrow> Q'" and "Q'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> \<open>Q[N <- z] = E[P1 <- hole]\<close> "7"(3)[of _ Q] by blast
  have "(Pair V' Q')[N <- z] = (Pair V E)[P2 <- hole]"
    using \<open>Q'[N <- z] = E[P2 <- hole]\<close> \<open>V'[N <- z] = V\<close> by (simp add: "7"(4))
  then show ?case
    using OrdPair2 \<open>M = term.Pair V' Q\<close> \<open>Q \<rightarrow> Q'\<close> \<open>val V'\<close> by blast
next
  case (8 hole E Q xy p M)
  have "M[N <- z] = Let xy E[P1 <- hole] Q"
   using usubst_simps(9)[of hole xy P1 E Q] subst_idle 8 by fastforce
  then obtain R Q' where "M = Let xy R Q'" and "R[N <- z] = E[P1 <- hole]" and "Q'[N <- z] = Q"
    using \<open>\<not> blocked z M\<close> subst_Let_inversion 8(1) blocked_inductive(1) by blast
  then have "\<not> blocked z R" using blocked_inductive(1,8) \<open>\<not> blocked z M\<close> 8(1,4,5)
    by (fastforce simp: Int_Un_distrib)
  then obtain R' where "R \<rightarrow> R'" and "R'[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> "8"(3)[of _  R] \<open>R[N <- z] = E[P1 <- hole]\<close> by auto
  thm FVars_subst
  have "dset xy \<inter> FVars E[P2 <- hole] = {}"
    using 8(1) FVars_subst[of "Var(hole:=P2)" E] by auto
  then have "dset xy \<inter> FVars R' = {}"
    using FVars_subst_inversion[of R' N z] FVars_subst_inversion[of Q' N z]
    using 8(1) \<open>R'[N <- z] = E[P2 <- hole]\<close> \<open>Q'[N <- z] = Q\<close>
    by auto
  then have "(Let xy R' Q')[N <- z] = (Let xy E Q)[P2 <- hole]"
    using usubst_simps(9)[of z xy N R' Q']  usubst_simps(9)[of hole xy P2 E Q] 
    using "8"(1, 4) \<open>Q'[N <- z] = Q\<close> \<open>R'[N <- z] = E[P2 <- hole]\<close>
    by fastforce
  then show ?case
    using OrdLet \<open>M = term.Let xy R Q'\<close> \<open>R \<rightarrow> R'\<close> by blast
next
  case (9 hole E Q1 Q2 p M)
  have "M[N <- z] = (If E[P1 <- hole] Q1 Q2)"
    by (simp add: 9)
  then obtain Q0' Q1' Q2' 
    where "M = If Q0' Q1' Q2'" and "Q0'[N <- z] = E[P1 <- hole]" and "Q1'[N <- z] = Q1" and "Q2'[N <- z] = Q2"
    using \<open>\<not> blocked z M\<close> subst_If_inversion[of M N z "E[P1 <- hole]" Q1 Q2] blocked_inductive(1) by blast
  then have "\<not> blocked z Q0'" using blocked_inductive(9) \<open>\<not> blocked z M\<close> \<open>M = If Q0' Q1' Q2'\<close> by metis
  then obtain Q where "Q0' \<rightarrow> Q" and "Q[N <- z] = E[P2 <- hole]"
    using \<open>P1 \<rightarrow> P2\<close> \<open>Q0'[N <- z] = E[P1 <- hole]\<close> 9(2)[of _ Q0'] by blast
  have "(If Q Q1' Q2')[N <- z] = (If E Q1 Q2)[P2 <- hole]"
    using \<open>Q[N <- z] = E[P2 <- hole]\<close> \<open>Q1'[N <- z] = Q1\<close> \<open>Q2'[N <- z] = Q2\<close> by (simp add: 9)
  then show ?case
    using OrdIf \<open>M = term.If Q0' Q1' Q2'\<close> \<open>Q0' \<rightarrow> Q\<close> by blast
qed

thm b3_1

lemma b3: "M[N <- z] \<rightarrow> P \<Longrightarrow> blocked z M \<or> (\<exists>M'. M \<rightarrow> M' \<and> P = M'[N <- z])"
proof -
  assume "M[N <- z] \<rightarrow> P"
  obtain E :: "'a term" and x :: 'a where "eval_ctx x E" and "E = Var x"
    by (simp add: eval_ctx.intros(1))
  then have "\<not> blocked z M \<Longrightarrow> (\<exists>M'. M \<rightarrow> M' \<and> P = M'[N <- z])" 
    using b3_1[of x E M N z "M[N <- z]" P] \<open>M[N <- z] \<rightarrow> P\<close> by auto
  then show ?thesis by blast
qed

section \<open>B4\<close>

context fixes x :: "'a :: var" begin
private definition Uctor :: "('a, 'a, 'a MrBNF_ver.term \<times> (unit \<Rightarrow> nat), 'a MrBNF_ver.term \<times> (unit \<Rightarrow> nat)) term_pre \<Rightarrow> unit \<Rightarrow> nat" where
  "Uctor \<equiv> \<lambda>pre _. case Rep_term_pre pre of
      Inl (Inl (Inl _)) \<Rightarrow> 0
    | Inl (Inl (Inr (_, c))) \<Rightarrow> c ()
    | Inl (Inr (Inl (_, c))) \<Rightarrow> c ()
    | Inl (Inr (Inr ((_, c1), (_, c2), (_, c3)))) \<Rightarrow> c1 () + c2 () + c3 ()
    | Inr (Inl (Inl y)) \<Rightarrow> (if x = y then 1 else 0)
    | Inr (Inl (Inr ((_, c1), (_, c2)))) \<Rightarrow> c1 () + c2 ()
    | Inr (Inr (Inl (_, _, _, c))) \<Rightarrow> c ()
    | Inr (Inr (Inr (Inl ((_, c1), (_, c2))))) \<Rightarrow> c1 () + c2 ()
    | Inr (Inr (Inr (Inr (_, (_, c1), (_, c2))))) \<Rightarrow> c1 () + c2 ()"
interpretation count: REC_term where
  Pmap = "\<lambda>_. id" and
  PFVars = "\<lambda>_. {}" and
  validP = "\<lambda>_::unit. True" and
  avoiding_set = "{x}" and
  Umap = "\<lambda>_ _. id" and
  UFVars = "\<lambda>_ _. {}" and
  validU = "\<lambda>_ :: nat. True" and
  Uctor = Uctor
  by standard
    (auto simp: Uctor_def map_term_pre_def Abs_term_pre_inverse[OF UNIV_I] in_imsupp
      dest: not_in_imsupp_same split: sum.splits)

definition "count_term t = count.REC_term t ()"

lemmas count_term_ctor = count.REC_ctor[simplified,
  folded count_term_def, unfolded Uctor_def map_term_pre_def o_apply Abs_term_pre_inverse[OF UNIV_I]
  case_sum_map_sum case_prod_map_prod prod.case, folded Uctor_def count_term_def]

lemmas count_term_swap = count.REC_swap[simplified, folded count_term_def]

end

lemma count_term_simps[simp]:
  "count_term x Zero = 0"
  "count_term x (Pred M) = count_term x M"
  "count_term x (Succ M) = count_term x M"
  "count_term x (If M N P) = count_term x M + count_term x N + count_term x P"
  "count_term x (Var y) = (if x = y then 1 else 0)"
  "count_term x (App M N) = count_term x M + count_term x N"
  "x \<noteq> f \<Longrightarrow> x \<noteq> a \<Longrightarrow> count_term x (Fix f a M) = count_term x M"
  "count_term x (Pair M N) = count_term x M + count_term x N"
  "x \<notin> dset xy \<Longrightarrow> dset xy \<inter> FVars M = {} \<Longrightarrow> count_term x (Let xy M N) = count_term x M + count_term x N"
  unfolding Zero_def Pred_def Succ_def If_def Var_def Fix_def App_def Pair_def Let_def
  by (subst count_term_ctor; auto simp:
    set1_term_pre_def set2_term_pre_def set3_term_pre_def set4_term_pre_def
    noclash_term_def sum.set_map Abs_term_pre_inverse[OF UNIV_I])+

lemma eval_ctx_beta: "eval_ctx x E \<Longrightarrow> M \<rightarrow> N \<Longrightarrow> E[M <- x] \<rightarrow> E[N <- x]"
  apply(binder_induction x E avoiding: M N E rule:eval_ctx.strong_induct)
  apply(auto intro:beta.intros)
  subgoal premises prems for hole Ea Na xy
  proof -
    have 1: "dset xy \<inter> FVars Ea = {}" using prems(3) by blast
    have L: "(term.Let xy Ea Na)[M <- hole] = term.Let xy (Ea[M <- hole]) Na"
      by (subst usubst_simps(9)) (use prems(1,6,7) 1 in auto)
    have R: "(term.Let xy Ea Na)[N <- hole] = term.Let xy (Ea[N <- hole]) Na"
      by (subst usubst_simps(9)) (use prems(2,6,7) 1 in auto)
    show ?thesis unfolding L R using beta.OrdLet[OF prems(5)] by simp
  qed
  done

corollary eval_ctx_betas: 
  assumes "eval_ctx x E" and "M \<rightarrow>[n] N" shows "E[M <- x] \<rightarrow>[n] E[N <- x]"
  using \<open>M \<rightarrow>[n] N\<close>
proof(induction rule:betas.induct)
  case (refl M)
  then show ?case using betas.intros by auto
next
  case (step M N n P)
  then have "E[M <- x] \<rightarrow> E[N <- x]" 
    using eval_ctx_beta \<open>eval_ctx x E\<close> by auto
  then show ?case using \<open>E[N <- x] \<rightarrow>[n] E[P <- x]\<close> betas.intros(2) by auto
qed

corollary eval_ctx_beta_star: "eval_ctx x E \<Longrightarrow> M \<rightarrow>* N \<Longrightarrow> E[M <- x] \<rightarrow>* E[N <- x]"
  using eval_ctx_betas beta_star_def by blast

lemma div_ctx: 
  "eval_ctx x E \<Longrightarrow> diverge Q \<Longrightarrow> diverge E[Q <- x]"
proof(coinduction arbitrary: "Q" rule:diverge.coinduct)
  case diverge
  then obtain Q' where "Q \<rightarrow> Q'" and "diverge Q'" using diverge.cases by auto
  then have "E[Q <- x] \<rightarrow> E[Q' <- x]" using eval_ctx_beta \<open>eval_ctx x E\<close> by blast
  then show ?case using \<open>diverge Q'\<close> \<open>eval_ctx x E\<close> by auto
qed

thm eval_ctx.intros

lemma num_usubst_idle[simp]: "num n \<Longrightarrow> n[Q <- x] = n"
  by (induct rule: num.induct) auto

text \<open>Substitution pushes through @{text Fix} and @{text Let} after alpha-refreshing the
  binder away from an arbitrary finite set, with a bound on the free variables of the new
  body. These are the workhorses for @{text blocked_fresh_hole} below, where an arbitrary
  term @{term N} (whose variables may clash with the binders) is substituted into a context.\<close>

lemma usubst_Fix_push:
  fixes Q N :: "'a::var term" and A :: "'a set"
  assumes "finite A"
  shows "\<exists>f' x' Q'. (Fix f x Q)[N <- z] = Fix f' x' Q' \<and> f' \<notin> A \<and> x' \<notin> A \<and>
    FVars Q' \<subseteq> (FVars Q - {f, x} - {z}) \<union> FVars N \<union> {f', x'}"
proof -
  have b1: "|{f, x}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
  have b2: "|{f, x} \<union> FVars Q \<union> FVars N \<union> A \<union> {z}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: assms)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` {f, x} \<inter> ({f, x} \<union> FVars Q \<union> FVars N \<union> A \<union> {z}) = {}"
      "id_on (FVars Q - {x, f}) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars Q - {x, f}"]
    by (auto simp: insert_commute)
  have eq: "Fix f x Q = Fix (g f) (g x) (permute_term g Q)"
    using g by (auto intro!: exI[of _ g])
  have fr: "g f \<notin> FVars N \<union> A \<union> {z}" "g x \<notin> FVars N \<union> A \<union> {z}"
    using g(3) by auto
  have push: "(Fix (g f) (g x) (permute_term g Q))[N <- z] =
      Fix (g f) (g x) ((permute_term g Q)[N <- z])"
    by (rule usubst_simps(7)) (use fr in auto)
  have FQ: "FVars (permute_term g Q) \<subseteq> (FVars Q - {f, x}) \<union> {g f, g x}"
    unfolding term.FVars_permute[OF g(1,2)] using g(4) unfolding id_on_def by force
  show ?thesis
    apply (rule exI[of _ "g f"], rule exI[of _ "g x"], rule exI[of _ "(permute_term g Q)[N <- z]"])
    using fr FQ
    apply auto
        apply (metis eq push)
       apply force
      apply force
    by (auto simp: FVars_usubst split: if_splits)
qed

lemma usubst_Let_push:
  fixes S B N :: "'a::var term" and A :: "'a set"
  assumes "finite A"
  shows "\<exists>xy' B'. (term.Let xy S B)[N <- z] = term.Let xy' (S[N <- z]) B' \<and> dset xy' \<inter> A = {} \<and>
    FVars B' \<subseteq> (FVars B - dset xy - {z}) \<union> FVars N \<union> dset xy'"
proof -
  have b1: "|dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|dset xy \<union> FVars S \<union> FVars B \<union> FVars N \<union> A \<union> {z}| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: assms finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> (dset xy \<union> FVars S \<union> FVars B \<union> FVars N \<union> A \<union> {z}) = {}"
      "id_on (FVars B - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars B - dset xy"] by auto
  have eq: "term.Let xy S B = term.Let (dmap g xy) S (permute_term g B)"
    using g by (auto intro!: exI[of _ g])
  have dd: "dset (dmap g xy) = g ` dset xy"
    by (rule dpair.set_map[OF g(1,2)])
  have fr: "dset (dmap g xy) \<inter> (FVars S \<union> FVars N \<union> A \<union> {z}) = {}"
    unfolding dd using g(3) by blast
  have push: "(term.Let (dmap g xy) S (permute_term g B))[N <- z] =
      term.Let (dmap g xy) (S[N <- z]) ((permute_term g B)[N <- z])"
    by (rule usubst_simps(9)) (use fr in auto)
  have FB: "FVars (permute_term g B) \<subseteq> (FVars B - dset xy) \<union> dset (dmap g xy)"
    unfolding term.FVars_permute[OF g(1,2)] dd using g(4) unfolding id_on_def by force
  show ?thesis
    apply (rule exI[of _ "dmap g xy"], rule exI[of _ "(permute_term g B)[N <- z]"])
    using fr FB
    apply auto
       apply (metis eq push)
      apply force
     apply force
    by (auto simp: FVars_usubst split: if_splits)
qed

text \<open>A value @{term V} either stays a value under every substitution for @{term z}
  (all @{term z}-occurrences are absorbed under @{text Fix} binders or absent), or its
  leftmost bare @{term z} can be marked as a hole such that the marked term is an
  evaluation context under every substitution for @{term z}.\<close>

lemma val_hole:
  fixes V :: "'a::var term"
  shows "val V \<Longrightarrow> h \<notin> FVars V \<union> {z} \<Longrightarrow>
    (\<forall>N. val (V[N <- z])) \<or>
    (\<exists>E. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E[N <- z])) \<and> V = E[Var z <- h] \<and>
         FVars E \<subseteq> FVars V \<union> {h})"
proof (induction rule: val.induct)
  case (1 y)
  show ?case
  proof (cases "y = z")
    case True
    have "eval_ctx h ((Var h)[N <- z])" for N
      using 1 eval_ctx.intros(1) by auto
    moreover have "Var y = (Var h)[Var z <- h]" using True by simp
    ultimately show ?thesis by (intro disjI2 exI[of _ "Var h"]) auto
  next
    case False
    then show ?thesis using val.intros(1) by auto
  qed
next
  case (2 n)
  then show ?case using val.intros(2) by auto
next
  case (3 V W)
  have hV: "h \<notin> FVars V \<union> {z}" and hW: "h \<notin> FVars W \<union> {z}" using 3(5) by auto
  from 3(3)[OF hV] show ?case
  proof (elim disjE exE)
    assume L1: "\<forall>N. val (V[N <- z])"
    from 3(4)[OF hW] show ?thesis
    proof (elim disjE exE)
      assume L2: "\<forall>N. val (W[N <- z])"
      have "val ((term.Pair V W)[N <- z])" for N
        using L1 L2 val.intros(3) by auto
      then show ?thesis by blast
    next
      fix E2 assume R2: "(\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E2[N <- z])) \<and> W = E2[Var z <- h] \<and>
        FVars E2 \<subseteq> FVars W \<union> {h}"
      have ctx: "eval_ctx h ((term.Pair V E2)[N <- z])" if hN: "h \<notin> FVars N" for N
      proof -
        have "eval_ctx h (E2[N <- z])" using R2 hN by blast
        moreover have "val (V[N <- z])" using L1 by blast
        moreover have "h \<notin> FVars (V[N <- z])" using hV hN by (auto simp: FVars_usubst)
        ultimately show ?thesis using eval_ctx.intros(7) by auto
      qed
      have eqn: "term.Pair V W = (term.Pair V E2)[Var z <- h]"
        using R2 hV by auto
      show ?thesis
        apply (rule disjI2, rule exI[of _ "term.Pair V E2"])
        using ctx eqn R2 by auto
    qed
  next
    fix E1 assume R1: "(\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E1[N <- z])) \<and> V = E1[Var z <- h] \<and>
      FVars E1 \<subseteq> FVars V \<union> {h}"
    have ctx: "eval_ctx h ((term.Pair E1 W)[N <- z])" if hN: "h \<notin> FVars N" for N
    proof -
      have "eval_ctx h (E1[N <- z])" using R1 hN by blast
      moreover have "h \<notin> FVars (W[N <- z])" using hW hN by (auto simp: FVars_usubst)
      ultimately show ?thesis using eval_ctx.intros(6) by auto
    qed
    have eqn: "term.Pair V W = (term.Pair E1 W)[Var z <- h]"
      using R1 hW by auto
    show ?thesis
      apply (rule disjI2, rule exI[of _ "term.Pair E1 W"])
      using ctx eqn R1 by auto
  qed
next
  case (4 f x Q)
  have "val ((Fix f x Q)[N <- z])" for N
  proof -
    obtain f' x' Q' where "(Fix f x Q)[N <- z] = Fix f' x' Q'"
      using usubst_Fix_push[of "{}" f x Q N z] by auto
    then show ?thesis using val.intros(4) by simp
  qed
  then show ?case by blast
qed

text \<open>The key re-holing lemma: a context can always be re-holed so that the hole avoids a
  given finite set AND the plugged context stays an evaluation context under EVERY
  substitution for @{term z} (no value condition on the substituted term). The hole may
  have to MOVE: in @{term "term.Pair (Var z) (Var hole)"} it must migrate to the first
  component, since substituting a non-value for @{term z} there destroys the value status
  required by the second-component-context rule. Values in the context are handled by
  @{text val_hole}; @{text Fix}- and @{text Let}-binders by the push lemmas above.\<close>

lemma blocked_fresh_hole_aux:
  fixes E0 :: "'a::var term"
  assumes ctx: "eval_ctx hole0 E0"
  shows "\<forall>p :: 'a \<times> 'a. case p of (z, h) \<Rightarrow> h \<notin> FVars E0 \<union> {z} \<longrightarrow>
    (\<exists>E. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E[N <- z])) \<and> E0[Var z <- hole0] = E[Var z <- h] \<and>
         FVars E \<subseteq> (FVars E0 - {hole0}) \<union> {h, z})"
proof (rule eval_ctx_strong_induct[where K = "\<lambda>(z, h). {z, h}"
      and P = "\<lambda>hole0 E0 p. case p of (z, h) \<Rightarrow> h \<notin> FVars E0 \<union> {z} \<longrightarrow>
        (\<exists>E. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E[N <- z])) \<and> E0[Var z <- hole0] = E[Var z <- h] \<and>
             FVars E \<subseteq> (FVars E0 - {hole0}) \<union> {h, z})", OF ctx],
    goal_cases card 1 2 3 4 5 6 7 8 9)
  case (card p)
  then show ?case
    by (cases p) (auto intro!: finite_ordLess_infinite2[OF _ infinite_UNIV])
next
  case (1 hole p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (Var hole) \<union> {z}"
    have "eval_ctx h ((Var h)[N <- z])" for N using hE eval_ctx.intros(1) by auto
    moreover have "(Var hole)[Var z <- hole] = (Var h)[Var z <- h]" by simp
    ultimately show "\<exists>E. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E[N <- z])) \<and>
        (Var hole)[Var z <- hole] = E[Var z <- h] \<and>
        FVars E \<subseteq> (FVars (Var hole) - {hole}) \<union> {h, z}"
      by (intro exI[of _ "Var h"]) auto
  qed
next
  case (2 hole E Q f x p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  have av: "f \<noteq> h" "x \<noteq> h" "f \<noteq> z" "x \<noteq> z" using 2(1) unfolding p by auto
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (App (Fix f x Q) E) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" and hQ: "h \<notin> FVars Q"
      using av by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 2(3)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    have hFix: "h \<notin> FVars (Fix f x Q)" and holeFix: "hole \<notin> FVars (Fix f x Q)"
      using hQ 2(4) by auto
    have ctx: "eval_ctx h ((App (Fix f x Q) E')[N <- z])" if hN: "h \<notin> FVars N" for N
    proof -
      obtain f2 x2 Q2 where push: "(Fix f x Q)[N <- z] = Fix f2 x2 Q2" and
          f2: "f2 \<notin> {h}" "x2 \<notin> {h}" and
          FQ2: "FVars Q2 \<subseteq> (FVars Q - {f, x} - {z}) \<union> FVars N \<union> {f2, x2}"
        using usubst_Fix_push[of "{h}" f x Q N z] by auto
      have "h \<notin> FVars Q2" using FQ2 f2 hQ hN by auto
      then have "eval_ctx h (App (Fix f2 x2 Q2) (E'[N <- z]))"
        using E'(1) hN eval_ctx.intros(2) by blast
      then show ?thesis using push by simp
    qed
    have eqn: "(App (Fix f x Q) E)[Var z <- hole] = (App (Fix f x Q) E')[Var z <- h]"
      using E'(2) hFix holeFix by simp
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (App (Fix f x Q) E)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (App (Fix f x Q) E) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "App (Fix f x Q) E'"])
      using ctx eqn E'(3) holeFix by auto
  qed
next
  case (3 hole E Na p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (App E Na) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" and hNa: "h \<notin> FVars Na" by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 3(2)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    have ctx: "eval_ctx h ((App E' Na)[N <- z])" if hN: "h \<notin> FVars N" for N
      using E'(1) hN hNa eval_ctx.intros(3) by force
    have eqn: "(App E Na)[Var z <- hole] = (App E' Na)[Var z <- h]"
      using E'(2) hNa 3(3) by simp
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (App E Na)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (App E Na) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "App E' Na"])
      using ctx eqn E'(3) 3(3) by auto
  qed
next
  case (4 hole E p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (Succ E) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 4(2)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (Succ E)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (Succ E) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "Succ E'"])
      using E' eval_ctx.intros(4) by auto
  qed
next
  case (5 hole E p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (Pred E) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 5(2)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (Pred E)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (Pred E) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "Pred E'"])
      using E' eval_ctx.intros(5) by auto
  qed
next
  case (6 hole E Na p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (term.Pair E Na) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" and hNa: "h \<notin> FVars Na" by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 6(2)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    have ctx: "eval_ctx h ((term.Pair E' Na)[N <- z])" if hN: "h \<notin> FVars N" for N
      using E'(1) hN hNa eval_ctx.intros(6) by force
    have eqn: "(term.Pair E Na)[Var z <- hole] = (term.Pair E' Na)[Var z <- h]"
      using E'(2) hNa 6(3) by simp
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (term.Pair E Na)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (term.Pair E Na) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "term.Pair E' Na"])
      using ctx eqn E'(3) 6(3) by auto
  qed
next
  case (7 V hole E p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (term.Pair V E) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" and hV: "h \<notin> FVars V \<union> {z}" by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 7(3)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    from val_hole[OF 7(1) hV] show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (term.Pair V E)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (term.Pair V E) - {hole}) \<union> {h, z}"
    proof (elim disjE exE)
      assume L: "\<forall>N. val (V[N <- z])"
      have ctx: "eval_ctx h ((term.Pair V E')[N <- z])" if hN: "h \<notin> FVars N" for N
      proof -
        have "val (V[N <- z])" using L by blast
        moreover have "h \<notin> FVars (V[N <- z])" using hV hN by (auto simp: FVars_usubst)
        ultimately show ?thesis using E'(1) hN eval_ctx.intros(7) by auto
      qed
      have eqn: "(term.Pair V E)[Var z <- hole] = (term.Pair V E')[Var z <- h]"
        using E'(2) hV 7(4) by simp
      show ?thesis
        apply (rule exI[of _ "term.Pair V E'"])
        using ctx eqn E'(3) 7(4) by auto
    next
      fix EV assume R: "(\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (EV[N <- z])) \<and> V = EV[Var z <- h] \<and>
        FVars EV \<subseteq> FVars V \<union> {h}"
      define Rst where "Rst \<equiv> E[Var z <- hole]"
      have hRst: "h \<notin> FVars Rst"
        unfolding Rst_def using hE' by (auto simp: FVars_usubst)
      have ctx: "eval_ctx h ((term.Pair EV Rst)[N <- z])" if hN: "h \<notin> FVars N" for N
      proof -
        have "eval_ctx h (EV[N <- z])" using R hN by blast
        moreover have "h \<notin> FVars (Rst[N <- z])" using hRst hN by (auto simp: FVars_usubst)
        ultimately show ?thesis using eval_ctx.intros(6) by auto
      qed
      have eqn: "(term.Pair V E)[Var z <- hole] = (term.Pair EV Rst)[Var z <- h]"
        using R hRst 7(4) unfolding Rst_def by simp
      have FR: "FVars Rst \<subseteq> (FVars E - {hole}) \<union> {z}"
        unfolding Rst_def by (auto simp: FVars_usubst)
      show ?thesis
        apply (rule exI[of _ "term.Pair EV Rst"])
        using ctx eqn R FR 7(4) by auto
    qed
  qed
next
  case (8 hole E Na xy p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  have av: "dset xy \<inter> {z, h} = {}" using 8(1) unfolding p by auto
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (term.Let xy E Na) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" and hNa: "h \<notin> FVars Na"
      using av by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 8(3)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    have ctx: "eval_ctx h ((term.Let xy E' Na)[N <- z])" if hN: "h \<notin> FVars N" for N
    proof -
      obtain xy2 Na2 where push: "(term.Let xy E' Na)[N <- z] = term.Let xy2 (E'[N <- z]) Na2"
          and xy2: "dset xy2 \<inter> {h} = {}"
          and FNa2: "FVars Na2 \<subseteq> (FVars Na - dset xy - {z}) \<union> FVars N \<union> dset xy2"
        using usubst_Let_push[of "{h}" xy E' Na N z] by auto
      have "h \<notin> FVars Na2" using FNa2 xy2 hNa hN by auto
      then have "eval_ctx h (term.Let xy2 (E'[N <- z]) Na2)"
        using E'(1) hN xy2 eval_ctx.intros(8) by blast
      then show ?thesis using push by simp
    qed
    have eqn: "(term.Let xy E Na)[Var z <- hole] = (term.Let xy E' Na)[Var z <- h]"
      using usubst_Let[of hole xy "Var z" E Na] usubst_Let[of h xy "Var z" E' Na]
        av 8(5) E'(2) hNa 8(4) by auto
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (term.Let xy E Na)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (term.Let xy E Na) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "term.Let xy E' Na"])
      using ctx eqn E'(3) 8(4,5) by auto
  qed
next
  case (9 hole E Na Pa p)
  obtain z h where p: "p = (z, h)" by (metis surj_pair)
  show ?case unfolding p prod.case
  proof (intro impI)
    assume hE: "h \<notin> FVars (term.If E Na Pa) \<union> {z}"
    then have hE': "h \<notin> FVars E \<union> {z}" and hNa: "h \<notin> FVars Na" and hPa: "h \<notin> FVars Pa"
      by auto
    obtain E' where E': "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E'[N <- z])"
        "E[Var z <- hole] = E'[Var z <- h]" "FVars E' \<subseteq> (FVars E - {hole}) \<union> {h, z}"
      using 9(2)[THEN spec[of _ "(z, h)"]] hE' unfolding prod.case by blast
    have ctx: "eval_ctx h ((term.If E' Na Pa)[N <- z])" if hN: "h \<notin> FVars N" for N
      using E'(1) hN hNa hPa eval_ctx.intros(9) by force
    have eqn: "(term.If E Na Pa)[Var z <- hole] = (term.If E' Na Pa)[Var z <- h]"
      using E'(2) hNa hPa 9(3,4) by simp
    show "\<exists>Ea. (\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (Ea[N <- z])) \<and>
        (term.If E Na Pa)[Var z <- hole] = Ea[Var z <- h] \<and>
        FVars Ea \<subseteq> (FVars (term.If E Na Pa) - {hole}) \<union> {h, z}"
      apply (rule exI[of _ "term.If E' Na Pa"])
      using ctx eqn E'(3) 9(3,4) by auto
  qed
qed

lemma blocked_fresh_hole:
  assumes "finite A"
  shows "blocked z M = (\<exists> hole E. (\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- z]) \<and> (M = E[Var z <- hole]) \<and> (hole \<notin> insert z A))"
proof (rule iffI)
  assume "blocked z M"
  then obtain hole0 E0 where ctx0: "eval_ctx hole0 E0" and M0: "M = E0[Var z <- hole0]"
    unfolding blocked_def by blast
  obtain h where h: "h \<notin> insert z (A \<union> FVars E0)"
    by (metis arb_element assms finite_FVars finite_Un finite_insert)
  then have "h \<notin> FVars E0 \<union> {z}" by auto
  then obtain E where "\<forall>N. h \<notin> FVars N \<longrightarrow> eval_ctx h (E[N <- z])"
      "E0[Var z <- hole0] = E[Var z <- h]"
    using blocked_fresh_hole_aux[OF ctx0, THEN spec[of _ "(z, h)"]] unfolding prod.case by blast
  then show "\<exists> hole E. (\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- z]) \<and> (M = E[Var z <- hole]) \<and> hole \<notin> insert z A"
    using M0 h by auto
next
  assume "\<exists> hole E. (\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- z]) \<and> (M = E[Var z <- hole]) \<and> hole \<notin> insert z A"
  then show "blocked z M"
    by (auto 0 3 simp: blocked_def usubst_def term.Sb_Inj dest!: spec[of _ "Var z"])
qed

lemma eval_ctx_fresh:
  fixes A :: "'var::var set" and hole :: 'var and z and E
  assumes fnt: "finite A" and ctx: "eval_ctx hole E"
  shows "\<exists>hole' E'. (\<forall>N. hole' \<notin> FVars N \<longrightarrow> eval_ctx hole' E'[N <- z]) \<and> (hole' \<notin> A)"
proof -
  have "E = E[Var hole <- hole]" using subst_iden by simp
  then have "blocked hole E" unfolding blocked_def
    using ctx by blast
  then obtain hole' :: "'var :: var" and E' where "\<forall>N. hole' \<notin> FVars N \<longrightarrow> eval_ctx hole' E'[N <- z]" and "hole' \<notin> A"
    using fnt blocked_fresh_hole by (metis blocked_def insert_iff)
  then show ?thesis
    by auto
qed

text \<open>The naive @{text "val V \<Longrightarrow> V \<noteq> Var x \<Longrightarrow> val V[Q <- x]"} is false (e.g.
  @{text "V = Pair (Var x) Zero"} with non-value @{text Q}); unblockedness is the right hypothesis.\<close>
lemma val_subst_unblocked: "val V \<Longrightarrow> \<not> blocked x V \<Longrightarrow> val V[Q <- x]"
  apply(binder_induction V avoiding: "App Q (Var x)" rule: val.strong_induct)
  subgoal for xa by (metis blocked_inductive(1) usubst_simps(5) val.intros(1))
  subgoal for n by (simp add: val.intros(2))
  subgoal for Va W by (metis blocked_inductive(6,7) usubst_simps(8) val.intros(3))
  subgoal for f xa Ma by (auto intro: val.intros)
  done

text \<open>NB: for general @{term Q} this is FALSE (hence the author's "Questionably True"):
  @{term "Pair (Var y) (Var x)"} is an evaluation context, but its substitution instance
  @{term "Pair Q (Var x)"} is one only when @{term "val Q"} (the hole sits right of a
  value position). With @{term "val Q"} it is true:\<close>
lemma eval_ctx_subst: "eval_ctx x E \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> FVars Q \<Longrightarrow> val Q \<Longrightarrow> eval_ctx x E[Q <- y]"
proof (binder_induction x E avoiding: "App Q (Var y)" E rule: eval_ctx.strong_induct)
  case (1 hole)
  then show ?case by (auto intro: eval_ctx.intros)
next
  case (2 hole Ea M f xa)
  have push: "(App (Fix f xa M) Ea)[Q <- y] = App (Fix f xa (M[Q <- y])) (Ea[Q <- y])"
    using 2(1) by (auto simp: disjoint_iff)
  have hM: "hole \<notin> FVars (M[Q <- y])"
    using 2(4,6) FVars_usubst[of M Q y] by (auto split: if_splits)
  show ?case unfolding push by (rule eval_ctx.intros(2)[OF 2(8)[OF 2(5,6,7)] hM])
next
  case (3 hole Ea N)
  have hN: "hole \<notin> FVars (N[Q <- y])" using 3(2,4) FVars_usubst[of N Q y] by (auto split: if_splits)
  show ?case using eval_ctx.intros(3)[OF 3(6)[OF 3(3,4,5)] hN] by simp
next
  case (4 hole Ea)
  then show ?case using eval_ctx.intros(4)[OF 4(5)[OF 4(2,3,4)]] by simp
next
  case (5 hole Ea)
  then show ?case using eval_ctx.intros(5)[OF 5(5)[OF 5(2,3,4)]] by simp
next
  case (6 hole Ea N)
  have hN: "hole \<notin> FVars (N[Q <- y])" using 6(2,4) FVars_usubst[of N Q y] by (auto split: if_splits)
  show ?case using eval_ctx.intros(6)[OF 6(6)[OF 6(3,4,5)] hN] by simp
next
  case (7 V hole Ea)
  have vQ: "val (V[Q <- y])" using 7(1,6) val_usubst by auto
  have hV: "hole \<notin> FVars (V[Q <- y])" using 7(3,5) FVars_usubst[of V Q y] by (auto split: if_splits)
  show ?case using eval_ctx.intros(7)[OF vQ 7(7)[OF 7(4,5,6)] hV] by simp
next
  case (8 hole Ea N xy)
  have push: "(term.Let xy Ea N)[Q <- y] = term.Let xy (Ea[Q <- y]) (N[Q <- y])"
    using 8(1,2) by (subst usubst_simps(9)) (auto simp: disjoint_iff)
  have hN: "hole \<notin> FVars (N[Q <- y])" using 8(4,7) FVars_usubst[of N Q y] by (auto split: if_splits)
  show ?case unfolding push by (rule eval_ctx.intros(8)[OF 8(9)[OF 8(6,7,8)] hN 8(5)])
next
  case (9 hole Ea N P)
  have hN: "hole \<notin> FVars (N[Q <- y])" using 9(2,5) FVars_usubst[of N Q y] by (auto split: if_splits)
  have hP: "hole \<notin> FVars (P[Q <- y])" using 9(3,5) FVars_usubst[of P Q y] by (auto split: if_splits)
  show ?case using eval_ctx.intros(9)[OF 9(7)[OF 9(4,5,6)] hN hP] by simp
qed

lemma count_idle[simp]: "x \<notin> FVars M \<Longrightarrow> count_term x M = 0"
  apply(binder_induction M avoiding: "App (Var x) M" rule:term.strong_induct)
  apply(auto simp add: Int_Un_distrib)
  done

lemma count_eval_ctx: "eval_ctx hole E \<Longrightarrow> count_term hole E = 1"
  apply(binder_induction hole E avoiding: "Var hole" E rule:eval_ctx.strong_induct)
          apply(auto)
  apply (subst count_term_simps)
    apply auto
  done

lemma count_subst: "x \<noteq> y \<Longrightarrow> count_term y M[Q <- x] = (count_term x M)*(count_term y Q) + count_term y M"
  apply(binder_induction M avoiding: "App (App M Q) (App (Var x) (Var y))" rule:term.strong_induct)
          apply(auto simp add: Int_Un_distrib distrib_right)
  subgoal premises prems for x1 x2 x3
  proof -
    have "dset x1 \<inter> FVars x2[Q <- x] = {}" 
      using FVars_usubst[of x2 Q x] prems(4, 5, 6, 7)
      by auto
    then show ?thesis
      using prems count_term_simps(9)[of y x1 "x2[Q <- x]" "x3[Q <- x]"]
      by auto
  qed
  done

lemma betas_path_exists: 
  "M \<rightarrow>[m] P \<Longrightarrow> n \<le> m \<Longrightarrow> \<exists>N. M \<rightarrow>[n] N \<and> N \<rightarrow>[m - n] P"
proof (induction n)
  case 0
  then show ?case using betas.refl by auto
next
  case (Suc n)
  then obtain N where "M \<rightarrow>[n] N" and "N \<rightarrow>[m - n] P" by auto
  show ?case using \<open>N \<rightarrow>[m - n] P\<close> 
  proof(cases rule:betas.cases)
    case refl
    then show ?thesis using \<open>Suc n \<le> m\<close> by auto
  next
    case (step N' n')
    then have "n' = m - Suc n" by auto
    moreover have "M \<rightarrow>[Suc n] N'" using \<open>M \<rightarrow>[n] N\<close> \<open>N \<rightarrow> N'\<close> betas_pets by auto
    ultimately show ?thesis using \<open>N' \<rightarrow>[n'] P\<close> by auto
  qed
qed

lemma beta_path_diff: 
  "M \<rightarrow>[p] P \<Longrightarrow> n \<le> p \<Longrightarrow> M \<rightarrow>[n] N \<Longrightarrow> N \<rightarrow>[p-n] P"
proof -
  assume "M \<rightarrow>[p] P" and "n \<le> p" and \<open>M \<rightarrow>[n] N\<close>
  then obtain N' where "M \<rightarrow>[n] N'" and "N' \<rightarrow>[p - n] P" using betas_path_exists by blast
  then have "N' = N" using \<open>M \<rightarrow>[n] N\<close> betas_deterministic by auto
  then show ?thesis using \<open>N' \<rightarrow>[p - n] P\<close> by auto
qed

lemma normalize_longest_beta: 
  "normal N \<Longrightarrow> M \<rightarrow>[n] N \<Longrightarrow> M \<rightarrow>[m] M' \<Longrightarrow> n \<ge> m"
proof (rule ccontr)
  assume normalN: "normal N" and "M \<rightarrow>[n] N" and "M \<rightarrow>[m] M'" and "\<not> m \<le> n"
  then have "N \<rightarrow>[m-n] M'" 
    using beta_path_diff[of M m M' n] by auto
  then show False using \<open>\<not> m \<le> n\<close>
  proof (cases rule:betas.cases)
    case (step N n)
    then show ?thesis using normalN normal_def by auto
  qed(auto)
qed

lemma beta_subst_unblocked:
  "M \<rightarrow> N \<Longrightarrow> \<not> blocked z M \<Longrightarrow> M[Q <- z] \<rightarrow> N[Q <- z]"
proof(binder_induction M N avoiding: "App M (App (Var z) Q)" rule:beta.strong_induct)
  case (OrdApp2 N N' f x M)
  then have "\<not> blocked z N" using 
      blocked_inductive(2) by blast
  then show ?case using OrdApp2 by (auto intro: beta.intros)
next
  case (OrdPair2 V Na N')
  then have "\<not> blocked z Na" using
      blocked_inductive by fast
  have "\<not> blocked z V" using \<open>\<not> blocked z (Pair V Na)\<close> blocked_inductive(6) by metis
  then have "val V[Q <- z]" using \<open>val V\<close> val_subst_unblocked by auto
  then show ?case using OrdPair2 beta.intros(6) \<open>\<not> blocked z Na\<close> by auto
next
  case (OrdLet Ma M' xy Na)
  have av: "z \<notin> dset xy" "dset xy \<inter> FVars Q = {}" "dset xy \<inter> FVars Ma = {}" "dset xy \<inter> FVars M' = {}"
    using OrdLet(1) FVars_beta[OF OrdLet(2)] by (auto simp: disjoint_iff subset_iff)
  have nb: "\<not> blocked z Ma" using OrdLet(3) blocked_inductive(8) av(1,3) by metis
  have push1: "(term.Let xy Ma Na)[Q <- z] = term.Let xy (Ma[Q <- z]) (Na[Q <- z])"
    by (rule usubst_simps(9)[OF av(1) av(2) av(3)])
  have push2: "(term.Let xy M' Na)[Q <- z] = term.Let xy (M'[Q <- z]) (Na[Q <- z])"
    by (rule usubst_simps(9)[OF av(1) av(2) av(4)])
  show ?case unfolding push1 push2 by (rule beta.OrdLet[OF OrdLet(4)[OF nb]])
next
  case (Let V W xy Ma)
  have av: "z \<notin> dset xy" "dset xy \<inter> FVars Q = {}" "dset xy \<inter> FVars (term.Pair V W) = {}"
    using Let(1) by (auto simp: disjoint_iff)
  have nbP: "\<not> blocked z (term.Pair V W)"
    using Let(5) blocked_inductive(8) av(1,3) by metis
  have nbV: "\<not> blocked z V" using nbP blocked_inductive(6) by metis
  have nbW: "\<not> blocked z W" using nbP Let(2) blocked_inductive(7) by metis
  have vV: "val (V[Q <- z])" using Let(2) nbV val_subst_unblocked by auto
  have vW: "val (W[Q <- z])" using Let(3) nbW val_subst_unblocked by auto
  have fr: "dset xy \<inter> FVars (V[Q <- z]) = {}"
    using Let(4) av(2) FVars_usubst[of V Q z] by (auto simp: disjoint_iff split: if_splits)
  have push: "(term.Let xy (term.Pair V W) Ma)[Q <- z] = term.Let xy (term.Pair (V[Q <- z]) (W[Q <- z])) (Ma[Q <- z])"
    using av by simp
  have subst_comm: "Ma[V <- dfst xy][W <- dsnd xy][Q <- z] = Ma[Q <- z][V[Q <- z] <- dfst xy][W[Q <- z] <- dsnd xy]"
    using usubst_usubst[of "dsnd xy" z Q "Ma[V <- dfst xy]" W] usubst_usubst[of "dfst xy" z Q Ma V] av(1,2)
    by (metis Int_emptyD dsel_dset(1,2))
  have step: "term.Let xy (term.Pair (V[Q <- z]) (W[Q <- z])) (Ma[Q <- z]) \<rightarrow> Ma[Q <- z][V[Q <- z] <- dfst xy][W[Q <- z] <- dsnd xy]"
    by (rule beta.Let[OF vV vW fr])
  show ?case unfolding push using step subst_comm by simp
next
  case (FixBeta V f xa Ma)
  have av: "f \<noteq> z" "xa \<noteq> z" "f \<notin> FVars Q" "xa \<notin> FVars Q"
    using FixBeta(1) by (auto simp: disjoint_iff)
  have nbV: "\<not> blocked z V" using FixBeta(4) blocked_inductive(2) by metis
  have vV: "val (V[Q <- z])" using FixBeta(2) nbV val_subst_unblocked by auto
  have fr: "f \<notin> FVars (V[Q <- z])"
    using FixBeta(3) av(3) FVars_usubst[of V Q z] by (auto split: if_splits)
  have pushF: "(Fix f xa Ma)[Q <- z] = Fix f xa (Ma[Q <- z])"
    using av by simp
  have push: "(App (Fix f xa Ma) V)[Q <- z] = App (Fix f xa (Ma[Q <- z])) (V[Q <- z])"
    using pushF by simp
  have subst_comm: "Ma[V <- xa][Fix f xa Ma <- f][Q <- z] = Ma[Q <- z][V[Q <- z] <- xa][Fix f xa (Ma[Q <- z]) <- f]"
    using usubst_usubst[of f z Q "Ma[V <- xa]" "Fix f xa Ma"] usubst_usubst[of xa z Q Ma V] av pushF
    by metis
  have step: "App (Fix f xa (Ma[Q <- z])) (V[Q <- z]) \<rightarrow> Ma[Q <- z][V[Q <- z] <- xa][Fix f xa (Ma[Q <- z]) <- f]"
    by (rule beta.FixBeta[OF vV fr])
  show ?case unfolding push using step subst_comm by simp
qed(auto intro:beta.intros blocked_inductive)

lemma my_induct[case_names lex]:
  assumes "\<And>n N. (\<And>m M. m < n \<Longrightarrow> P m x M) \<Longrightarrow> (\<And>M. count_term x M < count_term x N \<Longrightarrow> P n x M) \<Longrightarrow> P n x N"
  shows "P (n :: nat) x (N :: 'a :: var term)"
  apply (induct "(n, N)" arbitrary: n N rule: wf_induct[OF wf_mlex[OF wf_measure], of fst "count_term x o snd"])
  apply (auto simp add: mlex_iff intro: assms)
  done

lemma b4:
  assumes "M[N <- x] \<rightarrow>[k] P" and "normal P" and "Q \<lesssim> N" and "x \<notin> FVars N" 
  shows "diverge M[Q <- x] \<or> (\<exists>m M'. P = M'[N <- x] \<and> M[Q <- x] \<rightarrow>[m] M'[Q <- x])"
  using assms
proof (induct k x M rule: my_induct)
  case (lex k M)
  show ?case
    using lex(3)
  proof (cases rule:betas.cases)
    case refl
    then have "P = M[N <- x]" and "M[Q <- x] \<rightarrow>[k] M[Q <- x]"
       using betas.intros by auto
    then show ?thesis by auto
  next
    case (step P' k')
    then show ?thesis
    proof (cases "blocked x M")
      case True
      then obtain hole E where strong_eval: "\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- x]" and "M = E[Var x <- hole]" 
        and fresh1: "hole \<noteq> x" and fresh2: "hole \<notin> FVars Q \<union> FVars N"
        using blocked_fresh_hole[of "FVars Q \<union> FVars N" x M]
        using finite_FVars
        by auto
      then have "M[N <- x] = E[N <- x][N <- hole]" and "M[Q <- x] = E[Q <- x][Q <- hole]"
        using usubst_usubst[of hole x N E "Var x"] usubst_usubst[of hole x Q E "Var x"]
        by auto
      have eval: "eval_ctx hole E" 
        using strong_eval subst_iden[of E x] \<open>hole \<noteq> x\<close>
        using spec[of "\<lambda>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- x]" "Var x"]
        by simp
      have "eval_ctx hole E[Q <- x]" and "eval_ctx hole E[N <- x]"
        using strong_eval fresh2 by auto
      show ?thesis
      proof (cases "diverge Q")
        case True
        then have "diverge M[Q <- x]"
          using div_ctx[of hole "E[Q <- x]" Q] \<open>M[Q <- x] = E[Q <- x][Q <- hole]\<close>
          using \<open>eval_ctx hole E[Q <- x]\<close> by auto
        then show ?thesis by simp
      next
        case False
        then obtain N' where "normal N'" and "N \<rightarrow>* N'" and "Q \<rightarrow>* N'"
          using less_defined_def \<open>Q \<lesssim> N\<close> diverge_or_normalizes[of Q] by auto
        moreover have "x \<notin> FVars N'" using \<open>x \<notin> FVars N\<close> \<open>N \<rightarrow>* N'\<close> FVars_beta_star by auto
        ultimately have "M[N <- x] \<rightarrow>* E[N <- x][N' <- hole]" and "M[Q <- x] \<rightarrow>* E[Q <- x][N' <- hole]"
          using \<open>M[N <- x] = E[N <- x][N <- hole]\<close> \<open>M[Q <- x] = E[Q <- x][Q <- hole]\<close> 
          using \<open>eval_ctx hole E[N <- x]\<close> \<open>eval_ctx hole E[Q <- x]\<close>
          using eval_ctx_beta_star
          by auto
        then obtain m where steps: "E[N <- x][N' <- hole] \<rightarrow>[m] P" and steps_less: "m \<le> k"
          using beta_star_def[of "M[N <- x]"] lex(3) lex(4)
          using normalize_longest_beta[of P "M[N <- x]" k _ "E[N <- x][N' <- hole]"] 
          using beta_path_diff[of _]
          using diff_le_self by blast
        have counts_less: "count_term x E[N' <- hole] < count_term x M"
        proof -
          have "count_term x E[N' <- hole] = count_term x E"
            using count_subst[of hole x E N'] \<open>x \<notin> FVars N'\<close> count_idle[of x N'] \<open>hole \<noteq> x\<close>
            by auto
          also have "... < count_term x M"
            using count_subst[of hole x E "Var x"] \<open>hole \<noteq> x\<close> \<open>M = E[Var x <- hole]\<close> 
            using count_eval_ctx[of hole E] \<open>eval_ctx hole E\<close> by force
          finally show ?thesis by simp
        qed
        have steps': "E[N' <- hole][N <- x] \<rightarrow>[m] P"
          using steps usubst_usubst[of x hole] \<open>hole \<noteq> x\<close> \<open>x \<notin> FVars N'\<close> \<open>hole \<notin> FVars Q \<union> FVars N\<close>
          by auto
        have "E[N' <- hole][Q <- x] \<Up> \<or> (\<exists>m M'. P = M'[N <- x] \<and> E[N' <- hole][Q <- x] \<rightarrow>[m] M'[Q <- x])"
        proof(cases "m = k")
          case True
          then show ?thesis 
            using counts_less \<open>normal P\<close> \<open>Q \<lesssim> N\<close> \<open>x \<notin> FVars N\<close> steps'
            using lex(2)[of "E[N' <- hole]"]
            by auto
        next
          case False
          then have "m < k" using steps_less by auto
          then show ?thesis
            using steps' \<open>normal P\<close> \<open>Q \<lesssim> N\<close> \<open>x \<notin> FVars N\<close>
            using lex(1)[of m "E[N' <- hole]"]
            by blast
        qed
        then have "E[Q <- x][N' <- hole] \<Up> \<or> (\<exists>m M'. P = M'[N <- x] \<and> E[Q <- x][N' <- hole] \<rightarrow>[m] M'[Q <- x])"
          using steps usubst_usubst[of x hole] \<open>hole \<noteq> x\<close> \<open>x \<notin> FVars N'\<close> \<open>hole \<notin> FVars Q \<union> FVars N\<close>
          by auto
        moreover have "E[Q <- x][Q <- hole] \<rightarrow>* E[Q <- x][N' <- hole]"
          using eval_ctx_beta_star[of hole "E[Q <- x]" Q N'] \<open>Q \<rightarrow>* N'\<close> \<open>eval_ctx hole E[Q <- x]\<close>
          by blast
        ultimately have "E[Q <- x][Q <- hole] \<Up> \<or> (\<exists>m M'. P = M'[N <- x] \<and> E[Q <- x][Q <- hole] \<rightarrow>[m] M'[Q <- x])"
          using beta_star_diverge_back[of "E[Q <- x][Q <- hole]" "E[Q <- x][N' <- hole]"]
          using betas_path_sum beta_star_def
          by blast
        then show ?thesis using \<open>M[Q <- x] = E[Q <- x][Q <- hole]\<close> by auto
      qed
    next
      case False
      then obtain M'' where "M \<rightarrow> M''" and "P' = M''[N <- x]"
        using step(2) b3[of M N x P'] by auto
      then have "M''[N <- x] \<rightarrow>[k'] P"
        using step(3) by simp
      then have "diverge M''[Q <- x] \<or> (\<exists>m M'. P = M'[N <- x] \<and> M''[Q <- x] \<rightarrow>[m] M'[Q <- x])"
        using step(1) lex.prems lex(1)[of k' M''] by simp
      moreover have "M[Q <- x] \<rightarrow> M''[Q <- x]"
        using beta_subst_unblocked \<open>M \<rightarrow> M''\<close> \<open>\<not> blocked x M\<close> by auto
      ultimately show ?thesis
        using diverge.intros[of "M[Q <- x]" "M''[Q <- x]"]
        using betas.step[of "M[Q <- x]" "M''[Q <- x]" _ _]
        by blast
    qed
  qed
qed

section \<open>B5\<close>

inductive haveFix :: "'var::var term \<Rightarrow> bool" where
  "haveFix (Fix _ _ _)"
| "haveFix N \<Longrightarrow> haveFix (Succ N)"
| "haveFix N \<Longrightarrow> haveFix (Pred N)"
| "haveFix N \<Longrightarrow> haveFix (If N _ _)"
| "haveFix N \<Longrightarrow> haveFix (If _ N _)"
| "haveFix N \<Longrightarrow> haveFix (If _ _ N)"
| "haveFix N \<Longrightarrow> haveFix (App N _)"
| "haveFix N \<Longrightarrow> haveFix (App _ N)"
| "haveFix N \<Longrightarrow> haveFix (Fix _ _ N)"
| "haveFix N \<Longrightarrow> haveFix (Pair N _)"
| "haveFix N \<Longrightarrow> haveFix (Pair _ N)"
| "haveFix N \<Longrightarrow> haveFix (Let _ N _)"
| "haveFix N \<Longrightarrow> haveFix (Let _ _ N)"

lemma haveFix_Pair:
  assumes "\<not> haveFix (Pair V1 V2)"
  shows "\<not> haveFix V1" and "\<not> haveFix V2"
   apply(rule contrapos_nn[of "haveFix (Pair V1 V2)"])
  subgoal using assms by auto
   prefer 2
   apply(rule contrapos_nn[of "haveFix (Pair V1 V2)"])
  subgoal using assms by auto
   apply(auto intro:haveFix.intros)
  done

text \<open>The @{text Fix} clause of @{text b5_prop} quantifies over ALL binder representations of
  @{term V}. Guarding it only by \<open>z \<noteq> f\<close>, \<open>z \<noteq> x\<close> (as originally) makes the property FALSE for
  open @{term P}: take \<open>V = Fix f x (Pair (Var y) Zero)\<close>, \<open>M = Fix f x (Pair (Var y) (Var z))\<close>,
  \<open>N = Zero\<close> and a binder name \<open>f2 \<in> FVars P\<close>, \<open>f2 \<noteq> y\<close> --- then \<open>V = Fix f2 x (Pair (Var y) Zero)\<close>
  is a valid representation, but the only reachable value \<open>W = Fix f x (Pair (Var y) P)\<close> has
  \<open>f2 \<in> FVars W\<close>, so no representation of @{term W} with binder \<open>f2\<close> exists. (The paper avoids
  this by considering closed programs; the formalization's @{text less_defined} does not require
  closedness.) We therefore also require the binders to avoid @{term "FVars N \<union> FVars P"};
  consumers instantiate the clause with an alpha-refreshed representation (@{text Fix_refresh}).\<close>
definition b5_prop :: "'var::var term \<Rightarrow> 'var term \<Rightarrow> 'var term \<Rightarrow> 'var term \<Rightarrow> 'var \<Rightarrow>  bool" where
  "b5_prop V W P N z \<equiv> (\<not> haveFix V \<longrightarrow> W = V) \<and>
    (\<forall>V1 V2. V = Pair V1 V2 \<longrightarrow> (\<exists>W1 W2. W = Pair W1[P <- z] W2[P <- z] \<and> W1[N <- z] = V1 \<and> W2[N <- z] = V2)) \<and>
    (\<forall>f x R. V = Fix f x R \<longrightarrow> f \<notin> FVars N \<union> FVars P \<union> {z} \<longrightarrow> x \<notin> FVars N \<union> FVars P \<union> {z} \<longrightarrow>
      (\<exists>Q. W = Fix f x Q[P <- z] \<and> Q[N <- z] = R))"

lemma Succ_beta_star: "n \<rightarrow>* m \<Longrightarrow> Succ n \<rightarrow>* Succ m"
proof -
  assume "n \<rightarrow>* m"
  obtain x :: 'a where "eval_ctx x (Succ (Var x))"
    using eval_ctx.intros by blast
  then show ?thesis
    using eval_ctx_beta_star[of x "Succ (Var x)" n m] \<open>n \<rightarrow>* m\<close>
    by simp
qed

lemma Pred_beta_star: "n \<rightarrow>* m \<Longrightarrow> Pred n \<rightarrow>* Pred m"
proof -
  assume "n \<rightarrow>* m"
  obtain x :: 'a where "eval_ctx x (Pred (Var x))"
    using eval_ctx.intros by blast
  then show ?thesis
    using eval_ctx_beta_star[of x "Pred (Var x)" n m] \<open>n \<rightarrow>* m\<close>
    by simp
qed

lemma Pair_betas:
  assumes m: "M \<rightarrow>[m] M'" and n: "N \<rightarrow>[n] N'" and v:"val M'"
  shows "Pair M N \<rightarrow>[m+n] Pair M' N'"
proof -
  have "Pair M N \<rightarrow>[m] Pair M' N" using m
    apply(induction rule:betas.induct)
     apply(auto intro: betas.intros beta.intros)
    done
  moreover have "Pair M' N \<rightarrow>[n] Pair M' N'" using n v
    apply(induction rule:betas.induct)
     apply(auto intro: betas.intros beta.intros)
    done
  ultimately show ?thesis using betas_path_sum by blast
qed

corollary Pair_beta_star: "M \<rightarrow>* M' \<Longrightarrow> N \<rightarrow>* N' \<Longrightarrow> val M' \<Longrightarrow> Pair M N \<rightarrow>* Pair M' N'"
  using Pair_betas beta_star_def by metis

lemma Pair_div: "diverge M \<Longrightarrow> diverge (Pair M N)"
proof(coinduction arbitrary: M N rule:diverge.coinduct)
  case diverge
  then obtain M' where "Pair M N \<rightarrow> Pair M' N" and "diverge M'"
    using diverge.cases beta.intros(5) by metis
  then show ?case by auto
qed

lemma Pair_div2:
  fixes V N :: "'a::var term"
  assumes "val V" and "diverge N"
  shows "diverge (Pair V N)"
proof -
  obtain hole :: 'a where hole: "hole \<notin> FVars V"
    by (metis arb_element finite_FVars)
  have "eval_ctx hole (term.Pair V (Var hole))"
    using eval_ctx.intros(7)[OF assms(1) eval_ctx.intros(1) hole] .
  then have "diverge ((term.Pair V (Var hole))[N <- hole])"
    using div_ctx assms(2) by blast
  then show ?thesis using hole by simp
qed

lemma b5_prop_reflexive: 
  assumes "val V" and "z \<notin> FVars V" 
  shows "b5_prop V V P N z"
  using \<open>val V\<close> \<open>z \<notin> FVars V\<close>
proof(binder_induction V avoiding: z rule: val.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1, case_names 0 1 2 3 4])
  case (1 x)
  then show ?case unfolding b5_prop_def by auto
next
  case (2 n)
  then show ?case
  proof(cases n rule:num.cases)
  qed(auto simp add:b5_prop_def)
next
  case (3 V1 V2)
  from 3(3) have "z \<notin> FVars V1" and "z \<notin> FVars V2" by auto
  then have "V1 = V1[P <- z] \<and> V2 = V2[P <- z] \<and> V1[N <- z] = V1 \<and> V2[N <- z] = V2" by auto
  then show ?case using b5_prop_def by fastforce
next
  case (4 f x R)
  have "haveFix (Fix f x R)" by (metis haveFix.intros(1))
  moreover { fix f' x' R'
    assume fxR': "f' \<notin> FVars N \<union> FVars P \<union> {z}" "x' \<notin> FVars N \<union> FVars P \<union> {z}" "Fix f x R = Fix f' x' R'"
    then have "z \<notin> FVars (Fix f' x' R')" using 4(2) by metis
    with fxR' have "z \<notin> FVars R'" by auto
    then have "Fix f' x' R'[P <- z] = Fix f' x' R' \<and> R'[N <- z] = R'"
      by simp
  }
  ultimately show ?case using 4(1,2) unfolding b5_prop_def
    apply (auto simp del: term.inject)
    apply metis
    done
qed

thm b5_prop_def

lemma num_not_haveFix: "num n \<Longrightarrow> \<not> haveFix n"
  apply(induction rule:num.induct)
   apply(auto elim:haveFix.cases)
  done

text \<open>From @{text b5_prop} one can always extract a single "interpolating" term whose
  @{term N}-instance is @{term V} and whose @{term P}-instance is @{term W}. This is what the
  @{text Pair} clause of @{text b5_prop} demands of the components in the composite case.\<close>
lemma b5_prop_witness:
  fixes V W P N :: "'a::var term"
  assumes "val V" and "z \<notin> FVars V" and "b5_prop V W P N z"
  shows "\<exists>V'. W = V'[P <- z] \<and> V'[N <- z] = V"
  using assms(1)
proof (cases V rule: val.cases)
  case (1 x)
  then have "\<not> haveFix V" by (auto elim: haveFix.cases)
  then have "W = V" using assms(3) unfolding b5_prop_def by blast
  then show ?thesis using assms(2) by (intro exI[of _ V]) auto
next
  case 2
  then have "\<not> haveFix V" using num_not_haveFix by blast
  then have "W = V" using assms(3) unfolding b5_prop_def by blast
  then show ?thesis using assms(2) by (intro exI[of _ V]) auto
next
  case (3 V1 V2)
  then obtain W1 W2 where "W = Pair W1[P <- z] W2[P <- z]" "W1[N <- z] = V1" "W2[N <- z] = V2"
    using assms(3) unfolding b5_prop_def by blast
  then show ?thesis unfolding 3 by (intro exI[of _ "term.Pair W1 W2"]) auto
next
  case (4 f x R)
  obtain f' x' R' where r: "Fix f x R = Fix f' x' R'"
      and fr: "f' \<notin> FVars N \<union> FVars P \<union> {z}" "x' \<notin> FVars N \<union> FVars P \<union> {z}"
    using Fix_refresh[of "FVars N \<union> FVars P \<union> {z}" f x R] by auto
  then obtain Q where q: "W = Fix f' x' Q[P <- z]" "Q[N <- z] = R'"
    using assms(3) unfolding b5_prop_def 4 by blast
  have "(Fix f' x' Q)[P <- z] = Fix f' x' Q[P <- z]" and "(Fix f' x' Q)[N <- z] = Fix f' x' Q[N <- z]"
    by (rule usubst_simps(7); use fr in auto)+
  then show ?thesis using q r unfolding 4
    apply (intro exI[of _ "Fix f' x' Q"])
    apply (auto)
    by (metis insert_is_Un term.inject(6))
qed

lemma b5_helper:
  assumes "M[N <- z] \<rightarrow>* V" and "val V" and "P \<lesssim> N"
    "V = U[N <- z]" and "M[P <- z] \<rightarrow>* U[P <- z]" and "\<not> diverge M[P <- z]" and "U = Var z" and "z \<notin> FVars V"
  shows "\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
proof -
  have "N = V" and "M[P <- z] \<rightarrow>* P"
    using \<open>V = U[N <- z]\<close> \<open>M[P <- z] \<rightarrow>* U[P <- z]\<close> \<open>U = Var z\<close> by auto
  then show ?thesis
  proof (cases "diverge P")
    case True
    then have "diverge M[P <- z]"
      using \<open>M[P <- z] \<rightarrow>* P\<close> beta_star_diverge_back by blast
    then show ?thesis using \<open>\<not> diverge M[P <- z]\<close> by auto
  next
    case False
    then have "normalizes P" using diverge_or_normalizes by auto
    then obtain N' where "normal N'" and "P \<rightarrow>* N'" and "N \<rightarrow>* N'"
      using less_defined_def \<open>P \<lesssim> N\<close> by auto
    moreover have "N = N'" 
      using \<open>N = V\<close> \<open>val V\<close> vals_are_normal beta_star_def betas.cases normal_def
      by (metis calculation(3))
    ultimately have "P \<rightarrow>* V"
      using \<open>P \<lesssim> N\<close> \<open>N = V\<close> by simp
    then have "val V \<and> M[P <- z] \<rightarrow>* V"
      using betas_path_sum beta_star_def
      using \<open>val V\<close> \<open>M[P <- z] \<rightarrow>* P\<close> 
      by metis
    then show ?thesis using b5_prop_reflexive \<open>z \<notin> FVars V\<close> by blast
  qed
qed

text \<open>@{text "guarded z U"}: every free occurrence of @{text z} in @{text U} sits below a
  fixpoint abstraction. Under this invariant, substituting for @{text z} only touches the bodies
  of @{text fix}-abstractions, which are values regardless of their content, so valueness of
  @{text "U[N <- z]"} is preserved when we substitute a different term for @{text z}. This is the
  invariant that Lemma B.4's construction secretly provides for its witness (the surviving
  @{text z}-occurrences are exactly the never-evaluated ones), and it is what makes Lemma B.5's
  pair case go through.\<close>

inductive guarded :: "'var::var \<Rightarrow> 'var term \<Rightarrow> bool" where
  gVar: "x \<noteq> z \<Longrightarrow> guarded z (Var x)"
| gZero: "guarded z Zero"
| gSucc: "guarded z M \<Longrightarrow> guarded z (Succ M)"
| gPred: "guarded z M \<Longrightarrow> guarded z (Pred M)"
| gApp: "guarded z M \<Longrightarrow> guarded z N \<Longrightarrow> guarded z (App M N)"
| gPair: "guarded z M \<Longrightarrow> guarded z N \<Longrightarrow> guarded z (Pair M N)"
| gIf: "guarded z M \<Longrightarrow> guarded z N \<Longrightarrow> guarded z P \<Longrightarrow> guarded z (If M N P)"
| gLet: "guarded z M \<Longrightarrow> guarded z N \<Longrightarrow> guarded z (Let xy M N)"
| gLetB: "z \<in> dset xy \<Longrightarrow> guarded z M \<Longrightarrow> guarded z (Let xy M N)"
| gFix: "guarded z (Fix f x M)"

lemma guarded_simps[simp]:
  "guarded z (Var x) = (x \<noteq> z)"
  "guarded z Zero"
  "guarded z (Succ M) = guarded z M"
  "guarded z (Pred M) = guarded z M"
  "guarded z (App M1 M2) = (guarded z M1 \<and> guarded z M2)"
  "guarded z (Pair M1 M2) = (guarded z M1 \<and> guarded z M2)"
  "guarded z (If M1 M2 M3) = (guarded z M1 \<and> guarded z M2 \<and> guarded z M3)"
  "guarded z (Fix f x M)"
  by (auto intro: guarded.intros elim: guarded.cases)

lemma val_Succ_num:
  assumes "val (Succ M)" shows "num M"
  using assms by (cases rule: val.cases) (auto elim: num.cases)

lemma val_Pair_D:
  assumes "val (term.Pair M N)" shows "val M \<and> val N"
  using assms by (cases rule: val.cases) (auto elim: num.cases)

lemma not_val_Pred[simp]: "\<not> val (Pred M)"
  by (rule notI, cases rule: val.cases) (auto elim: num.cases)
lemma not_val_App[simp]: "\<not> val (App M1 M2)"
  by (rule notI, cases rule: val.cases) (auto elim: num.cases)
lemma not_val_If[simp]: "\<not> val (If M1 M2 M3)"
  by (rule notI, cases rule: val.cases) (auto elim: num.cases)
lemma not_val_Let[simp]: "\<not> val (term.Let xy M1 M2)"
  by (rule notI, cases rule: val.cases) (auto elim: num.cases)

lemma val_usubst_Let_False: "\<not> val ((term.Let xy M N)[s <- z])"
proof -
  obtain xy' N' where eq: "term.Let xy M N = term.Let xy' M N'"
    and d: "dset xy' \<inter> ({z} \<union> FVars s) = {}"
    using Let_refresh[of "{z} \<union> FVars s" xy M N] finite_FVars by auto
  have "z \<notin> dset xy'" and "dset xy' \<inter> FVars s = {}" using d by auto
  then have "(term.Let xy M N)[s <- z] = term.Let xy' (M[s <- z]) (N'[s <- z])"
    unfolding eq by (rule usubst_Let)
  then show ?thesis by simp
qed

lemma num_guarded_zfree: "num W \<Longrightarrow> W = M[N <- z] \<Longrightarrow> guarded z M \<Longrightarrow> z \<notin> FVars M"
proof (induction W arbitrary: M rule: num.induct)
  case 1
  then have "M = Zero" using subst_Zero_inversion by (metis guarded_simps(1))
  then show ?case by simp
next
  case (2 n)
  from 2 have "M \<noteq> Var z" by auto
  then obtain M' where M': "M = Succ M'" and n: "M'[N <- z] = n"
    using subst_Succ_inversion 2(3) by metis
  have gM': "guarded z M'" using 2(4) M' by simp
  have "z \<notin> FVars M'" using 2 n gM' by blast
  then show ?case using M' by (simp add: FVars_usubst)
qed

lemma val_subst_guarded:
  "guarded z U \<Longrightarrow> val (U[N <- z]) \<Longrightarrow> val (U[P <- z])"
proof (induction U rule: guarded.induct)
  case (gVar x z) then show ?case by simp
next
  case (gZero z) then show ?case by simp
next
  case (gSucc z M)
  then have "num (M[N <- z])" using val_Succ_num by simp
  then have "z \<notin> FVars M" using num_guarded_zfree gSucc.hyps by blast
  then show ?case using gSucc.prems by simp
next
  case (gPred z M) then show ?case using gPred.prems by simp
next
  case (gApp z M Na) then show ?case using gApp.prems by simp
next
  case (gPair z M Na)
  from gPair.prems have "val (M[N <- z]) \<and> val (Na[N <- z])" using val_Pair_D by simp
  then show ?case using gPair.IH by (auto intro: val.intros(3))
next
  case (gIf z M Na Pa) then show ?case using gIf.prems by simp
next
  case (gLet z M Na xy) then show ?case using gLet.prems val_usubst_Let_False by blast
next
  case (gLetB z xy M Na) then show ?case using gLetB.prems val_usubst_Let_False by blast
next
  case (gFix z f x M)
  obtain f' x' M' where eq: "Fix f x M = Fix f' x' M'"
    and f': "f' \<notin> {z} \<union> FVars P" and x': "x' \<notin> {z} \<union> FVars P"
    using Fix_refresh[of "{z} \<union> FVars P" f x M] finite_FVars by auto
  have "(Fix f x M)[P <- z] = Fix f' x' (M'[P <- z])"
    unfolding eq using f' x' by simp
  then show ?case by (simp add: val.intros(4))
qed

lemma guarded_zfree: "z \<notin> FVars M \<Longrightarrow> guarded z M"
proof (binder_induction M avoiding: z rule: term.strong_induct)
  case (Var x) then show ?case by simp
next
  case (Let xy M1 M2)
  then have "z \<notin> FVars M1" and "z \<notin> FVars M2" by auto
  then show ?case using Let.IH by (auto intro: gLet)
next
  case (Fix f x M) then show ?case by simp
qed auto

lemma guardedize:
  assumes zN: "z \<notin> FVars N" and ls: "P \<lesssim> N"
  shows "val (U[N <- z]) \<Longrightarrow>
    diverge (U[P <- z]) \<or> (\<exists>U'. guarded z U' \<and> U'[N <- z] = U[N <- z] \<and> U[P <- z] \<rightarrow>* U'[P <- z])"
proof (binder_induction U avoiding: N P z rule: term.strong_induct,
    goal_cases Zero Succ Pred If Var App Fix Pair Let)
  case Zero
  have "guarded z Zero \<and> Zero[N <- z] = Zero[N <- z] \<and> Zero[P <- z] \<rightarrow>* Zero[P <- z]"
    by (auto simp: beta_star_def intro: betas.refl)
  then show ?case by blast
next
  case (Succ M)
  from Succ(2) have "num (M[N <- z])" using val_Succ_num[of "M[N <- z]"] by simp
  then have vM: "val (M[N <- z])" by (rule val.intros(2))
  from Succ(1)[OF vM] consider (d) "diverge (M[P <- z])"
    | (g) U' where "guarded z U'" "U'[N <- z] = M[N <- z]" "M[P <- z] \<rightarrow>* U'[P <- z]" by blast
  then show ?case
  proof cases
    case d
    obtain h :: 'a where h: "eval_ctx h (Succ (Var h))" using eval_ctx.intros by blast
    have "diverge ((Succ (Var h))[M[P <- z] <- h])" using div_ctx[OF h] d by blast
    then show ?thesis by simp
  next
    case (g U')
    have "guarded z (Succ U') \<and> (Succ U')[N <- z] = (Succ M)[N <- z]
        \<and> (Succ M)[P <- z] \<rightarrow>* (Succ U')[P <- z]"
      using g by (simp add: Succ_beta_star)
    then show ?thesis by blast
  qed
next
  case (Pred M) then show ?case using Pred(2) by simp
next
  case (If M1 M2 M3) then show ?case using If(4) by simp
next
  case (Var y)
  show ?case
  proof (cases "y = z")
    case True
    then have vN: "val N" using Var(1) by simp
    show ?thesis
    proof (cases "diverge P")
      case True then show ?thesis using \<open>y = z\<close> by simp
    next
      case False
      then obtain Nf where Nf: "normal Nf" "P \<rightarrow>* Nf" "N \<rightarrow>* Nf"
        using ls diverge_or_normalizes[of P] unfolding less_defined_def normalizes_def by auto
      have "N = Nf" using Nf(3) vals_are_normal[OF vN] unfolding beta_star_def normal_def
        by (metis betas.cases)
      then have "P \<rightarrow>* N" using Nf(2) by simp
      moreover have "guarded z N" by (rule guarded_zfree[OF zN])
      ultimately have "guarded z N \<and> N[N <- z] = (Var y)[N <- z] \<and> (Var y)[P <- z] \<rightarrow>* N[P <- z]"
        using \<open>y = z\<close> zN by simp
      then show ?thesis by blast
    qed
  next
    case False
    have "guarded z (Var y) \<and> (Var y)[N <- z] = (Var y)[N <- z] \<and> (Var y)[P <- z] \<rightarrow>* (Var y)[P <- z]"
      using False by (auto simp: beta_star_def intro: betas.refl)
    then show ?thesis by blast
  qed
next
  case (App M1 M2) then show ?case using App(3) by simp
next
  case (Fix f x M)
  have "guarded z (Fix f x M) \<and> (Fix f x M)[N <- z] = (Fix f x M)[N <- z]
      \<and> (Fix f x M)[P <- z] \<rightarrow>* (Fix f x M)[P <- z]"
    by (auto simp: beta_star_def intro: betas.refl)
  then show ?case by blast
next
  case (Pair M1 M2)
  from Pair(3) have v1: "val (M1[N <- z])" and v2: "val (M2[N <- z])"
    using val_Pair_D by auto
  from Pair(1)[OF v1] consider (d1) "diverge (M1[P <- z])"
    | (g1) U1 where "guarded z U1" "U1[N <- z] = M1[N <- z]" "M1[P <- z] \<rightarrow>* U1[P <- z]" by blast
  then show ?case
  proof cases
    case d1
    then have "diverge ((Pair M1 M2)[P <- z])" by (simp add: Pair_div)
    then show ?thesis by simp
  next
    case (g1 U1)
    have vU1: "val (U1[P <- z])" using val_subst_guarded g1(1) g1(2) v1 by metis
    have reflW2: "M2[P <- z] \<rightarrow>* M2[P <- z]" using beta_star_def betas.refl by blast
    from Pair(2)[OF v2] consider (d2) "diverge (M2[P <- z])"
      | (g2) U2 where "guarded z U2" "U2[N <- z] = M2[N <- z]" "M2[P <- z] \<rightarrow>* U2[P <- z]" by blast
    then show ?thesis
    proof cases
      case d2
      have "Pair (M1[P <- z]) (M2[P <- z]) \<rightarrow>* Pair (U1[P <- z]) (M2[P <- z])"
        by (rule Pair_beta_star[OF g1(3) reflW2 vU1])
      moreover have "diverge (Pair (U1[P <- z]) (M2[P <- z]))" by (rule Pair_div2[OF vU1 d2])
      ultimately have "diverge (Pair (M1[P <- z]) (M2[P <- z]))"
        using beta_star_diverge_back by blast
      then show ?thesis by simp
    next
      case (g2 U2)
      have "guarded z (Pair U1 U2) \<and> (Pair U1 U2)[N <- z] = (Pair M1 M2)[N <- z]
          \<and> (Pair M1 M2)[P <- z] \<rightarrow>* (Pair U1 U2)[P <- z]"
        using g1 g2 vU1 by (simp add: Pair_beta_star[OF g1(3) g2(3) vU1])
      then show ?thesis by blast
    qed
  qed
next
  case (Let xy M1 M2) then show ?case using Let(3) val_usubst_Let_False by blast
qed

text \<open>@{text b4} specialised to a value target, additionally securing the @{text guarded}
  invariant on the witness (this is the strengthening of Lemma B.4 that the author's proof of
  Lemma B.5 relies on): the value @{text V} is reached as @{text "U[N <- z]"} for some @{text U}
  whose @{text z}-occurrences are all below fixpoint abstractions.\<close>
lemma b4_val:
  assumes "M[N <- z] \<rightarrow>* V" and "val V" and "P \<lesssim> N" and "z \<notin> FVars N"
  shows "diverge (M[P <- z]) \<or> (\<exists>U. guarded z U \<and> V = U[N <- z] \<and> M[P <- z] \<rightarrow>* U[P <- z])"
proof -
  from assms(1) obtain k where "M[N <- z] \<rightarrow>[k] V" unfolding beta_star_def by auto
  then have "diverge (M[P <- z]) \<or> (\<exists>m U0. V = U0[N <- z] \<and> M[P <- z] \<rightarrow>[m] U0[P <- z])"
    using b4[of M N z k V P] vals_are_normal[OF assms(2)] assms(3,4) by auto
  then show ?thesis
  proof
    assume "diverge (M[P <- z])" then show ?thesis by simp
  next
    assume "\<exists>m U0. V = U0[N <- z] \<and> M[P <- z] \<rightarrow>[m] U0[P <- z]"
    then obtain U0 where U0: "V = U0[N <- z]" and st: "M[P <- z] \<rightarrow>* U0[P <- z]"
      unfolding beta_star_def by auto
    have "val (U0[N <- z])" using U0 assms(2) by simp
    then have "diverge (U0[P <- z]) \<or>
        (\<exists>U'. guarded z U' \<and> U'[N <- z] = U0[N <- z] \<and> U0[P <- z] \<rightarrow>* U'[P <- z])"
      using guardedize[OF assms(4) assms(3)] by simp
    then show ?thesis
    proof
      assume "diverge (U0[P <- z])"
      then have "diverge (M[P <- z])" using st beta_star_diverge_back by blast
      then show ?thesis by simp
    next
      assume "\<exists>U'. guarded z U' \<and> U'[N <- z] = U0[N <- z] \<and> U0[P <- z] \<rightarrow>* U'[P <- z]"
      then obtain U' where "guarded z U'" "U'[N <- z] = U0[N <- z]" "U0[P <- z] \<rightarrow>* U'[P <- z]" by auto
      then have "guarded z U' \<and> V = U'[N <- z] \<and> M[P <- z] \<rightarrow>* U'[P <- z]"
        using U0 st beta_star_sums by auto
      then show ?thesis by blast
    qed
  qed
qed

lemma b5_induction:
  assumes "val V" and "z \<notin> FVars N" and "M[N <- z] \<rightarrow>* V" and "P \<lesssim> N" and "\<not> diverge M[P <- z]" and "z \<notin> FVars V"
  shows "\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
  using assms
proof (induction V arbitrary: M rule:val.induct)
  case (1 x)
  then obtain U where U1: "Var x = U[N <- z]" and U2: "M[P <- z] \<rightarrow>* U[P <- z]"
    using b4[of M N z _ "Var x" P] beta_star_def val.intros(1) vals_are_normal
    by blast
  then show ?case
  proof (cases "U = Var z")
    case True
    then show ?thesis 
      using b5_helper[of M N z "Var x" P U] 1 val.intros(1) U1 U2 by blast
  next
    case False
    then have "U = Var x" 
      using subst_Var_inversion[of U N z x] U1 by simp
    then have "x \<noteq> z" using \<open>U \<noteq> Var z\<close> by simp
    then have "U[P <- z] = Var x" using \<open>U = Var x\<close> subst_idle by auto
    then have "val (Var x) \<and> M[P <- z] \<rightarrow>* (Var x) \<and> b5_prop (Var x) (Var x) P N z" 
      using \<open>M[P <- z] \<rightarrow>* U[P <- z]\<close> val.intros(1)[of x] b5_prop_reflexive[of "Var x" z] \<open>z \<notin> FVars (Var x)\<close>
      by simp
    then show ?thesis by auto
  qed
next
  case (2 n)
  then show ?case
  proof (induction n arbitrary: M rule:num.induct)
    case 1
    then obtain U where U1: "Zero = U[N <- z]" and U2: "M[P <- z] \<rightarrow>* U[P <- z]"
      using b4[of M N z _ Zero P] beta_star_def num.intros(1) nums_are_normal
      by blast
    then show ?case
    proof(cases "U = Var z")
      case True
      then show ?thesis 
        using b5_helper[of M N z Zero P U] 1 num.intros(1) val.intros(2) U1 U2 by blast 
    next
      case False
      then have "U = Zero" using subst_Zero_inversion U1 by metis
      then have "U[P <- z] = Zero" using subst_idle by simp
      then have "val Zero \<and> M[P <- z] \<rightarrow>* Zero \<and> b5_prop Zero Zero P N z"
        using \<open>M[P <- z] \<rightarrow>* U[P <- z]\<close> b5_prop_reflexive[of Zero z] val.intros(2) num.intros(1) \<open>z \<notin> FVars Zero\<close>
        by metis
      then show ?thesis by auto
    qed
  next
    case (2 n)
    then obtain U where U1: "Succ n = U[N <- z]" and U2: "M[P <- z] \<rightarrow>* U[P <- z]"
      using b4[of M N z _ "Succ n" P] beta_star_def num.intros(2) nums_are_normal
      by metis
    then show ?case
    proof (cases "U = Var z")
      case True
      then show ?thesis 
        using b5_helper[of M N z "Succ n" P U] 2 num.intros(2) val.intros(2) U1 U2 by blast 
    next
      case False
      obtain W' where "U = Succ W'" and "W'[N <- z] = n"
        using 2(5) \<open>U \<noteq> Var z\<close> subst_Succ_inversion[of U N z n] U1 by auto
      then have "W'[N <- z] \<rightarrow>* n" using beta_star_def betas.refl by auto
      have "M[P <- z] \<rightarrow>* Succ (W'[P <- z])"
        using U2 \<open>U = Succ W'\<close> by auto
      then have "\<not> diverge W'[P <- z]"
        using "2.prems"(4) beta_star_diverge_back div_ctx eval_ctx.intros(1,4)
            usubst_simps(2,5)
        by metis
      then obtain W where "val W" and "W'[P <- z] \<rightarrow>* W" and "b5_prop n W P N z"
        using 2(2)[of W'] 2(3, 5, 6) \<open>W'[N <- z] \<rightarrow>* n\<close>
        using "2.prems"(5) term.set(2) by blast
      have "W = n" using \<open>b5_prop n W P N z\<close> \<open>num n\<close> num_not_haveFix b5_prop_def by blast
      then have "W'[P <- z] \<rightarrow>* n"                             
        using \<open>W'[P <- z] \<rightarrow>* W\<close> by blast
      then have "M[P <- z] \<rightarrow>* (Succ n)"
        using \<open>M[P <- z] \<rightarrow>* U[P <- z]\<close> \<open>U = Succ W'\<close>
        using beta_star_def betas_path_sum Succ_beta_star
        by (metis usubst_simps(2))
      then have "val (Succ n) \<and> M[P <- z] \<rightarrow>* (Succ n) \<and> b5_prop (Succ n) (Succ n) P N z"
        using val.intros(2) num.intros(2) b5_prop_reflexive \<open>num n\<close> \<open>z \<notin> FVars (Succ n)\<close> by blast
      then show ?thesis by auto
    qed
  qed
next
  case (3 V1 V2)
  have vV: "val (term.Pair V1 V2)" using 3(1) 3(2) by (rule val.intros(3))
  from b4_val[OF "3.prems"(2) vV "3.prems"(3) "3.prems"(1)] "3.prems"(4)
  obtain U where gU: "guarded z U" and U1: "term.Pair V1 V2 = U[N <- z]" and U2: "M[P <- z] \<rightarrow>* U[P <- z]"
    by auto
  then show ?case
  proof (cases "U = Var z")
    case True
    then show ?thesis
      using b5_helper[of M N z "Pair V1 V2" P U] 3 val.intros(3) U1 U2 by blast
  next
    case False
    then obtain M1 M2 where m1m2: "U = term.Pair M1 M2" and m1: "M1[N <- z] = V1" and m2: "M2[N <- z] = V2"
      using subst_Pair_inversion[of U N z V1 V2] U1 by metis
    have gM1: "guarded z M1" and gM2: "guarded z M2" using gU m1m2 by simp_all
    have vM1P: "val (M1[P <- z])" using val_subst_guarded[OF gM1] m1 3(1) by metis
    have vM2P: "val (M2[P <- z])" using val_subst_guarded[OF gM2] m2 3(2) by metis
    have "\<not> diverge (U[P <- z])" using "3.prems"(4) U2 beta_star_diverge_back by blast
    then have nd1: "\<not> (M1[P <- z] \<Up>)" and nd2: "\<not> (M2[P <- z] \<Up>)"
      using m1m2 Pair_div Pair_div2[OF vM1P] by auto
    show ?thesis
    proof(cases "haveFix (term.Pair V1 V2)")
      case True
      have b5VU: "b5_prop (term.Pair V1 V2) (U[P <- z]) P N z" unfolding b5_prop_def
        using m1m2 m1 m2 True by auto
      have "val (U[P <- z])" using m1m2 vM1P vM2P by (simp add: val.intros(3))
      then show ?thesis using b5VU U2 by auto
    next
      case False
      obtain W1 where "val W1" and "M1[P <- z] \<rightarrow>* W1" and "b5_prop V1 W1 P N z"
        using 3(3)[of M1] m1 beta_star_def betas.refl
        using "3.prems"(3) "3.prems"(1) nd1 "3.prems"(5)
        by (metis Un_iff term.set(8))
      moreover obtain W2 where "val W2" and "M2[P <- z] \<rightarrow>* W2" and "b5_prop V2 W2 P N z"
        using 3(4)[of M2] m2 beta_star_def betas.refl
        using "3.prems"(3) "3.prems"(1) nd2 "3.prems"(5)
        by (metis Un_iff term.set(8))
      ultimately have *: "val (term.Pair W1 W2)" and **: "M[P <- z] \<rightarrow>* (term.Pair W1 W2)"
        using val.intros(3) U2 m1m2 beta_star_sums[of "M[P <- z]" "U[P <- z]" "Pair W1 W2"] Pair_beta_star
         apply auto
        by blast
      have "\<not> haveFix V1" and "\<not> haveFix V2"
        using False haveFix_Pair by auto
      then have "V1 = W1 \<and> V2 = W2"
        using \<open>b5_prop V1 W1 P N z\<close> \<open>b5_prop V2 W2 P N z\<close> unfolding b5_prop_def by blast
      then have "val (Pair V1 V2) \<and> M[P <- z] \<rightarrow>* (Pair V1 V2) \<and> b5_prop (Pair V1 V2) (Pair V1 V2) P N z"
        using * ** b5_prop_reflexive 3(1) 3(2) "3.prems"(5) by blast
      then show ?thesis by auto
    qed
  qed
next
  case (4 f x R)
  then obtain U where U1: "Fix f x R = U[N <- z]" and U2: "M[P <- z] \<rightarrow>* U[P <- z]"
    using b4[of M N z _ "Fix f x R" P] beta_star_def val.intros(4) vals_are_normal
    by metis
  then show ?case
  proof (cases "U = Var z")
    case True
    then show ?thesis 
      using b5_helper[of M N z "Fix f x R" P U] 4 val.intros(4) U1 U2 by blast
  next
    case False
    obtain f' x' R' where V_eq: "Fix f x R = Fix f' x' R'"
      and fz: "f' \<noteq> z" and fN: "f' \<notin> FVars N" and fP: "f' \<notin> FVars P"
      and xz: "x' \<noteq> z" and xN: "x' \<notin> FVars N" and xP: "x' \<notin> FVars P"
      using Fix_refresh[of "{z} \<union> FVars N \<union> FVars P" f x R] finite_FVars by auto
    from U1 V_eq have U1': "Fix f' x' R' = U[N <- z]" by simp
    then obtain Q where q1: "U = Fix f' x' Q" and q2: "Q[N <- z] = R'"
      using subst_Fix_inversion[of U N z f' x' R'] \<open>U \<noteq> Var z\<close> fz fN xz xN
      by auto
    have bp: "b5_prop (Fix f' x' R') U[P <- z] P N z" unfolding b5_prop_def
      apply (intro conjI allI impI)
      subgoal using haveFix.intros(1) by blast
      subgoal by simp
      subgoal premises prems for fa xa Ra
      proof -
        have eq: "Fix f' x' R' = Fix fa xa Ra" and faf: "fa \<notin> FVars N \<union> FVars P \<union> {z}"
          and xaf: "xa \<notin> FVars N \<union> FVars P \<union> {z}" using prems by blast+
        from U1' eq have "U[N <- z] = Fix fa xa Ra" by simp
        then obtain Q'' where u2: "U = Fix fa xa Q''" and q2'': "Q''[N <- z] = Ra"
          using subst_Fix_inversion[of U N z fa xa Ra] \<open>U \<noteq> Var z\<close> faf xaf by auto
        have "U[P <- z] = Fix fa xa (Q''[P <- z])"
          using u2 usubst_simps(7) faf xaf by auto
        then show "\<exists>Q. U[P <- z] = Fix fa xa Q[P <- z] \<and> Q[N <- z] = Ra"
          using q2'' by blast
      qed
      done
    have vU: "val U[P <- z]"
    proof -
      have "U[P <- z] = Fix f' x' (Q[P <- z])"
        unfolding q1 by (simp add: fz fP xz xP)
      moreover have "val (Fix f' x' (Q[P <- z]))" by (rule val.intros(4))
      ultimately show ?thesis by simp
    qed
    then have "val U[P <- z] \<and> M[P <- z] \<rightarrow>* U[P <- z] \<and> b5_prop (Fix f x R) U[P <- z] P N z"
      using bp U2 unfolding V_eq by blast
    then show ?thesis by blast
  qed
qed

lemma b5:
  assumes "val V" and "z \<notin> FVars N" and "M[N <- z] \<rightarrow>* V" and "P \<lesssim> N"
  shows "diverge M[P <- z] \<or> (\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z)"
  using assms
proof -
  have "z \<notin> FVars M[N <- z]" using \<open>z \<notin> FVars N\<close>
    by (simp add: FVars_usubst)
  then have "z \<notin> FVars V" 
    using \<open>M[N <- z] \<rightarrow>* V\<close> FVars_beta_star by auto
  then show ?thesis
  apply(cases "diverge M[P <- z]")
   apply(auto)
    using b5_induction assms by blast
qed

section \<open>B6\<close>

thm val.cases

text \<open>NB: the naive inverse of @{text eval_ctx_beta},
    @{prop "eval_ctx hole E \<Longrightarrow> E[M <- hole] \<rightarrow> E[N <- hole] \<Longrightarrow> M \<rightarrow> N"},
  is FALSE (and unused). Counterexample: take the self-looping @{text FixBeta} redex.
  With @{text "E = App (Fix f x (App (Var f) (Var x))) (Var hole)"} (a valid evaluation context,
  @{text "hole \<notin> {f,x}"}) we have @{text "E[Zero <- hole] = App (Fix f x (App (Var f) (Var x))) Zero"},
  which @{text FixBeta}-reduces to @{text "(App (Var f) (Var x))[Zero <- x][Fix f x \<dots> <- f] =
  App (Fix f x (App (Var f) (Var x))) Zero"}, i.e.\ to itself. Hence
  @{text "E[Zero <- hole] \<rightarrow> E[Zero <- hole]"} holds while @{text "Zero \<rightarrow> Zero"} does not.
  The step consumes the whole context as a redex rather than descending into the hole, so no
  inversion to a hole-local step exists. (Determinism only yields the converse implication when the
  hole content is itself reducible.)\<close>

lemma stuckEx_are_normal: "stuckEx M \<Longrightarrow> normal M"
proof(rule ccontr)
  assume stuck: "stuckEx M" and "\<not> normal M"
  then obtain M' where steps: "M \<rightarrow> M'" unfolding normal_def by auto
  show False using stuck
  proof(cases M rule:stuckEx.cases)
    case (1 V)
    then show ?thesis using vals_are_normal[of V] steps beta.cases[of M M'] unfolding normal_def
      by auto
  next
    case (2 V N P)
    show ?thesis 
      using 2 vals_are_normal[of V] steps beta.cases[of M M'] unfolding normal_def
      by (smt (verit, best) MrBNF_ver.num.simps term.distinct(26,27,29,31,68) term.inject(3))
  next
    case (3 V M0)
    show ?thesis using steps unfolding 3(1)
    proof (cases rule: beta.cases)
      case (OrdApp2 N N' f x Ma)
      then show ?thesis using 3(3) unfolding is_Fix_def by (meson term.inject(5))
    next
      case (OrdApp1 Ma Ma' N)
      then show ?thesis using 3(2) normal_def vals_are_normal by auto
    next
      case (FixBeta V2 f x Ma)
      then show ?thesis using 3(3) unfolding is_Fix_def by (meson term.inject(5))
    qed auto
  next
    case (4 V xy M0)
    show ?thesis using steps unfolding 4(1)
    proof (cases rule: beta.cases)
      case (OrdLet Ma Ma' xy2 Na)
      then show ?thesis using 4(2) vals_are_normal unfolding normal_def by auto
    next
      case (Let V2 W2 xy2 M2)
      then show ?thesis using 4(3) unfolding is_Pair_def by auto
    qed auto
  next
    case (5 V)
    then show ?thesis
      using vals_are_normal[of V] steps beta.cases[of M M'] num.intros unfolding normal_def
      by (smt (verit, best) term.distinct(10,19,21,23,67) term.inject(2))

  qed
qed

lemma stuckEx_not_val: "stuckEx M \<Longrightarrow> \<not> val M"
  apply (cases rule: stuckEx.cases)
      apply (auto 0 3 elim: val.cases num.cases)
  done

lemma val_ctx_plug: "eval_ctx hole E \<Longrightarrow> val (E[N <- hole]) \<Longrightarrow> val N"
  apply (binder_induction hole E avoiding: N E rule: eval_ctx.strong_induct)
  subgoal by simp
  subgoal by (auto 0 3 elim: val.cases num.cases)
  subgoal by (auto 0 3 elim: val.cases num.cases)
  subgoal by (force elim: val.cases num.cases intro: val.intros)
  subgoal by (auto 0 3 elim: val.cases num.cases)
  subgoal by (auto 0 3 elim: val.cases num.cases)
  subgoal by (auto 0 3 elim: val.cases num.cases)
  subgoal for holea Ea Na xy
    apply (subst (asm) usubst_simps(9))
    apply (auto 0 3 elim: val.cases num.cases simp: disjoint_iff)
    done
  subgoal by (auto 0 3 elim: val.cases num.cases)
  done

lemma ctx_plug_stuckEx_normal: "eval_ctx hole E \<Longrightarrow> stuckEx N \<Longrightarrow> normal (E[N <- hole])"
proof (binder_induction hole E avoiding: N E rule: eval_ctx.strong_induct)
  case (1 holea)
  then show ?case by (simp add: stuckEx_are_normal)
next
  case (2 holea Ea Ma f xa)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(App (Fix f xa Ma) Ea)[N <- holea] \<rightarrow> M'"
    then have st: "App (Fix f xa Ma) (Ea[N <- holea]) \<rightarrow> M'" using 2(4,5) by auto
    from st show False
    proof (cases rule: beta.cases)
      case (OrdApp2 N0 N0' f2 x2 M2)
      then show ?thesis using 2(6)[OF 2(5)] unfolding normal_def by auto
    next
      case (OrdApp1 M0 M0' N0)
      then show ?thesis using vals_are_normal[OF val.intros(4)] unfolding normal_def by (metis term.inject(5))
    next
      case (FixBeta V2 f2 x2 M2)
      then have "val (Ea[N <- holea])" by auto
      then show ?thesis using val_ctx_plug[OF 2(3)] stuckEx_not_val[OF 2(5)] by blast
    qed auto
  qed
next
  case (3 holea Ea Na)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(App Ea Na)[N <- holea] \<rightarrow> M'"
    then have st: "App (Ea[N <- holea]) (Na[N <- holea]) \<rightarrow> M'" by auto
    from st show False
    proof (cases rule: beta.cases)
      case (OrdApp2 N0 N0' f2 x2 M2)
      then have "val (Ea[N <- holea])" using val.intros(4) by auto
      then show ?thesis using val_ctx_plug[OF 3(1)] stuckEx_not_val[OF 3(3)] by blast
    next
      case (OrdApp1 M0 M0' N0)
      then show ?thesis using 3(4)[OF 3(3)] unfolding normal_def by auto
    next
      case (FixBeta V2 f2 x2 M2)
      then have "val (Ea[N <- holea])" using val.intros(4) by auto
      then show ?thesis using val_ctx_plug[OF 3(1)] stuckEx_not_val[OF 3(3)] by blast
    qed auto
  qed
next
  case (4 holea Ea)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(Succ Ea)[N <- holea] \<rightarrow> M'"
    then have st: "Succ (Ea[N <- holea]) \<rightarrow> M'" by auto
    from st show False
      by (cases rule: beta.cases) (use 4(3)[OF 4(2)] normal_def in auto)
  qed
next
  case (5 holea Ea)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(Pred Ea)[N <- holea] \<rightarrow> M'"
    then have st: "Pred (Ea[N <- holea]) \<rightarrow> M'" by auto
    from st show False
    proof (cases rule: beta.cases)
      case (OrdPred M0 M0')
      then show ?thesis using 5(3)[OF 5(2)] unfolding normal_def by auto
    next
      case PredZ
      then have "val (Ea[N <- holea])" using val.intros(2) num.intros(1) by auto
      then show ?thesis using val_ctx_plug[OF 5(1)] stuckEx_not_val[OF 5(2)] by blast
    next
      case (PredS)
      then have "val (Ea[N <- holea])" using val.intros(2) num.intros(2) by auto
      then show ?thesis using val_ctx_plug[OF 5(1)] stuckEx_not_val[OF 5(2)] by blast
    qed auto
  qed
next
  case (6 holea Ea Na)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(term.Pair Ea Na)[N <- holea] \<rightarrow> M'"
    then have st: "term.Pair (Ea[N <- holea]) (Na[N <- holea]) \<rightarrow> M'" by auto
    from st show False
    proof (cases rule: beta.cases)
      case (OrdPair1 M0 M0' N0)
      then show ?thesis using 6(4)[OF 6(3)] unfolding normal_def by auto
    next
      case (OrdPair2 V0 N0 N0')
      then have "val (Ea[N <- holea])" by auto
      then show ?thesis using val_ctx_plug[OF 6(1)] stuckEx_not_val[OF 6(3)] by blast
    qed auto
  qed
next
  case (7 V holea Ea)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(term.Pair V Ea)[N <- holea] \<rightarrow> M'"
    then have st: "term.Pair V (Ea[N <- holea]) \<rightarrow> M'" using 7(3) by auto
    from st show False
    proof (cases rule: beta.cases)
      case (OrdPair1 M0 M0' N0)
      then show ?thesis using 7(1) vals_are_normal unfolding normal_def by (metis term.inject(7))
    next
      case (OrdPair2 V0 N0 N0')
      then show ?thesis using 7(5)[OF 7(4)] unfolding normal_def by auto
    qed auto
  qed
next
  case (8 holea Ea Na xy)
  show ?case unfolding normal_def
  proof safe
    fix M' assume pre: "(term.Let xy Ea Na)[N <- holea] \<rightarrow> M'"
    have push: "(term.Let xy Ea Na)[N <- holea] = term.Let xy (Ea[N <- holea]) (Na[N <- holea])"
      using 8(1,2,5) by (subst usubst_simps(9)) (auto simp: disjoint_iff)
    from pre have st: "term.Let xy (Ea[N <- holea]) (Na[N <- holea]) \<rightarrow> M'" unfolding push .
    from st show False
    proof (cases rule: beta.cases)
      case (OrdLet M0 M0' xy2 N0)
      then have "Ea[N <- holea] \<rightarrow> M0'" by auto
      then show ?thesis using 8(7)[OF 8(6)] unfolding normal_def by auto
    next
      case (Let V2 W2 xy2 M2)
      then have "val (Ea[N <- holea])" using val.intros(3) by auto
      then show ?thesis using val_ctx_plug[OF 8(3)] stuckEx_not_val[OF 8(6)] by blast
    qed auto
  qed
next
  case (9 holea Ea Na P)
  show ?case unfolding normal_def
  proof safe
    fix M' assume "(term.If Ea Na P)[N <- holea] \<rightarrow> M'"
    then have st: "term.If (Ea[N <- holea]) (Na[N <- holea]) (P[N <- holea]) \<rightarrow> M'" by auto
    from st show False
    proof (cases rule: beta.cases)
      case (OrdIf M0 M0' N0 P0)
      then show ?thesis using 9(5)[OF 9(4)] unfolding normal_def by auto
    next
      case (Ifz N0)
      then have "val (Ea[N <- holea])" using val.intros(2) num.intros(1) by auto
      then show ?thesis using val_ctx_plug[OF 9(1)] stuckEx_not_val[OF 9(4)] by blast
    next
      case (Ifs n N0)
      then have "val (Ea[N <- holea])" using val.intros(2) num.intros(2) by auto
      then show ?thesis using val_ctx_plug[OF 9(1)] stuckEx_not_val[OF 9(4)] by blast
    qed auto
  qed
qed

lemma stucks_are_normal: "stuck M \<Longrightarrow> normal M"
  unfolding stuck_def using ctx_plug_stuckEx_normal by auto

lemma dset_finite: "finite (dset xy)"
  by (simp add: dset_alt)

lemma If_beta_star: "n \<rightarrow>* m \<Longrightarrow> If n M1 M2 \<rightarrow>* If m M1 M2"
proof -
  assume "n \<rightarrow>* m"
  obtain x :: 'a where "eval_ctx x (If (Var x) M1 M2)" and "x \<notin> FVars M1" and "x \<notin> FVars M2"
    using eval_ctx.intros(1, 9)
    by (metis UnCI arb_element finite_FVars term.set(8))
  then show ?thesis 
    using eval_ctx_beta_star[of x "If (Var x) M1 M2" n m] \<open>n \<rightarrow>* m\<close>
    by auto
qed

lemma App_beta_star: "V \<rightarrow>* V' \<Longrightarrow> App V M \<rightarrow>* App V' M"
proof -
  assume "V \<rightarrow>* V'"
  obtain x :: 'a where "eval_ctx x (App (Var x) M)" and "x \<notin> FVars M"
    using eval_ctx.intros(1,3)
    by (metis arb_element finite_FVars)
  then show ?thesis 
    using eval_ctx_beta_star[of x "App (Var x) M" V V'] \<open>V \<rightarrow>* V'\<close>
    by auto
qed

lemma Let_subst_scrutinee:
  fixes A :: "'a::var term"
  assumes zd: "z \<notin> dset xy" and zB: "z \<notin> FVars B"
  shows "(term.Let xy A B)[N <- z] = term.Let xy (A[N <- z]) B"
proof -
  have b1: "|dset xy| <o |UNIV::'a set|" by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
  have b2: "|FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z]) \<union> dset xy| <o |UNIV::'a set|"
    by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
  obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
      "g ` dset xy \<inter> (FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z]) \<union> dset xy) = {}"
      "id_on ((FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z])) - dset xy) g" "g \<circ> g = id"
    using eextend_fresh[OF b1 b2 infinite_UNIV,
        of "(FVars A \<union> FVars B \<union> FVars N \<union> {z} \<union> FVars (A[N <- z])) - dset xy"] by auto
  have gz: "g z = z" using g(4) zd zB unfolding id_on_def by auto
  have alpha_out: "term.Let xy A B = term.Let (dmap g xy) A (permute_term g B)"
    using g by (auto intro!: exI[of _ g] simp: id_on_def)
  have zd': "z \<notin> dset (dmap g xy)" using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  have dN': "dset (dmap g xy) \<inter> FVars N = {}" using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  have dA': "dset (dmap g xy) \<inter> FVars A = {}" using g(3) unfolding dpair.set_map[OF g(1) g(2)] by blast
  have push: "(term.Let (dmap g xy) A (permute_term g B))[N <- z]
      = term.Let (dmap g xy) (A[N <- z]) ((permute_term g B)[N <- z])"
    by (rule usubst_simps(9)[OF zd' dN' dA'])
  have zpB: "z \<notin> FVars (permute_term g B)"
  proof
    assume "z \<in> FVars (permute_term g B)"
    then obtain w where w: "w \<in> FVars B" and gw: "g w = z" unfolding term.FVars_permute[OF g(1) g(2)] by auto
    from gw gz have "w = z" using g(1) by (metis bij_is_inj injD)
    then show False using w zB by simp
  qed
  have body: "(permute_term g B)[N <- z] = permute_term g B" using subst_idle[OF zpB] .
  have alpha_back: "term.Let xy (A[N <- z]) B = term.Let (dmap g xy) (A[N <- z]) (permute_term g B)"
    using g by (auto intro!: exI[of _ g] simp: id_on_def)
  show ?thesis unfolding alpha_out push body alpha_back ..
qed

lemma Let_beta_star: "V \<rightarrow>* V' \<Longrightarrow> Let xy V M \<rightarrow>* Let xy V' M"
proof -
  assume "V \<rightarrow>* V'"
  obtain x :: 'a where x: "x \<notin> FVars M \<union> dset xy"
    by (meson arb_element finite_FVars finite_Un finite_dset)
  then have ctx: "eval_ctx x (Let xy (Var x) M)"
    using eval_ctx.intros(1)[of x] eval_ctx.intros(8)[of x "Var x" M xy] by auto
  have e1: "(Let xy (Var x) M)[V <- x] = Let xy V M"
    using Let_subst_scrutinee[where z=x and xy=xy and B=M and A="Var x" and N=V] x by auto
  have e2: "(Let xy (Var x) M)[V' <- x] = Let xy V' M"
    using Let_subst_scrutinee[where z=x and xy=xy and B=M and A="Var x" and N=V'] x by auto
  show ?thesis
    using eval_ctx_beta_star[OF ctx \<open>V \<rightarrow>* V'\<close>] unfolding e1 e2 .
qed

lemma b5_prop_not_fix: 
  assumes "val V" and nFix: "\<forall>f x Q. V \<noteq> Fix f x Q" and b5: "b5_prop V W P N z"
  shows "\<forall>f x Q. W \<noteq> Fix f x Q"
  using assms(1)
proof (cases V rule:val.cases)
  case (1 x)
  then show ?thesis using b5 nFix haveFix.simps unfolding b5_prop_def by force
next
  case 2
  then show ?thesis using num_not_haveFix b5 nFix unfolding b5_prop_def
    by auto
next
  case (3 V W)
  then show ?thesis using b5 unfolding b5_prop_def by force
next
  case (4 f x Q)
  then show ?thesis by (simp add: nFix)
qed

lemma b5_prop_not_num:
assumes "val V" and nNum: "\<not> num V" and b5: "b5_prop V W P N z"
  shows "\<not> num W"
  using assms
proof (binder_induction V avoiding: "Var z" N P rule:val.strong_induct)
  case (1 x)
  then have "W = Var x" using haveFix.simps unfolding b5_prop_def by force
  then show ?thesis using 1(1) by auto
next
  case (2 n)
  then show ?thesis by auto
next
  case (3 V W)
  then show ?thesis using b5 unfolding b5_prop_def
    by (metis num.simps term.distinct(58,7))
next
  case (4 f x Q)
  have av: "f \<notin> FVars N \<union> FVars P \<union> {z}" "x \<notin> FVars N \<union> FVars P \<union> {z}"
    using 4 by auto
  obtain Q' where "W = Fix f x Q'[P <- z]"
    using 4 av unfolding b5_prop_def by metis
  then show ?thesis by (auto elim: num.cases)
qed

lemma b5_prop_not_pair:
assumes "val V" and nNum: "\<nexists>V1 V2. V = Pair V1 V2" and b5: "b5_prop V W P N z"
  shows "\<nexists>W1 W2. W = Pair W1 W2"
  using assms
proof (binder_induction V avoiding: "Var z" N P rule:val.strong_induct)
  case (1 x)
  then have "W = Var x" using haveFix.simps unfolding b5_prop_def by force
  then show ?thesis using 1(1) by auto
next
  case (2 n)
  then show ?thesis
    by (simp add: b5_prop_def num_not_haveFix)
next
  case (3 V W)
  then show ?thesis by auto
next
  case (4 f x Q)
  have av: "f \<notin> FVars N \<union> FVars P \<union> {z}" "x \<notin> FVars N \<union> FVars P \<union> {z}"
    using 4 by auto
  obtain Q' where "W = Fix f x Q'[P <- z]"
    using 4 av unfolding b5_prop_def by metis
  then show ?thesis by auto
qed

lemma stuck_not_val: "stuck M \<Longrightarrow> \<not> val M"
  unfolding stuck_def using val_ctx_plug stuckEx_not_val by metis

text \<open>Support lemmas for @{text b6}: evaluation-context composition, lifting @{text getStuck}/
  @{text diverge} through a context, structural inversions of @{text stuck} at each constructor,
  and the key induction @{text b6'} (a stuck term stays stuck-or-divergent under a less-defined
  substitution), from which @{text b6} follows via @{text b4}.\<close>

lemma eval_ctx_compose:
  "eval_ctx hole E \<Longrightarrow> eval_ctx h D \<Longrightarrow> h \<noteq> hole \<Longrightarrow> h \<notin> FVars E \<Longrightarrow> eval_ctx h (E[D <- hole])"
proof (binder_induction hole E avoiding: "App D (Var h)" E rule: eval_ctx.strong_induct)
  case (1 holea)
  then show ?case by simp
next
  case (2 holea Ea M f xa)
  have hEa: "h \<notin> FVars Ea" and hM: "h \<notin> FVars M" using 2(7) 2(1) by auto
  have push: "(App (Fix f xa M) Ea)[D <- holea] = App (Fix f xa M) (Ea[D <- holea])"
    using 2(4) by simp
  show ?case unfolding push by (rule eval_ctx.intros(2)[OF 2(8)[OF 2(5) 2(6) hEa] hM])
next
  case (3 holea Ea N)
  have hEa: "h \<notin> FVars Ea" and hN: "h \<notin> FVars N" using 3(5) by auto
  have push: "(App Ea N)[D <- holea] = App (Ea[D <- holea]) N" using 3(2) by simp
  show ?case unfolding push by (rule eval_ctx.intros(3)[OF 3(6)[OF 3(3) 3(4) hEa] hN])
next
  case (4 holea Ea)
  have hEa: "h \<notin> FVars Ea" using 4(4) by simp
  show ?case using eval_ctx.intros(4)[OF 4(5)[OF 4(2) 4(3) hEa]] by simp
next
  case (5 holea Ea)
  have hEa: "h \<notin> FVars Ea" using 5(4) by simp
  show ?case using eval_ctx.intros(5)[OF 5(5)[OF 5(2) 5(3) hEa]] by simp
next
  case (6 holea Ea N)
  have hEa: "h \<notin> FVars Ea" and hN: "h \<notin> FVars N" using 6(5) by auto
  have push: "(term.Pair Ea N)[D <- holea] = term.Pair (Ea[D <- holea]) N" using 6(2) by simp
  show ?case unfolding push by (rule eval_ctx.intros(6)[OF 6(6)[OF 6(3) 6(4) hEa] hN])
next
  case (7 V holea Ea)
  have hEa: "h \<notin> FVars Ea" and hV: "h \<notin> FVars V" using 7(6) by auto
  have push: "(term.Pair V Ea)[D <- holea] = term.Pair V (Ea[D <- holea])" using 7(3) by simp
  show ?case unfolding push by (rule eval_ctx.intros(7)[OF 7(1) 7(7)[OF 7(4) 7(5) hEa] hV])
next
  case (8 holea Ea N xy)
  have hxy: "h \<notin> dset xy" and dD: "dset xy \<inter> FVars D = {}" using 8(1) by auto
  have hEa: "h \<notin> FVars Ea" using 8(8) by simp
  have hN: "h \<notin> FVars N" using 8(8) hxy by auto
  have push: "(term.Let xy Ea N)[D <- holea] = term.Let xy (Ea[D <- holea]) N"
    using 8(4) by (subst usubst_Let[OF 8(5) dD]) simp
  show ?case unfolding push by (rule eval_ctx.intros(8)[OF 8(9)[OF 8(6) 8(7) hEa] hN hxy])
next
  case (9 holea Ea N P)
  have hEa: "h \<notin> FVars Ea" and hN: "h \<notin> FVars N" and hP: "h \<notin> FVars P" using 9(6) by auto
  have push: "(term.If Ea N P)[D <- holea] = term.If (Ea[D <- holea]) N P" using 9(2) 9(3) by simp
  show ?case unfolding push by (rule eval_ctx.intros(9)[OF 9(7)[OF 9(4) 9(5) hEa] hN hP])
qed

lemma stuck_ctx:
  assumes ctx: "eval_ctx hole E" and st: "stuck S" and hS: "hole \<notin> FVars S"
  shows "stuck (E[S <- hole])"
proof -
  obtain D h s where hD: "eval_ctx h D" and Seq: "S = D[s <- h]" and ss: "stuckEx s"
      and h': "h \<notin> FVars E \<union> {hole}"
    using stuck_fresh_hole[OF st, of "FVars E \<union> {hole}"] finite_FVars by auto
  have hh: "h \<noteq> hole" and hFE: "h \<notin> FVars E" using h' by auto
  have hs: "hole \<notin> FVars s"
  proof -
    have "FVars s \<subseteq> FVars S" using Seq eval_ctxt_FVars[OF hD] by (auto simp: FVars_usubst)
    then show ?thesis using hS by auto
  qed
  have eq: "E[S <- hole] = (E[D <- hole])[s <- h]"
  proof -
    have "(E[D <- hole])[s <- h] = E[s <- h][D[s <- h] <- hole]"
      by (rule usubst_usubst[OF hh[symmetric] hs])
    also have "\<dots> = E[D[s <- h] <- hole]" using hFE by simp
    also have "\<dots> = E[S <- hole]" unfolding Seq ..
    finally show ?thesis by (rule sym)
  qed
  have "eval_ctx h (E[D <- hole])" using eval_ctx_compose[OF ctx hD hh hFE] .
  then show ?thesis unfolding eq stuck_def using ss by metis
qed

lemma getStuck_ctx:
  assumes ctx: "eval_ctx hole E" and gs: "getStuck A" and hA: "hole \<notin> FVars A"
  shows "getStuck (E[A <- hole])"
proof -
  obtain S where AS: "A \<rightarrow>* S" and stS: "stuck S" using gs getStuck_def by auto
  have hS: "hole \<notin> FVars S" using AS FVars_beta_star hA by auto
  have "E[A <- hole] \<rightarrow>* E[S <- hole]" using eval_ctx_beta_star[OF ctx AS] .
  moreover have "stuck (E[S <- hole])" using stuck_ctx[OF ctx stS hS] .
  ultimately show ?thesis unfolding getStuck_def by auto
qed

lemma progress: "normal M \<Longrightarrow> val M \<or> stuck M"
  using val_stuck_step normal_def by auto

lemma not_stuck_Zero: "\<not> stuck Zero"
  using stuck_not_val val.intros(2) num.intros(1) by blast

lemma not_stuck_Var: "\<not> stuck (Var x)"
  using stuck_not_val val.intros(1) by blast

lemma not_stuck_Fix: "\<not> stuck (Fix f x M)"
  using stuck_not_val val.intros(4) by blast

lemma stuck_Succ: "stuck (Succ M) \<Longrightarrow> (val M \<and> \<not> num M) \<or> stuck M"
proof -
  assume s: "stuck (Succ M)"
  have nM: "normal M" using s stucks_are_normal[of "Succ M"] unfolding normal_def
    by (metis beta.OrdSucc)
  have "\<not> num M" using s stuck_not_val num.intros(2) val.intros(2) by blast
  then show ?thesis using nM progress by blast
qed

lemma stuck_Pred: "stuck (Pred M) \<Longrightarrow> (val M \<and> \<not> num M) \<or> stuck M"
proof -
  assume s: "stuck (Pred M)"
  have nM: "normal M" using s stucks_are_normal[of "Pred M"] unfolding normal_def
    by (metis beta.OrdPred)
  have "\<not> num M" using s stucks_are_normal[of "Pred M"] unfolding normal_def
    by (metis beta.PredZ beta.PredS num.cases)
  then show ?thesis using nM progress by blast
qed

lemma stuck_If: "stuck (If M N P) \<Longrightarrow> (val M \<and> \<not> num M) \<or> stuck M"
proof -
  assume s: "stuck (If M N P)"
  have nM: "normal M" using s stucks_are_normal[of "If M N P"] unfolding normal_def
    by (metis beta.OrdIf)
  have "\<not> num M" using s stucks_are_normal[of "If M N P"] unfolding normal_def
    by (metis beta.Ifz beta.Ifs num.cases)
  then show ?thesis using nM progress by blast
qed

lemma normal_AppFix_arg: "normal (App (Fix f x M0) B) \<Longrightarrow> \<not> val B"
proof (rule notI)
  assume n: "normal (App (Fix f x M0) B)" and v: "val B"
  obtain f' x' M0' where eq: "Fix f x M0 = Fix f' x' M0'" and f': "f' \<notin> FVars B"
    using Fix_refresh[of "FVars B" f x M0] finite_FVars by auto
  have "App (Fix f x M0) B \<rightarrow> M0'[B <- x'][Fix f' x' M0' <- f']"
    unfolding eq using beta.FixBeta[OF v f'] .
  then show False using n normal_def by auto
qed

lemma stuck_App:
  "stuck (App M1 M2) \<Longrightarrow> (val M1 \<and> \<not> is_Fix M1) \<or> stuck M1 \<or> (is_Fix M1 \<and> stuck M2)"
proof -
  assume s: "stuck (App M1 M2)"
  have n: "normal (App M1 M2)" using s stucks_are_normal by blast
  have n1: "normal M1" using n unfolding normal_def by (metis beta.OrdApp1)
  show ?thesis
  proof (cases "val M1")
    case False
    then have "stuck M1" using n1 progress by blast
    then show ?thesis by blast
  next
    case True
    show ?thesis
    proof (cases "is_Fix M1")
      case False
      then show ?thesis using True by blast
    next
      case True
      then obtain f x M0 where m1: "M1 = Fix f x M0" unfolding is_Fix_def by blast
      have "\<not> val M2" using n normal_AppFix_arg m1 by blast
      moreover have "normal M2" using n m1 unfolding normal_def by (metis beta.OrdApp2)
      ultimately have "stuck M2" using progress by blast
      then show ?thesis using \<open>is_Fix M1\<close> by blast
    qed
  qed
qed

lemma stuck_Pair:
  "stuck (term.Pair M1 M2) \<Longrightarrow> stuck M1 \<or> (val M1 \<and> stuck M2)"
proof -
  assume s: "stuck (term.Pair M1 M2)"
  have n: "normal (term.Pair M1 M2)" using s stucks_are_normal by blast
  have n1: "normal M1" using n unfolding normal_def by (metis beta.OrdPair1)
  show ?thesis
  proof (cases "val M1")
    case False then show ?thesis using n1 progress by blast
  next
    case True
    have "\<not> val M2" using s stuck_not_val True val.intros(3) by blast
    moreover have "normal M2" using True n unfolding normal_def by (metis beta.OrdPair2)
    ultimately have "stuck M2" using progress by blast
    then show ?thesis using True by blast
  qed
qed

lemma normal_Let_notPair:
  "normal (term.Let xy M1 M2) \<Longrightarrow> val M1 \<Longrightarrow> \<not> is_Pair M1"
proof (rule notI)
  assume n: "normal (term.Let xy M1 M2)" and v: "val M1" and p: "is_Pair M1"
  from p obtain V W where m1: "M1 = term.Pair V W" unfolding is_Pair_def by blast
  have vV: "val V" and vW: "val W" using v m1 val_Pair_D by auto
  obtain xy' M2' where eq: "term.Let xy M1 M2 = term.Let xy' M1 M2'" and d: "dset xy' \<inter> FVars V = {}"
    using Let_refresh[of "FVars V" xy M1 M2] finite_FVars by blast
  have "term.Let xy' M1 M2' \<rightarrow> M2'[V <- dfst xy'][W <- dsnd xy']"
    unfolding m1 using beta.Let[OF vV vW d] .
  then show False using n eq normal_def by auto
qed

lemma stuck_Let:
  "stuck (term.Let xy M1 M2) \<Longrightarrow> (val M1 \<and> \<not> is_Pair M1) \<or> stuck M1"
proof -
  assume s: "stuck (term.Let xy M1 M2)"
  have n: "normal (term.Let xy M1 M2)" using s stucks_are_normal by blast
  have n1: "normal M1" using n unfolding normal_def by (metis beta.OrdLet)
  show ?thesis
  proof (cases "val M1")
    case False then show ?thesis using n1 progress by blast
  next
    case True
    then have "\<not> is_Pair M1" using n normal_Let_notPair by blast
    then show ?thesis using True by blast
  qed
qed

lemma dg_Succ: "diverge A \<or> getStuck A \<Longrightarrow> diverge (Succ A) \<or> getStuck (Succ A)"
proof -
  assume dg: "diverge A \<or> getStuck A"
  obtain h where h: "h \<notin> FVars A" by (meson arb_element finite_FVars)
  have ctx: "eval_ctx h (Succ (Var h))" by (rule eval_ctx.intros(4)[OF eval_ctx.intros(1)])
  show ?thesis
  proof (cases "diverge A")
    case True then show ?thesis using div_ctx[OF ctx True] by simp
  next
    case False
    then have "getStuck ((Succ (Var h))[A <- h])" using getStuck_ctx[OF ctx _ h] dg by blast
    then show ?thesis by simp
  qed
qed

lemma dg_Pred: "diverge A \<or> getStuck A \<Longrightarrow> diverge (Pred A) \<or> getStuck (Pred A)"
proof -
  assume dg: "diverge A \<or> getStuck A"
  obtain h where h: "h \<notin> FVars A" by (meson arb_element finite_FVars)
  have ctx: "eval_ctx h (Pred (Var h))" by (rule eval_ctx.intros(5)[OF eval_ctx.intros(1)])
  show ?thesis
  proof (cases "diverge A")
    case True then show ?thesis using div_ctx[OF ctx True] by simp
  next
    case False
    then have "getStuck ((Pred (Var h))[A <- h])" using getStuck_ctx[OF ctx _ h] dg by blast
    then show ?thesis by simp
  qed
qed

lemma dg_If: "diverge A \<or> getStuck A \<Longrightarrow> diverge (If A B C) \<or> getStuck (If A B C)"
proof -
  assume dg: "diverge A \<or> getStuck A"
  obtain h where h: "h \<notin> FVars A \<union> FVars B \<union> FVars C"
    by (meson arb_element finite_FVars finite_Un)
  then have hA: "h \<notin> FVars A" and hB: "h \<notin> FVars B" and hC: "h \<notin> FVars C" by auto
  have ctx: "eval_ctx h (If (Var h) B C)"
    by (rule eval_ctx.intros(9)[OF eval_ctx.intros(1) hB hC])
  have push: "(If (Var h) B C)[A <- h] = If A B C" using hB hC by simp
  show ?thesis
  proof (cases "diverge A")
    case True then show ?thesis using div_ctx[OF ctx True] push by simp
  next
    case False
    then have "getStuck ((If (Var h) B C)[A <- h])" using getStuck_ctx[OF ctx _ hA] dg by blast
    then show ?thesis using push by simp
  qed
qed

lemma dg_App1: "diverge A \<or> getStuck A \<Longrightarrow> diverge (App A B) \<or> getStuck (App A B)"
proof -
  assume dg: "diverge A \<or> getStuck A"
  obtain h where h: "h \<notin> FVars A \<union> FVars B" by (meson arb_element finite_FVars finite_Un)
  then have hA: "h \<notin> FVars A" and hB: "h \<notin> FVars B" by auto
  have ctx: "eval_ctx h (App (Var h) B)" by (rule eval_ctx.intros(3)[OF eval_ctx.intros(1) hB])
  have push: "(App (Var h) B)[A <- h] = App A B" using hB by simp
  show ?thesis
  proof (cases "diverge A")
    case True then show ?thesis using div_ctx[OF ctx True] push by simp
  next
    case False
    then have "getStuck ((App (Var h) B)[A <- h])" using getStuck_ctx[OF ctx _ hA] dg by blast
    then show ?thesis using push by simp
  qed
qed

lemma dg_AppFix2:
  "is_Fix V \<Longrightarrow> diverge B \<or> getStuck B \<Longrightarrow> diverge (App V B) \<or> getStuck (App V B)"
proof -
  assume isf: "is_Fix V" and dg: "diverge B \<or> getStuck B"
  from isf obtain f x M0 where V: "V = Fix f x M0" unfolding is_Fix_def by blast
  obtain h where h: "h \<notin> FVars B \<union> FVars M0" by (meson arb_element finite_FVars finite_Un)
  then have hB: "h \<notin> FVars B" and hM0: "h \<notin> FVars M0" by auto
  have ctx: "eval_ctx h (App (Fix f x M0) (Var h))"
    by (rule eval_ctx.intros(2)[OF eval_ctx.intros(1) hM0])
  have push: "(App (Fix f x M0) (Var h))[B <- h] = App V B" using hM0 V by simp
  show ?thesis
  proof (cases "diverge B")
    case True then show ?thesis using div_ctx[OF ctx True] push by simp
  next
    case False
    then have "getStuck ((App (Fix f x M0) (Var h))[B <- h])" using getStuck_ctx[OF ctx _ hB] dg by blast
    then show ?thesis using push by simp
  qed
qed

lemma dg_Pair1: "diverge A \<or> getStuck A \<Longrightarrow> diverge (term.Pair A B) \<or> getStuck (term.Pair A B)"
proof -
  assume dg: "diverge A \<or> getStuck A"
  obtain h where h: "h \<notin> FVars A \<union> FVars B" by (meson arb_element finite_FVars finite_Un)
  then have hA: "h \<notin> FVars A" and hB: "h \<notin> FVars B" by auto
  have ctx: "eval_ctx h (term.Pair (Var h) B)" by (rule eval_ctx.intros(6)[OF eval_ctx.intros(1) hB])
  have push: "(term.Pair (Var h) B)[A <- h] = term.Pair A B" using hB by simp
  show ?thesis
  proof (cases "diverge A")
    case True then show ?thesis using div_ctx[OF ctx True] push by simp
  next
    case False
    then have "getStuck ((term.Pair (Var h) B)[A <- h])" using getStuck_ctx[OF ctx _ hA] dg by blast
    then show ?thesis using push by simp
  qed
qed

lemma dg_PairV2:
  "val V \<Longrightarrow> diverge B \<or> getStuck B \<Longrightarrow> diverge (term.Pair V B) \<or> getStuck (term.Pair V B)"
proof -
  assume vV: "val V" and dg: "diverge B \<or> getStuck B"
  obtain h where h: "h \<notin> FVars B \<union> FVars V" by (meson arb_element finite_FVars finite_Un)
  then have hB: "h \<notin> FVars B" and hV: "h \<notin> FVars V" by auto
  have ctx: "eval_ctx h (term.Pair V (Var h))"
    by (rule eval_ctx.intros(7)[OF vV eval_ctx.intros(1) hV])
  have push: "(term.Pair V (Var h))[B <- h] = term.Pair V B" using hV by simp
  show ?thesis
  proof (cases "diverge B")
    case True then show ?thesis using div_ctx[OF ctx True] push by simp
  next
    case False
    then have "getStuck ((term.Pair V (Var h))[B <- h])" using getStuck_ctx[OF ctx _ hB] dg by blast
    then show ?thesis using push by simp
  qed
qed

lemma dg_Let1:
  "diverge A \<or> getStuck A \<Longrightarrow> diverge (term.Let xy A B) \<or> getStuck (term.Let xy A B)"
proof -
  assume dg: "diverge A \<or> getStuck A"
  obtain h where h: "h \<notin> FVars A \<union> FVars B \<union> dset xy"
    by (meson arb_element finite_FVars finite_Un finite_dset)
  then have hA: "h \<notin> FVars A" and hB: "h \<notin> FVars B" and hxy: "h \<notin> dset xy" by auto
  have ctx: "eval_ctx h (term.Let xy (Var h) B)"
    by (rule eval_ctx.intros(8)[OF eval_ctx.intros(1) hB hxy])
  have push: "(term.Let xy (Var h) B)[A <- h] = term.Let xy A B"
    using Let_subst_scrutinee[OF hxy hB, of "Var h" A] by simp
  show ?thesis
  proof (cases "diverge A")
    case True then show ?thesis using div_ctx[OF ctx True] push by simp
  next
    case False
    then have "getStuck ((term.Let xy (Var h) B)[A <- h])" using getStuck_ctx[OF ctx _ hA] dg by blast
    then show ?thesis using push by simp
  qed
qed

lemma b5_prop_is_fix:
  assumes "is_Fix V" and "b5_prop V W P N z"
  shows "is_Fix W"
proof -
  from assms(1) obtain f0 x0 R0 where V0: "V = Fix f0 x0 R0" unfolding is_Fix_def by blast
  obtain f x R where eq: "Fix f0 x0 R0 = Fix f x R"
      and fr: "f \<notin> FVars N \<union> FVars P \<union> {z}" "x \<notin> FVars N \<union> FVars P \<union> {z}"
    using Fix_refresh[of "FVars N \<union> FVars P \<union> {z}" f0 x0 R0] finite_FVars by auto
  have "V = Fix f x R" using V0 eq by simp
  then obtain Q' where "W = Fix f x Q'[P <- z]"
    using assms(2) fr unfolding b5_prop_def by metis
  then show ?thesis unfolding is_Fix_def by blast
qed

lemma b6':
  assumes zN: "z \<notin> FVars N" and ls: "P \<lesssim> N"
  shows "stuck (U[N <- z]) \<Longrightarrow> diverge (U[P <- z]) \<or> getStuck (U[P <- z])"
proof (binder_induction U avoiding: N P z rule: term.strong_induct,
    goal_cases Zero Succ Pred If Var App Fix Pair Let)
  case Zero
  then show ?case by (simp add: not_stuck_Zero)
next
  case (Succ M)
  from Succ(2) have "stuck (Succ (M[N <- z]))" by simp
  then consider (r) "val (M[N <- z]) \<and> \<not> num (M[N <- z])" | (c) "stuck (M[N <- z])"
    using stuck_Succ by blast
  then show ?case
  proof cases
    case c
    then have "diverge (M[P <- z]) \<or> getStuck (M[P <- z])" using Succ(1) by blast
    then have "diverge (Succ (M[P <- z])) \<or> getStuck (Succ (M[P <- z]))" by (rule dg_Succ)
    then show ?thesis by simp
  next
    case r
    then have vM: "val (M[N <- z])" and nnM: "\<not> num (M[N <- z])" by auto
    from b5[OF vM zN _ ls, of M] have
      "diverge (M[P <- z]) \<or> (\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop (M[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M[P <- z])"
      then have "diverge (Succ (M[P <- z])) \<or> getStuck (Succ (M[P <- z]))" using dg_Succ by blast
      then show ?thesis by simp
    next
      assume "\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop (M[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M[P <- z] \<rightarrow>* W" and bp: "b5_prop (M[N <- z]) W P N z" by blast
      have "\<not> num W" using bp nnM vM b5_prop_not_num by blast
      then have "stuckEx (Succ W)" using vW stuckEx.intros(1) by blast
      then have "stuck (Succ W)" using stuckEx_imp_stuck by blast
      moreover have "Succ (M[P <- z]) \<rightarrow>* Succ W" using Succ_beta_star sW by blast
      ultimately have "getStuck (Succ (M[P <- z]))" using getStuck_def by blast
      then show ?thesis by simp
    qed
  qed
next
  case (Pred M)
  from Pred(2) have "stuck (Pred (M[N <- z]))" by simp
  then consider (r) "val (M[N <- z]) \<and> \<not> num (M[N <- z])" | (c) "stuck (M[N <- z])"
    using stuck_Pred by blast
  then show ?case
  proof cases
    case c
    then have "diverge (M[P <- z]) \<or> getStuck (M[P <- z])" using Pred(1) by blast
    then have "diverge (Pred (M[P <- z])) \<or> getStuck (Pred (M[P <- z]))" by (rule dg_Pred)
    then show ?thesis by simp
  next
    case r
    then have vM: "val (M[N <- z])" and nnM: "\<not> num (M[N <- z])" by auto
    from b5[OF vM zN _ ls, of M] have
      "diverge (M[P <- z]) \<or> (\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop (M[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M[P <- z])"
      then have "diverge (Pred (M[P <- z])) \<or> getStuck (Pred (M[P <- z]))" using dg_Pred by blast
      then show ?thesis by simp
    next
      assume "\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop (M[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M[P <- z] \<rightarrow>* W" and bp: "b5_prop (M[N <- z]) W P N z" by blast
      have "\<not> num W" using bp nnM vM b5_prop_not_num by blast
      then have "stuckEx (Pred W)" using vW stuckEx.intros(5) by blast
      then have "stuck (Pred W)" using stuckEx_imp_stuck by blast
      moreover have "Pred (M[P <- z]) \<rightarrow>* Pred W" using Pred_beta_star sW by blast
      ultimately have "getStuck (Pred (M[P <- z]))" using getStuck_def by blast
      then show ?thesis by simp
    qed
  qed
next
  case (If M N2 P2)
  from If(4) have "stuck (If (M[N <- z]) (N2[N <- z]) (P2[N <- z]))" by simp
  then consider (r) "val (M[N <- z]) \<and> \<not> num (M[N <- z])" | (c) "stuck (M[N <- z])"
    using stuck_If by blast
  then show ?case
  proof cases
    case c
    then have "diverge (M[P <- z]) \<or> getStuck (M[P <- z])" using If(1) by blast
    then have "diverge (If (M[P <- z]) (N2[P <- z]) (P2[P <- z])) \<or> getStuck (If (M[P <- z]) (N2[P <- z]) (P2[P <- z]))"
      by (rule dg_If)
    then show ?thesis by simp
  next
    case r
    then have vM: "val (M[N <- z])" and nnM: "\<not> num (M[N <- z])" by auto
    from b5[OF vM zN _ ls, of M] have
      "diverge (M[P <- z]) \<or> (\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop (M[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M[P <- z])"
      then have "diverge (If (M[P <- z]) (N2[P <- z]) (P2[P <- z])) \<or> getStuck (If (M[P <- z]) (N2[P <- z]) (P2[P <- z]))"
        using dg_If by blast
      then show ?thesis by simp
    next
      assume "\<exists>W. val W \<and> M[P <- z] \<rightarrow>* W \<and> b5_prop (M[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M[P <- z] \<rightarrow>* W" and bp: "b5_prop (M[N <- z]) W P N z" by blast
      have "\<not> num W" using bp nnM vM b5_prop_not_num by blast
      then have "stuckEx (If W (N2[P <- z]) (P2[P <- z]))" using vW stuckEx.intros(2) by blast
      then have "stuck (If W (N2[P <- z]) (P2[P <- z]))" using stuckEx_imp_stuck by blast
      moreover have "If (M[P <- z]) (N2[P <- z]) (P2[P <- z]) \<rightarrow>* If W (N2[P <- z]) (P2[P <- z])"
        using If_beta_star sW by blast
      ultimately have "getStuck (If (M[P <- z]) (N2[P <- z]) (P2[P <- z]))" using getStuck_def by blast
      then show ?thesis by simp
    qed
  qed
next
  case (Var y)
  show ?case
  proof (cases "y = z")
    case False
    then have "stuck (Var y)" using Var(1) by simp
    then show ?thesis using not_stuck_Var by blast
  next
    case True
    then have sN: "stuck N" using Var(1) by simp
    have pP: "(Var y)[P <- z] = P" using True by simp
    show ?thesis
    proof (cases "diverge P")
      case True then show ?thesis using pP by simp
    next
      case False
      then obtain Nf where Nf: "normal Nf" "P \<rightarrow>* Nf" "N \<rightarrow>* Nf"
        using ls diverge_or_normalizes[of P] unfolding less_defined_def normalizes_def by auto
      have "N = Nf" using Nf(3) stucks_are_normal[OF sN] unfolding beta_star_def normal_def
        by (metis betas.cases)
      then have "P \<rightarrow>* N" using Nf(2) by simp
      then have "getStuck P" using sN getStuck_def by blast
      then show ?thesis using pP by simp
    qed
  qed
next
  case (App M1 M2)
  from App(3) have stApp: "stuck (App (M1[N <- z]) (M2[N <- z]))" by simp
  consider (redex) "val (M1[N <- z]) \<and> \<not> is_Fix (M1[N <- z])"
    | (ctx1) "stuck (M1[N <- z])"
    | (ctxf) "is_Fix (M1[N <- z]) \<and> stuck (M2[N <- z])"
    using stApp stuck_App by blast
  then show ?case
  proof cases
    case ctx1
    then have "diverge (M1[P <- z]) \<or> getStuck (M1[P <- z])" using App(1) by blast
    then have "diverge (App (M1[P <- z]) (M2[P <- z])) \<or> getStuck (App (M1[P <- z]) (M2[P <- z]))"
      by (rule dg_App1)
    then show ?thesis by simp
  next
    case redex
    then have vM1: "val (M1[N <- z])" and nf: "\<not> is_Fix (M1[N <- z])" by auto
    from b5[OF vM1 zN _ ls, of M1] have
      "diverge (M1[P <- z]) \<or> (\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M1[P <- z])"
      then have "diverge (App (M1[P <- z]) (M2[P <- z])) \<or> getStuck (App (M1[P <- z]) (M2[P <- z]))"
        using dg_App1 by blast
      then show ?thesis by simp
    next
      assume "\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M1[P <- z] \<rightarrow>* W" and bp: "b5_prop (M1[N <- z]) W P N z" by blast
      have "\<not> is_Fix W" using vM1 nf bp b5_prop_not_fix unfolding is_Fix_def by blast
      then have "stuckEx (App W (M2[P <- z]))" using vW stuckEx.intros(3) by blast
      then have "stuck (App W (M2[P <- z]))" using stuckEx_imp_stuck by blast
      moreover have "App (M1[P <- z]) (M2[P <- z]) \<rightarrow>* App W (M2[P <- z])" using App_beta_star sW by blast
      ultimately have "getStuck (App (M1[P <- z]) (M2[P <- z]))" using getStuck_def by blast
      then show ?thesis by simp
    qed
  next
    case ctxf
    then have isf: "is_Fix (M1[N <- z])" and st2: "stuck (M2[N <- z])" by auto
    have ihM2: "diverge (M2[P <- z]) \<or> getStuck (M2[P <- z])" using App(2) st2 by blast
    have vM1: "val (M1[N <- z])" using isf by (metis is_Fix_def val.intros(4))
    from b5[OF vM1 zN _ ls, of M1] have
      "diverge (M1[P <- z]) \<or> (\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M1[P <- z])"
      then have "diverge (App (M1[P <- z]) (M2[P <- z])) \<or> getStuck (App (M1[P <- z]) (M2[P <- z]))"
        using dg_App1 by blast
      then show ?thesis by simp
    next
      assume "\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M1[P <- z] \<rightarrow>* W" and bp: "b5_prop (M1[N <- z]) W P N z" by blast
      have "is_Fix W" using isf bp b5_prop_is_fix by blast
      then have "diverge (App W (M2[P <- z])) \<or> getStuck (App W (M2[P <- z]))" using ihM2 dg_AppFix2 by blast
      moreover have "App (M1[P <- z]) (M2[P <- z]) \<rightarrow>* App W (M2[P <- z])" using App_beta_star sW by blast
      ultimately have "diverge (App (M1[P <- z]) (M2[P <- z])) \<or> getStuck (App (M1[P <- z]) (M2[P <- z]))"
        by (metis beta_star_diverge_back beta_star_sums getStuck_def)
      then show ?thesis by simp
    qed
  qed
next
  case (Fix f x M)
  then have "stuck (Fix f x (M[N <- z]))" by simp
  then show ?case using not_stuck_Fix by blast
next
  case (Pair M1 M2)
  from Pair(3) have "stuck (term.Pair (M1[N <- z]) (M2[N <- z]))" by simp
  then consider (ctx1) "stuck (M1[N <- z])" | (ctx2) "val (M1[N <- z]) \<and> stuck (M2[N <- z])"
    using stuck_Pair by blast
  then show ?case
  proof cases
    case ctx1
    then have "diverge (M1[P <- z]) \<or> getStuck (M1[P <- z])" using Pair(1) by blast
    then have "diverge (term.Pair (M1[P <- z]) (M2[P <- z])) \<or> getStuck (term.Pair (M1[P <- z]) (M2[P <- z]))"
      by (rule dg_Pair1)
    then show ?thesis by simp
  next
    case ctx2
    then have vM1: "val (M1[N <- z])" and st2: "stuck (M2[N <- z])" by auto
    have ihM2: "diverge (M2[P <- z]) \<or> getStuck (M2[P <- z])" using Pair(2) st2 by blast
    from b5[OF vM1 zN _ ls, of M1] have
      "diverge (M1[P <- z]) \<or> (\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M1[P <- z])"
      then have "diverge (term.Pair (M1[P <- z]) (M2[P <- z]))" by (simp add: Pair_div)
      then show ?thesis by simp
    next
      assume "\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M1[P <- z] \<rightarrow>* W" by blast
      have "diverge (term.Pair W (M2[P <- z])) \<or> getStuck (term.Pair W (M2[P <- z]))"
        using vW ihM2 dg_PairV2 by blast
      moreover have "term.Pair (M1[P <- z]) (M2[P <- z]) \<rightarrow>* term.Pair W (M2[P <- z])"
        using Pair_beta_star sW vW betas.refl beta_star_def by blast
      ultimately have "diverge (term.Pair (M1[P <- z]) (M2[P <- z])) \<or> getStuck (term.Pair (M1[P <- z]) (M2[P <- z]))"
        by (metis beta_star_diverge_back beta_star_sums getStuck_def)
      then show ?thesis by simp
    qed
  qed
next
  case (Let xy M1 M2)
  have av1: "z \<notin> dset xy" using Let(3) by simp
  have av2: "dset xy \<inter> FVars N = {}" using Let(1) by simp
  have av3: "dset xy \<inter> FVars P = {}" using Let(2) by simp
  have subN: "(term.Let xy M1 M2)[N <- z] = term.Let xy (M1[N <- z]) (M2[N <- z])"
    by (rule usubst_Let[OF av1 av2])
  have subP: "(term.Let xy M1 M2)[P <- z] = term.Let xy (M1[P <- z]) (M2[P <- z])"
    by (rule usubst_Let[OF av1 av3])
  from Let(6) have stLet: "stuck (term.Let xy (M1[N <- z]) (M2[N <- z]))" using subN by simp
  consider (r) "val (M1[N <- z]) \<and> \<not> is_Pair (M1[N <- z])" | (c) "stuck (M1[N <- z])"
    using stLet stuck_Let by blast
  then show ?case
  proof cases
    case c
    then have "diverge (M1[P <- z]) \<or> getStuck (M1[P <- z])" using Let(4) by blast
    then have "diverge (term.Let xy (M1[P <- z]) (M2[P <- z])) \<or> getStuck (term.Let xy (M1[P <- z]) (M2[P <- z]))"
      by (rule dg_Let1)
    then show ?thesis using subP by simp
  next
    case r
    then have vM1: "val (M1[N <- z])" and np: "\<not> is_Pair (M1[N <- z])" by auto
    from b5[OF vM1 zN _ ls, of M1] have
      "diverge (M1[P <- z]) \<or> (\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z)"
      using betas.refl beta_star_def by auto
    then show ?thesis
    proof
      assume "diverge (M1[P <- z])"
      then have "diverge (term.Let xy (M1[P <- z]) (M2[P <- z])) \<or> getStuck (term.Let xy (M1[P <- z]) (M2[P <- z]))"
        using dg_Let1 by blast
      then show ?thesis using subP by simp
    next
      assume "\<exists>W. val W \<and> M1[P <- z] \<rightarrow>* W \<and> b5_prop (M1[N <- z]) W P N z"
      then obtain W where vW: "val W" and sW: "M1[P <- z] \<rightarrow>* W" and bp: "b5_prop (M1[N <- z]) W P N z" by blast
      have "\<not> is_Pair W" using vM1 np bp b5_prop_not_pair unfolding is_Pair_def by blast
      then have "stuckEx (term.Let xy W (M2[P <- z]))" using vW stuckEx.intros(4) by (auto simp: is_Pair_def)
      then have "stuck (term.Let xy W (M2[P <- z]))" using stuckEx_imp_stuck by blast
      moreover have "term.Let xy (M1[P <- z]) (M2[P <- z]) \<rightarrow>* term.Let xy W (M2[P <- z])" using Let_beta_star sW by blast
      ultimately have "getStuck (term.Let xy (M1[P <- z]) (M2[P <- z]))" using getStuck_def by blast
      then show ?thesis using subP by simp
    qed
  qed
qed


lemma b6:
  assumes gsM: "getStuck M[N <- z]" and ls: "P \<lesssim> N" and znN: "z \<notin> FVars N"
  shows "diverge M[P <- z] \<or> getStuck M[P <- z]"
proof -
  obtain M' where redM: "M[N <- z] \<rightarrow>* M'" and stM': "stuck M'" using gsM getStuck_def by auto
  then obtain R where "diverge M[P <- z] \<or> (M[P <- z] \<rightarrow>* R[P <- z] \<and> M' = R[N <- z])"
    unfolding beta_star_def
    using ls znN stucks_are_normal[of M'] b4[of M N z _ M' P] by blast
  then consider (A) "M[P <- z] \<rightarrow>* R[P <- z] \<and> M' = R[N <- z]" | (B) "diverge M[P <- z]" by auto
  then show ?thesis
  proof cases
    case B then show ?thesis by simp
  next
    case A
    then have red: "M[P <- z] \<rightarrow>* R[P <- z]" and eq: "M' = R[N <- z]" by auto
    have "stuck (R[N <- z])" using eq stM' by simp
    then have "diverge (R[P <- z]) \<or> getStuck (R[P <- z])" using b6'[OF znN ls] by blast
    then show ?thesis
      using red by (metis beta_star_diverge_back beta_star_sums getStuck_def)
  qed
qed

section \<open>Thm 4.7\<close>


lemma beta_star_normal_unique:
  assumes "M \<rightarrow>* V" and "normal V" and "M \<rightarrow>* V'" and "normal V'"
  shows "V = V'"
proof -
  from assms(1) obtain n where n: "M \<rightarrow>[n] V" unfolding beta_star_def by auto
  from assms(3) obtain m where m: "M \<rightarrow>[m] V'" unfolding beta_star_def by auto
  have "n \<ge> m" using normalize_longest_beta[OF assms(2) n m] .
  moreover have "m \<ge> n" using normalize_longest_beta[OF assms(4) m n] .
  ultimately have "n = m" by simp
  then show ?thesis using betas_deterministic n m by metis
qed

lemma val_tau_iff:
  assumes "val V"
  shows "(V \<in> \<T>\<lblot>A\<rblot>) = (V \<in> \<lblot>A\<rblot>)"
proof
  assume "V \<in> \<T>\<lblot>A\<rblot>"
  then obtain V' where iA: "V' \<in> \<lblot>A\<rblot>" and sV': "V \<rightarrow>* V'" and vV': "val V'"
    unfolding tau_semantics.simps by auto
  have "V \<rightarrow>* V" using beta_star_def betas.refl by blast
  then have "V = V'"
    using beta_star_normal_unique[OF _ vals_are_normal[OF assms] sV' vals_are_normal[OF vV']] by blast
  then show "V \<in> \<lblot>A\<rblot>" using iA by simp
next
  assume vin: "V \<in> \<lblot>A\<rblot>"
  have "V \<rightarrow>* V" using beta_star_def betas.refl by blast
  then show "V \<in> \<T>\<lblot>A\<rblot>" unfolding tau_semantics.simps
    using vin assms by (auto intro!: bexI[of _ V])
qed

inductive finitely_verifiable :: "type \<Rightarrow> bool" where
  "finitely_verifiable Nat"
| "finitely_verifiable Ok"
| "finitely_verifiable F1 \<Longrightarrow> finitely_verifiable F2 \<Longrightarrow> finitely_verifiable (Prod F1 F2)"

inductive safe :: "type \<Rightarrow> bool" where
  "safe Nat"
| "safe Ok"
| "safe A \<Longrightarrow> safe B \<Longrightarrow> safe (Prod A B)"
| "safe A \<Longrightarrow> safe B \<Longrightarrow> safe (To A B)"
| "safe A \<Longrightarrow> finitely_verifiable F \<Longrightarrow> safe (OnlyTo A F)"

lemma diverge_xor_normalizes: "\<not> (normalizes M \<and> diverge M)"
proof
  assume "normalizes M \<and> diverge M"
  then have "normalizes M" and "diverge M" by auto
  then obtain N where "normal N" and "M \<rightarrow>* N" unfolding normalizes_def by auto
  then have "diverge N" using \<open>diverge M\<close> beta_star_diverge_forw by auto
  then obtain N' where "N \<rightarrow> N'" using diverge.cases by auto
  then show False using \<open>normal N\<close> unfolding normal_def by auto
qed

lemma less_defined_diverge:
  assumes "P \<lesssim> Q" and "diverge Q"
  shows "diverge P"
  using assms(2)
proof(rule contrapos_pp[of "diverge Q" "diverge P"])
  assume "\<not> diverge P"
  then have "normalizes P" using diverge_or_normalizes by auto
  then obtain N where "normal N" and "Q \<rightarrow>* N" 
    using \<open>P \<lesssim> Q\<close> unfolding less_defined_def by auto
  then have "normalizes Q" unfolding normalizes_def by auto
  then show "\<not> diverge Q" using diverge_xor_normalizes by auto
qed

text \<open>Infrastructure for @{text less_defined_diverge_subst}: bounded reduction lemmas and the
  key one-step lemma @{text ldds_step} (well-founded on @{term "count_term z M"}: a term whose
  @{text N}-substitution diverges either diverges under the @{text Q}-substitution or takes at least
  one step to another such term; the measure drops when a blocked @{text z} at the evaluation
  position is resolved to its value).\<close>

lemma betas_prefix: "M \<rightarrow>[a] X \<Longrightarrow> M \<rightarrow>[b] Y \<Longrightarrow> a \<le> b \<Longrightarrow> X \<rightarrow>[b - a] Y"
proof (induction a arbitrary: M b)
  case 0
  then have "X = M" by (auto elim: betas.cases)
  then show ?case using 0 by simp
next
  case (Suc a)
  from Suc.prems(1) obtain M1 where m1: "M \<rightarrow> M1" and r1: "M1 \<rightarrow>[a] X"
    by (auto elim: betas.cases)
  from Suc.prems(3) obtain b' where b': "b = Suc b'" using Suc_le_D by blast
  from Suc.prems(2) b' obtain M2 where m2: "M \<rightarrow> M2" and r2: "M2 \<rightarrow>[b'] Y"
    by (auto elim: betas.cases)
  have "M1 = M2" using m1 m2 beta_deterministic by blast
  then have "M1 \<rightarrow>[b'] Y" using r2 by simp
  then have "X \<rightarrow>[b' - a] Y" using Suc.IH[OF r1] Suc.prems(3) b' by simp
  then show ?case using b' by simp
qed

lemma diverge_reduces_k: "diverge M \<Longrightarrow> \<exists>N. M \<rightarrow>[k] N"
proof (induction k arbitrary: M)
  case 0 then show ?case using betas.refl by blast
next
  case (Suc k)
  from Suc.prems obtain M1 where "M \<rightarrow> M1" and "diverge M1" using diverge.cases by blast
  then obtain N where "M1 \<rightarrow>[k] N" using Suc.IH by blast
  then show ?case using \<open>M \<rightarrow> M1\<close> betas.step by blast
qed

lemma diverge_of_infinite: "(\<forall>k. \<exists>N. M \<rightarrow>[k] N) \<Longrightarrow> diverge M"
proof (coinduction arbitrary: M rule: diverge.coinduct)
  case (diverge M)
  then obtain M1 where m1: "M \<rightarrow>[1] M1" by blast
  then have "M \<rightarrow> M1" by (auto elim: betas.cases)
  moreover have "\<forall>k. \<exists>N. M1 \<rightarrow>[k] N"
  proof
    fix k
    from diverge obtain N where "M \<rightarrow>[Suc k] N" by blast
    then obtain P where "M \<rightarrow> P" and "P \<rightarrow>[k] N" by (auto elim: betas.cases)
    then have "M1 = P" using \<open>M \<rightarrow> M1\<close> beta_deterministic by blast
    then show "\<exists>N. M1 \<rightarrow>[k] N" using \<open>P \<rightarrow>[k] N\<close> by blast
  qed
  ultimately show ?case by blast
qed

lemma ldds_step:
  assumes ls: "Q \<lesssim> N" and zN: "z \<notin> FVars N"
  shows "diverge M[N <- z] \<Longrightarrow>
    diverge M[Q <- z] \<or> (\<exists>n M'. M[Q <- z] \<rightarrow>[Suc n] M'[Q <- z] \<and> diverge M'[N <- z])"
proof (induction M rule: measure_induct_rule[where f = "\<lambda>M. count_term z M"])
  case (less M)
  note Md = less.prems
  show ?case
  proof (cases "blocked z M")
    case False
    from Md obtain X where sX: "M[N <- z] \<rightarrow> X" and "diverge X" using diverge.cases by blast
    then obtain M' where "M \<rightarrow> M'" and mX: "M'[N <- z] = X"
      using b3_root[of "M[N <- z]" X M N z] False by auto
    then have "M[Q <- z] \<rightarrow> M'[Q <- z]" using beta_subst_unblocked False by auto
    then have "M[Q <- z] \<rightarrow>[Suc 0] M'[Q <- z]" using betas.refl betas.step by fastforce
    moreover have "diverge M'[N <- z]" using \<open>diverge X\<close> mX by simp
    ultimately show ?thesis by blast
  next
    case True
    obtain E hole where Meq: "M = E[Var z <- hole]" and hz: "hole \<noteq> z"
      and niN: "hole \<notin> FVars N" and niQ: "hole \<notin> FVars Q"
      and ctx_subst: "\<forall>Na. hole \<notin> FVars Na \<longrightarrow> eval_ctx hole E[Na <- z]"
      using blocked_fresh_hole[of "FVars N \<union> FVars Q" z M] finite_FVars True by auto
    have ctxN: "eval_ctx hole (E[N <- z])" using ctx_subst niN by auto
    have ctxQ: "eval_ctx hole (E[Q <- z])" using ctx_subst niQ by auto
    have MNeq: "M[N <- z] = E[N <- z][N <- hole]"
      using Meq usubst_usubst[of hole z N] hz niN by simp
    have MQeq: "M[Q <- z] = E[Q <- z][Q <- hole]"
      using Meq usubst_usubst[of hole z Q] hz niQ by simp
    show ?thesis
    proof (cases "diverge Q")
      case True
      have "diverge (E[Q <- z][Q <- hole])" using div_ctx[OF ctxQ True] .
      then show ?thesis using MQeq by simp
    next
      case False
      then have "normalizes Q" using diverge_or_normalizes by auto
      then obtain Nf where nf: "normal Nf" and QNf: "Q \<rightarrow>* Nf" and NNf: "N \<rightarrow>* Nf"
        using ls unfolding less_defined_def by auto
      have dNfN: "diverge (E[N <- z][Nf <- hole])"
      proof -
        have "E[N <- z][N <- hole] \<rightarrow>* E[N <- z][Nf <- hole]"
          using eval_ctx_beta_star[OF ctxN NNf] .
        then show ?thesis using Md MNeq beta_star_diverge_forw by simp
      qed
      have hNf: "hole \<notin> FVars Nf" using NNf FVars_beta_star niN by auto
      have znNf: "z \<notin> FVars Nf" using NNf FVars_beta_star zN by auto
      have vNf: "val Nf"
      proof (rule ccontr)
        assume "\<not> val Nf"
        then have "stuck Nf" using nf progress by auto
        then have "stuck (E[N <- z][Nf <- hole])" using stuck_ctx[OF ctxN _ hNf] by auto
        then have "normalizes (E[N <- z][Nf <- hole])"
          using stucks_are_normal normals_normalizes by blast
        then show False using dNfN diverge_xor_normalizes by blast
      qed
      define M2 where "M2 = E[Nf <- hole]"
      have M2N: "M2[N <- z] = E[N <- z][Nf <- hole]"
        unfolding M2_def using usubst_usubst[of hole z N] hz niN znNf by simp
      have M2Q: "M2[Q <- z] = E[Q <- z][Nf <- hole]"
        unfolding M2_def using usubst_usubst[of hole z Q] hz niQ znNf by simp
      have chE: "count_term hole E = 1"
      proof -
        have "count_term hole (E[N <- z]) = count_term hole E"
          using count_subst[of z hole E N] hz niN by simp
        then show ?thesis using count_eval_ctx[OF ctxN] by simp
      qed
      have "count_term z M = count_term hole E * 1 + count_term z E"
        unfolding Meq using count_subst[of hole z E "Var z"] hz by simp
      moreover have "count_term z M2 = count_term hole E * 0 + count_term z E"
        unfolding M2_def using count_subst[of hole z E Nf] hz znNf by simp
      ultimately have cnt: "count_term z M2 < count_term z M" using chE by simp
      have dM2N: "diverge M2[N <- z]" using M2N dNfN by simp
      obtain a where QNfa: "Q \<rightarrow>[a] Nf" using QNf beta_star_def by auto
      have redMM2: "M[Q <- z] \<rightarrow>[a] M2[Q <- z]"
        using MQeq M2Q eval_ctx_betas[OF ctxQ QNfa] by simp
      from less.IH[OF cnt dM2N] show ?thesis
      proof
        assume "diverge M2[Q <- z]"
        then have "diverge M[Q <- z]"
          using redMM2 betas_diverge_back by blast
        then show ?thesis by blast
      next
        assume "\<exists>n M'. M2[Q <- z] \<rightarrow>[Suc n] M'[Q <- z] \<and> diverge M'[N <- z]"
        then obtain n M' where st: "M2[Q <- z] \<rightarrow>[Suc n] M'[Q <- z]" and dM'N: "diverge M'[N <- z]" by blast
        have "M[Q <- z] \<rightarrow>[a + Suc n] M'[Q <- z]" using redMM2 st betas_path_sum by blast
        then have "M[Q <- z] \<rightarrow>[Suc (a + n)] M'[Q <- z]" by simp
        then show ?thesis using dM'N by blast
      qed
    qed
  qed
qed

lemma betas_take: "M \<rightarrow>[b] Y \<Longrightarrow> k \<le> b \<Longrightarrow> \<exists>t. M \<rightarrow>[k] t"
proof (induction k arbitrary: M b)
  case 0 show ?case using betas.refl by blast
next
  case (Suc k)
  from Suc.prems(2) obtain b' where b': "b = Suc b'" using Suc_le_D by blast
  from Suc.prems(1) b' obtain M1 where "M \<rightarrow> M1" and "M1 \<rightarrow>[b'] Y" by (auto elim: betas.cases)
  moreover have "k \<le> b'" using Suc.prems(2) b' by simp
  ultimately obtain t where "M1 \<rightarrow>[k] t" using Suc.IH by blast
  then show ?case using \<open>M \<rightarrow> M1\<close> betas.step by blast
qed

lemma less_defined_diverge_subst:
  assumes ls: "Q \<lesssim> N" and zN: "z \<notin> FVars N" and Md: "diverge M[N <- z]"
  shows "diverge M[Q <- z]"
proof (rule diverge_of_infinite, rule allI)
  have key: "\<And>k M. diverge M[N <- z] \<Longrightarrow> \<exists>t. M[Q <- z] \<rightarrow>[k] t"
  proof -
    fix k0 M0
    show "diverge M0[N <- z] \<Longrightarrow> \<exists>t. M0[Q <- z] \<rightarrow>[k0] t"
    proof (induction k0 arbitrary: M0 rule: less_induct)
      case (less k M)
      from ldds_step[OF ls zN less.prems] show ?case
      proof
        assume "diverge M[Q <- z]"
        then show ?thesis using diverge_reduces_k by blast
      next
        assume "\<exists>n M'. M[Q <- z] \<rightarrow>[Suc n] M'[Q <- z] \<and> diverge M'[N <- z]"
        then obtain n M' where st: "M[Q <- z] \<rightarrow>[Suc n] M'[Q <- z]" and dM': "diverge M'[N <- z]" by blast
        show ?thesis
        proof (cases "k \<le> Suc n")
          case True
          then show ?thesis using st betas_take by blast
        next
          case False
          then have "k - Suc n < k" and "Suc n + (k - Suc n) = k" by auto
          then obtain t where "M'[Q <- z] \<rightarrow>[k - Suc n] t" using less.IH dM' by blast
          then have "M[Q <- z] \<rightarrow>[Suc n + (k - Suc n)] t" using st betas_path_sum by blast
          then show ?thesis using \<open>Suc n + (k - Suc n) = k\<close> by metis
        qed
      qed
    qed
  qed
  fix k show "\<exists>t. M[Q <- z] \<rightarrow>[k] t" using key[OF Md] by blast
qed

text \<open>The fixpoint-unfolding at a value is independent of the chosen binder representation
  (the paper reads @{term "V \<in> \<lblot>To A B\<rblot>"} for whatever @{text "V = Fix f x R"} one has to hand):
  both unfoldings are the unique @{text FixBeta}-reduct of @{term "App V U"} for a closed argument
  @{text U}.\<close>
lemma To_unfold:
  assumes iV: "V \<in> \<lblot>To A B\<rblot>" and vU: "val U" and clU: "FVars U = {}" and iU: "U \<in> \<lblot>A\<rblot>"
      and Veq: "V = Fix f x R"
  shows "R[U <- x][V <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
proof -
  from iV obtain f' x' M0' where V': "V = Fix f' x' M0'"
      and prop': "\<forall>U'\<in>Vals0. FVars U' = {} \<longrightarrow> U' \<in> \<lblot>A\<rblot> \<longrightarrow> M0'[U' <- x'][Fix f' x' M0' <- f'] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
    unfolding type_semantics.simps by blast
  have m: "M0'[U <- x'][V <- f'] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
    using prop' vU clU iU V' unfolding Vals0_def by auto
  have fU: "f \<notin> FVars U" and f'U: "f' \<notin> FVars U" using clU by auto
  have "App V U \<rightarrow> R[U <- x][V <- f]" using beta.FixBeta[OF vU fU, of x R] Veq by simp
  moreover have "App V U \<rightarrow> M0'[U <- x'][V <- f']" using beta.FixBeta[OF vU f'U, of x' M0'] V' by simp
  ultimately have "R[U <- x][V <- f] = M0'[U <- x'][V <- f']" using beta_deterministic by blast
  then show ?thesis using m by simp
qed

lemma OnlyTo_unfold:
  assumes iV: "V \<in> \<lblot>OnlyTo A B\<rblot>" and vU: "val U" and clU: "FVars U = {}"
      and Veq: "V = Fix f x R" and mem: "R[U <- x][V <- f] \<in> \<T>\<lblot>B\<rblot>"
  shows "U \<in> \<lblot>A\<rblot>"
proof -
  from iV obtain f' x' M0' where V': "V = Fix f' x' M0'"
      and prop': "\<forall>U'\<in>Vals0. FVars U' = {} \<longrightarrow> M0'[U' <- x'][Fix f' x' M0' <- f'] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> U' \<in> \<lblot>A\<rblot>"
    unfolding type_semantics.simps by blast
  have fU: "f \<notin> FVars U" and f'U: "f' \<notin> FVars U" using clU by auto
  have "App V U \<rightarrow> R[U <- x][V <- f]" using beta.FixBeta[OF vU fU, of x R] Veq by simp
  moreover have "App V U \<rightarrow> M0'[U <- x'][V <- f']" using beta.FixBeta[OF vU f'U, of x' M0'] V' by simp
  ultimately have "R[U <- x][V <- f] = M0'[U <- x'][V <- f']" using beta_deterministic by blast
  then have "M0'[U <- x'][V <- f'] \<in> \<T>\<lblot>B\<rblot>" using mem by simp
  then show ?thesis using prop' vU clU V' unfolding Vals0_def by auto
qed

text \<open>The paper's substitution equation @{text "(Q'[V/x, fix f(x).Q'/f])[N/z]
  = (Q'[N/z])[V/x, fix f(x).Q'[N/z]]"}, valid because the argument @{text U} is closed
  (Def.\ 4.1: @{text Vals0} are the closed values).\<close>
lemma unfold_subst:
  assumes clU: "FVars U = {}" and fz: "f \<noteq> z" and xz: "x \<noteq> z"
      and fS: "f \<notin> FVars S" and xS: "x \<notin> FVars S"
  shows "(Q0[U <- x][Fix f x Q0 <- f])[S <- z]
       = (Q0[S <- z])[U <- x][Fix f x (Q0[S <- z]) <- f]"
proof -
  have zU: "z \<notin> FVars U" using clU by simp
  have e1: "(Q0[U <- x][Fix f x Q0 <- f])[S <- z]
      = (Q0[U <- x])[S <- z][(Fix f x Q0)[S <- z] <- f]"
    by (rule usubst_usubst[OF fz fS])
  have e2: "(Q0[U <- x])[S <- z] = (Q0[S <- z])[U <- x]"
    using usubst_usubst[OF xz xS, of Q0 U] zU by simp
  have e3: "(Fix f x Q0)[S <- z] = Fix f x (Q0[S <- z])"
    using fz xz fS xS by simp
  show ?thesis unfolding e1 e2 e3 ..
qed

lemma safe_Prod: "safe (Prod A B) \<Longrightarrow> safe A \<and> safe B" by (auto elim: safe.cases)
lemma safe_To: "safe (To A B) \<Longrightarrow> safe A \<and> safe B" by (auto elim: safe.cases)
lemma safe_OnlyTo: "safe (OnlyTo A B) \<Longrightarrow> safe A \<and> finitely_verifiable B" by (auto elim: safe.cases)
lemma fv_Prod: "finitely_verifiable (Prod A B) \<Longrightarrow> finitely_verifiable A \<and> finitely_verifiable B"
  by (auto elim: finitely_verifiable.cases)
lemma not_fv_To: "\<not> finitely_verifiable (To A B)" by (auto elim: finitely_verifiable.cases)
lemma not_fv_OnlyTo: "\<not> finitely_verifiable (OnlyTo A B)" by (auto elim: finitely_verifiable.cases)

theorem b7_induction:
  assumes cl: "FVars M[N <- z] = {}" and ls: "Q \<lesssim> N" and nzN: "z \<notin> FVars N"
  shows "safe A \<Longrightarrow> M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow> M[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    and "finitely_verifiable A \<Longrightarrow> M[N <- z] \<notin> \<T>\<lblot>A\<rblot> \<Longrightarrow> M[Q <- z] \<notin> \<T>\<lblot>A\<rblot>"
proof(induction A arbitrary: M)
  case Nat
  {
    case 1
    then consider (A) "(M[N <- z] \<in> \<T>\<lblot>Nat\<rblot>)" | (B) "(M[N <- z] \<Up>)" 
      using bottom_semantics.simps by auto
    then show ?case
    proof cases
      case A
      then obtain n where "num n" and "M[N <- z] \<rightarrow>* n"
        using tau_semantics.simps type_semantics.simps(2) by auto
      then have "diverge M[Q <- z] \<or> M[Q <- z] \<rightarrow>* n" 
        using ls val.intros(2)[of n] nzN b5[of n z N M Q] b5_prop_def[of n]
        by (metis num_not_haveFix)
      then show ?thesis 
        unfolding bottom_semantics.simps tau_semantics.simps type_semantics.simps(2)
        using \<open>num n\<close> val.intros(2) by auto
    next
      case B
      then show ?thesis unfolding bottom_semantics.simps 
        using less_defined_diverge_subst ls nzN by blast
    qed
  next
    case 2
    consider (A) "\<exists>V. M[N <- z] \<rightarrow>* V \<and> val V" | (B) "getStuck M[N <- z]" | (C) "diverge M[N <- z]"
    proof -
      have "diverge M[N <- z] \<or> normalizes M[N <- z]" by (rule diverge_or_normalizes)
      then show thesis
      proof
        assume "diverge M[N <- z]"
        then show thesis by (rule that(3))
      next
        assume "normalizes M[N <- z]"
        then obtain Nf where nf: "normal Nf" and st: "M[N <- z] \<rightarrow>* Nf"
          unfolding normalizes_def by auto
        have "val Nf \<or> stuck Nf" using val_stuck_step[of Nf] nf unfolding normal_def by auto
        then show thesis
        proof
          assume "val Nf" then show thesis using st by (intro that(1)) auto
        next
          assume "stuck Nf" then show thesis using st by (intro that(2)) (auto simp: getStuck_def)
        qed
      qed
    qed
    then show ?case
      proof cases
        case A
        then obtain V where sV: "M[N <- z] \<rightarrow>* V" and vV: "val V" and nV: "V \<notin> \<lblot>Nat\<rblot>"
          using 2 unfolding tau_semantics.simps by blast
        have nnV: "\<not> num V" using nV unfolding type_semantics.simps(2) by simp
        have "diverge M[Q <- z] \<or> (\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z)"
          using b5[of V z N M Q] vV nzN sV ls by simp
        then show ?thesis
        proof
          assume "diverge M[Q <- z]"
          then show ?thesis unfolding tau_semantics.simps
            using diverge_xor_normalizes vals_are_normal normalizes_def by auto
        next
          assume "\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z"
          then obtain W where vW: "val W" and sW: "M[Q <- z] \<rightarrow>* W" and bp: "b5_prop V W Q N z" by auto
          have nnW: "\<not> num W" using b5_prop_not_num[OF vV nnV bp] .
          show ?thesis
          proof
            assume "M[Q <- z] \<in> \<T>\<lblot>Nat\<rblot>"
            then obtain n where nn: "num n" and sn: "M[Q <- z] \<rightarrow>* n"
              unfolding tau_semantics.simps type_semantics.simps(2) by auto
            have "n = W" using beta_star_normal_unique[OF sn nums_are_normal[OF nn] sW vals_are_normal[OF vW]] .
            then show False using nn nnW by simp
          qed
        qed
      next
        case B
        then have disj: "diverge M[Q <- z] \<or> getStuck M[Q <- z]"
          using ls nzN b6[of M N z Q] by auto
        show ?thesis
        proof
          assume "M[Q <- z] \<in> \<T>\<lblot>Nat\<rblot>"
          then obtain n where nn: "num n" and sn: "M[Q <- z] \<rightarrow>* n"
            unfolding tau_semantics.simps type_semantics.simps(2) by auto
          from disj show False
          proof
            assume "diverge M[Q <- z]"
            then show False
              using diverge_xor_normalizes[of "M[Q <- z]"] sn nums_are_normal[OF nn] normalizes_def by blast
          next
            assume "getStuck M[Q <- z]"
            then obtain S where sS0: "stuck S" and sS: "M[Q <- z] \<rightarrow>* S" unfolding getStuck_def by auto
            have eq: "n = S" using beta_star_normal_unique[OF sn nums_are_normal[OF nn] sS stucks_are_normal[OF sS0]] .
            have "val n" using nn val.intros(2) by blast
            then have "val S" unfolding eq .
            then show False using sS0 stuck_not_val by blast
          qed
        qed
      next
        case C
        then have "diverge M[Q <- z]" 
          using ls nzN less_defined_diverge_subst by auto
        then show ?thesis unfolding tau_semantics.simps 
          using diverge_xor_normalizes vals_are_normal normalizes_def
          by auto
      qed
  }
next
  case (Prod A1 A2)
  {
    case 1
    then have safeP: "safe (Prod A1 A2)" and memb1: "M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>Prod A1 A2\<rblot>" by blast+
    have sA1: "safe A1" and sA2: "safe A2" using safe_Prod[OF safeP] by blast+
    from memb1 consider (A) "diverge M[N <- z]" | (B) "\<exists>V1 V2. M[N <- z] \<rightarrow>* (Pair V1 V2) \<and> V1 \<in> \<lblot>A1\<rblot> \<and> V2 \<in> \<lblot>A2\<rblot> \<and> val (Pair V1 V2)"
      unfolding bottom_semantics.simps tau_semantics.simps type_semantics.simps
      by auto
    then show ?case
    proof cases
      case A
      then have "diverge M[Q <- z]" 
        using ls nzN less_defined_diverge_subst by auto                 
      then show ?thesis by simp
    next
      case B
      then obtain V1 V2 where steps: "M[N <- z] \<rightarrow>* term.Pair V1 V2" and "V1 \<in> \<lblot>A1\<rblot>" and "V2 \<in> \<lblot>A2\<rblot>" and "val (Pair V1 V2)"
        by auto
      then consider 
        (B1) "diverge M[Q <- z]" | (B2) "\<exists>W. M[Q <- z] \<rightarrow>* W \<and> b5_prop (term.Pair V1 V2) W Q N z"
        using nzN ls b5[of "Pair V1 V2" z N M Q] by auto
      then show ?thesis
      proof cases
        case B2
        then obtain W where M2W: "M[Q <- z] \<rightarrow>* W" and bpW: "b5_prop (term.Pair V1 V2) W Q N z" by auto
        have vv12: "val V1 \<and> val V2"
          using \<open>val (Pair V1 V2)\<close> by (cases rule: val.cases) (auto elim: num.cases)
        have vV1: "val V1" and vV2: "val V2" using vv12 by auto
        from bpW obtain W1 W2 where wW: "W = Pair W1[Q <- z] W2[Q <- z]"
          and w1: "W1[N <- z] = V1" and w2: "W2[N <- z] = V2"
          unfolding b5_prop_def by blast
        have iA1: "W1[N <- z] \<in> \<lblot>A1\<rblot>" and iA2: "W2[N <- z] \<in> \<lblot>A2\<rblot>"
          using \<open>V1 \<in> \<lblot>A1\<rblot>\<close> \<open>V2 \<in> \<lblot>A2\<rblot>\<close> w1 w2 by auto
        have vW1N: "val W1[N <- z]" and vW2N: "val W2[N <- z]" using vV1 vV2 w1 w2 by auto
        have "W1[N <- z] \<in> \<T>\<lblot>A1\<rblot>" using iA1 vW1N unfolding tau_semantics.simps
          by (auto simp: beta_star_def intro!: betas.refl)
        then have TbN1: "W1[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>" unfolding bottom_semantics.simps by simp
        have "W2[N <- z] \<in> \<T>\<lblot>A2\<rblot>" using iA2 vW2N unfolding tau_semantics.simps
          by (auto simp: beta_star_def intro!: betas.refl)
        then have TbN2: "W2[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" unfolding bottom_semantics.simps by simp
        from TbN1 TbN2 have TbA1: "W1[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>" and TbA2: "W2[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
          using Prod.IH(1)[OF sA1, of W1] Prod.IH(3)[OF sA2, of W2] by auto
        from TbA1 TbA2 consider (a) "diverge W1[Q <- z] \<or> diverge W2[Q <- z]"
          | (b) "W1[Q <- z] \<in> \<T>\<lblot>A1\<rblot> \<and> W2[Q <- z] \<in> \<T>\<lblot>A2\<rblot>"
          unfolding bottom_semantics.simps by auto
        then show ?thesis
        proof cases
          case a
          have "diverge W"
          proof (cases "diverge W1[Q <- z]")
            case True
            then show ?thesis unfolding wW by (rule Pair_div)
          next
            case False
            then have "W1[Q <- z] \<in> \<T>\<lblot>A1\<rblot>" using TbA1 unfolding bottom_semantics.simps by simp
            then obtain U1 where sU1: "W1[Q <- z] \<rightarrow>* U1" and vU1: "val U1"
              unfolding tau_semantics.simps by auto
            have dW2: "diverge W2[Q <- z]" using a False by simp
            have reflW2: "W2[Q <- z] \<rightarrow>* W2[Q <- z]" using beta_star_def betas.refl by blast
            have "Pair W1[Q <- z] W2[Q <- z] \<rightarrow>* Pair U1 W2[Q <- z]"
              by (rule Pair_beta_star[OF sU1 reflW2 vU1])
            moreover have "diverge (Pair U1 W2[Q <- z])" by (rule Pair_div2[OF vU1 dW2])
            ultimately show ?thesis unfolding wW using beta_star_diverge_back by blast
          qed
          then show ?thesis using beta_star_diverge_back M2W by auto
        next
          case b
          then have TA1: "W1[Q <- z] \<in> \<T>\<lblot>A1\<rblot>" and TA2: "W2[Q <- z] \<in> \<T>\<lblot>A2\<rblot>" by auto
          from TA1 obtain U1 where sU1: "W1[Q <- z] \<rightarrow>* U1" and vU1: "val U1" and iU1: "U1 \<in> \<lblot>A1\<rblot>"
            unfolding tau_semantics.simps by auto
          from TA2 obtain U2 where sU2: "W2[Q <- z] \<rightarrow>* U2" and vU2: "val U2" and iU2: "U2 \<in> \<lblot>A2\<rblot>"
            unfolding tau_semantics.simps by auto
          have "W \<rightarrow>* Pair U1 U2" unfolding wW by (rule Pair_beta_star[OF sU1 sU2 vU1])
          moreover have "val (Pair U1 U2)" using vU1 vU2 val.intros(3) by blast
          moreover have "Pair U1 U2 \<in> \<lblot>Prod A1 A2\<rblot>"
            unfolding type_semantics.simps using iU1 iU2 by (auto intro!: image_eqI[of _ _ "(U1, U2)"])
          ultimately have "W \<in> \<T>\<lblot>Prod A1 A2\<rblot>" unfolding tau_semantics.simps by blast
          then have "M[Q <- z] \<in> \<T>\<lblot>Prod A1 A2\<rblot>" unfolding tau_semantics.simps
            using M2W beta_star_sums by blast
          then show ?thesis unfolding bottom_semantics.simps by auto
        qed
      qed(auto)
    qed
  next
    case 2
    then have fvP: "finitely_verifiable (Prod A1 A2)" and notT: "M[N <- z] \<notin> \<T>\<lblot>Prod A1 A2\<rblot>" by blast+
    have fA1: "finitely_verifiable A1" and fA2: "finitely_verifiable A2" using fv_Prod[OF fvP] by blast+
    consider (A) "\<exists>V. M[N <- z] \<rightarrow>* V \<and> val V" | (B) "getStuck M[N <- z]" | (C) "diverge M[N <- z]"
    proof -
      have "diverge M[N <- z] \<or> normalizes M[N <- z]" by (rule diverge_or_normalizes)
      then show thesis
      proof
        assume "diverge M[N <- z]" then show thesis by (rule that(3))
      next
        assume "normalizes M[N <- z]"
        then obtain Nf where nf: "normal Nf" and st: "M[N <- z] \<rightarrow>* Nf"
          unfolding normalizes_def by auto
        have "val Nf \<or> stuck Nf" using val_stuck_step[of Nf] nf unfolding normal_def by auto
        then show thesis
        proof
          assume "val Nf" then show thesis using st by (intro that(1)) auto
        next
          assume "stuck Nf" then show thesis using st by (intro that(2)) (auto simp: getStuck_def)
        qed
      qed
    qed
    then show ?case
    proof cases
      case C
      then have "diverge M[Q <- z]" using ls nzN less_defined_diverge_subst by auto
      then show ?thesis unfolding tau_semantics.simps
        using diverge_xor_normalizes vals_are_normal normalizes_def by auto
    next
      case B
      then have disj: "diverge M[Q <- z] \<or> getStuck M[Q <- z]"
        using ls nzN b6[of M N z Q] by auto
      show ?thesis
      proof
        assume "M[Q <- z] \<in> \<T>\<lblot>Prod A1 A2\<rblot>"
        then obtain W where vW: "val W" and sW: "M[Q <- z] \<rightarrow>* W"
          unfolding tau_semantics.simps by auto
        from disj show False
        proof
          assume "diverge M[Q <- z]"
          then show False using sW vals_are_normal[OF vW] diverge_xor_normalizes normalizes_def by blast
        next
          assume "getStuck M[Q <- z]"
          then obtain S where sS0: "stuck S" and sS: "M[Q <- z] \<rightarrow>* S" unfolding getStuck_def by auto
          have "W = S" using beta_star_normal_unique[OF sW vals_are_normal[OF vW] sS stucks_are_normal[OF sS0]] .
          then show False using vW sS0 stuck_not_val by blast
        qed
      qed
    next
      case A
      then obtain V where sV: "M[N <- z] \<rightarrow>* V" and vV: "val V" by auto
      have nVP: "V \<notin> \<lblot>Prod A1 A2\<rblot>" using notT sV vV unfolding tau_semantics.simps by auto
      have "diverge M[Q <- z] \<or> (\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z)"
        using b5[of V z N M Q] vV nzN sV ls by simp
      then show ?thesis
      proof
        assume "diverge M[Q <- z]"
        then show ?thesis unfolding tau_semantics.simps
          using diverge_xor_normalizes vals_are_normal normalizes_def by auto
      next
        assume "\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z"
        then obtain W where vW: "val W" and sW: "M[Q <- z] \<rightarrow>* W" and bp: "b5_prop V W Q N z" by auto
        have wNP: "W \<notin> \<lblot>Prod A1 A2\<rblot>"
        proof (cases "\<exists>V1 V2. V = Pair V1 V2")
          case False
          then have "\<nexists>W1 W2. W = Pair W1 W2"
            using b5_prop_not_pair[OF vV _ bp] by auto
          then show ?thesis unfolding type_semantics.simps by auto
        next
          case True
          then obtain V1 V2 where vEq: "V = Pair V1 V2" by auto
          have vv: "val V1 \<and> val V2"
            using vV vEq by (cases rule: val.cases) (auto elim: num.cases)
          then have vV1: "val V1" and vV2: "val V2" by auto
          obtain W1 W2 where wW: "W = Pair W1[Q <- z] W2[Q <- z]"
            and w1: "W1[N <- z] = V1" and w2: "W2[N <- z] = V2"
            using bp vEq unfolding b5_prop_def by blast
          have vw: "val W1[Q <- z] \<and> val W2[Q <- z]"
            using vW wW by (cases rule: val.cases) (auto elim: num.cases)
          then have vW1: "val W1[Q <- z]" and vW2: "val W2[Q <- z]" by auto
          from nVP vEq have "V1 \<notin> \<lblot>A1\<rblot> \<or> V2 \<notin> \<lblot>A2\<rblot>"
            unfolding type_semantics.simps by auto
          then have "W1[Q <- z] \<notin> \<lblot>A1\<rblot> \<or> W2[Q <- z] \<notin> \<lblot>A2\<rblot>"
          proof
            assume "V1 \<notin> \<lblot>A1\<rblot>"
            then have "W1[N <- z] \<notin> \<T>\<lblot>A1\<rblot>" using w1 vV1 val_tau_iff by auto
            then have "W1[Q <- z] \<notin> \<T>\<lblot>A1\<rblot>" using Prod.IH(2)[OF fA1, of W1] by auto
            then have "W1[Q <- z] \<notin> \<lblot>A1\<rblot>" using vW1 val_tau_iff by auto
            then show ?thesis by simp
          next
            assume "V2 \<notin> \<lblot>A2\<rblot>"
            then have "W2[N <- z] \<notin> \<T>\<lblot>A2\<rblot>" using w2 vV2 val_tau_iff by auto
            then have "W2[Q <- z] \<notin> \<T>\<lblot>A2\<rblot>" using Prod.IH(4)[OF fA2, of W2] by auto
            then have "W2[Q <- z] \<notin> \<lblot>A2\<rblot>" using vW2 val_tau_iff by auto
            then show ?thesis by simp
          qed
          then show ?thesis unfolding wW type_semantics.simps by auto
        qed
        show ?thesis
        proof
          assume "M[Q <- z] \<in> \<T>\<lblot>Prod A1 A2\<rblot>"
          then obtain P where vP: "val P" and sP: "M[Q <- z] \<rightarrow>* P" and iP: "P \<in> \<lblot>Prod A1 A2\<rblot>"
            unfolding tau_semantics.simps by auto
          have "W = P" using beta_star_normal_unique[OF sW vals_are_normal[OF vW] sP vals_are_normal[OF vP]] .
          then show False using wNP iP by simp
        qed
      qed
    qed
  }
next
  case (To A1 A2)
  {
    case 1
    then have safeT: "safe (To A1 A2)" and memb1: "M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>To A1 A2\<rblot>" by blast+
    have sA2: "safe A2" using safe_To[OF safeT] by blast
    from memb1 have "M[N <- z] \<in> \<T>\<lblot>To A1 A2\<rblot> \<or> diverge M[N <- z]"
      unfolding bottom_semantics.simps by simp
    then show ?case
    proof
      assume "diverge M[N <- z]"
      then have "diverge M[Q <- z]" using ls nzN less_defined_diverge_subst by auto
      then show ?thesis unfolding bottom_semantics.simps by simp
    next
      assume "M[N <- z] \<in> \<T>\<lblot>To A1 A2\<rblot>"
      then obtain V where iV: "V \<in> \<lblot>To A1 A2\<rblot>" and sV: "M[N <- z] \<rightarrow>* V" and vV: "val V"
        unfolding tau_semantics.simps by auto
      from iV obtain f0 x0 R0 where "V = Fix f0 x0 R0" unfolding type_semantics.simps by blast
      then obtain f x R where Veq: "V = Fix f x R"
          and fr: "f \<notin> FVars N \<union> FVars Q \<union> {z}" and xr: "x \<notin> FVars N \<union> FVars Q \<union> {z}"
        using Fix_refresh[of "FVars N \<union> FVars Q \<union> {z}" f0 x0 R0] finite_FVars by auto
      have fN: "f \<notin> FVars N" "f \<notin> FVars Q" "f \<noteq> z" and xN: "x \<notin> FVars N" "x \<notin> FVars Q" "x \<noteq> z"
        using fr xr by auto
      from b5[of V z N M Q] vV nzN sV ls
      have "diverge M[Q <- z] \<or> (\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z)" by simp
      then show ?thesis
      proof
        assume "diverge M[Q <- z]"
        then show ?thesis unfolding bottom_semantics.simps by simp
      next
        assume "\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z"
        then obtain W where vW: "val W" and sW: "M[Q <- z] \<rightarrow>* W" and bp: "b5_prop V W Q N z" by auto
        from bp Veq fr xr obtain Q0 where Weq: "W = Fix f x (Q0[Q <- z])" and Q0N: "Q0[N <- z] = R"
          unfolding b5_prop_def by (metis (no_types, lifting))
        have "W \<in> \<lblot>To A1 A2\<rblot>"
        proof -
          have "\<forall>U \<in> Vals0. FVars U = {} \<longrightarrow> U \<in> \<lblot>A1\<rblot> \<longrightarrow> (Q0[Q <- z])[U <- x][W <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
          proof (intro ballI impI)
            fix U :: "'a term"
            assume U0: "U \<in> Vals0" and clU: "FVars U = {}" and iU: "U \<in> \<lblot>A1\<rblot>"
            have vU: "val U" using U0 unfolding Vals0_def by simp
            have VpropU: "R[U <- x][V <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" using To_unfold[OF iV vU clU iU Veq] .
            have Tn: "(Q0[U <- x][Fix f x Q0 <- f])[N <- z] = R[U <- x][V <- f]"
              using unfold_subst[OF clU fN(3) xN(3) fN(1) xN(1), of Q0] Q0N Veq by simp
            have Tq: "(Q0[U <- x][Fix f x Q0 <- f])[Q <- z] = (Q0[Q <- z])[U <- x][W <- f]"
              using unfold_subst[OF clU fN(3) xN(3) fN(2) xN(2), of Q0] Weq by simp
            have "(Q0[U <- x][Fix f x Q0 <- f])[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" using Tn VpropU by simp
            then have "(Q0[U <- x][Fix f x Q0 <- f])[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" using To.IH(3)[OF sA2] by blast
            then show "(Q0[Q <- z])[U <- x][W <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" using Tq by simp
          qed
          then show ?thesis unfolding Weq type_semantics.simps by blast
        qed
        then have "M[Q <- z] \<in> \<T>\<lblot>To A1 A2\<rblot>" using sW vW unfolding tau_semantics.simps by auto
        then show ?thesis unfolding bottom_semantics.simps by simp
      qed
    qed
  next
    case 2
    then show ?case using not_fv_To by blast
  }
next
  case (OnlyTo A1 A2)
  {
    case 1
    then have safeO: "safe (OnlyTo A1 A2)" and memb1: "M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A1 A2\<rblot>" by blast+
    have fvA2: "finitely_verifiable A2" using safe_OnlyTo[OF safeO] by blast
    from memb1 have "M[N <- z] \<in> \<T>\<lblot>OnlyTo A1 A2\<rblot> \<or> diverge M[N <- z]"
      unfolding bottom_semantics.simps by simp
    then show ?case
    proof
      assume "diverge M[N <- z]"
      then have "diverge M[Q <- z]" using ls nzN less_defined_diverge_subst by auto
      then show ?thesis unfolding bottom_semantics.simps by simp
    next
      assume "M[N <- z] \<in> \<T>\<lblot>OnlyTo A1 A2\<rblot>"
      then obtain V where iV: "V \<in> \<lblot>OnlyTo A1 A2\<rblot>" and sV: "M[N <- z] \<rightarrow>* V" and vV: "val V"
        unfolding tau_semantics.simps by auto
      from iV obtain f0 x0 R0 where "V = Fix f0 x0 R0" unfolding type_semantics.simps by blast
      then obtain f x R where Veq: "V = Fix f x R"
          and fr: "f \<notin> FVars N \<union> FVars Q \<union> {z}" and xr: "x \<notin> FVars N \<union> FVars Q \<union> {z}"
        using Fix_refresh[of "FVars N \<union> FVars Q \<union> {z}" f0 x0 R0] finite_FVars by auto
      have fN: "f \<notin> FVars N" "f \<notin> FVars Q" "f \<noteq> z" and xN: "x \<notin> FVars N" "x \<notin> FVars Q" "x \<noteq> z"
        using fr xr by auto
      from b5[of V z N M Q] vV nzN sV ls
      have "diverge M[Q <- z] \<or> (\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z)" by simp
      then show ?thesis
      proof
        assume "diverge M[Q <- z]"
        then show ?thesis unfolding bottom_semantics.simps by simp
      next
        assume "\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z"
        then obtain W where vW: "val W" and sW: "M[Q <- z] \<rightarrow>* W" and bp: "b5_prop V W Q N z" by auto
        from bp Veq fr xr obtain Q0 where Weq: "W = Fix f x (Q0[Q <- z])" and Q0N: "Q0[N <- z] = R"
          unfolding b5_prop_def by (metis (no_types, lifting))
        have "W \<in> \<lblot>OnlyTo A1 A2\<rblot>"
        proof -
          have "\<forall>U \<in> Vals0. FVars U = {} \<longrightarrow> (Q0[Q <- z])[U <- x][W <- f] \<in> \<T>\<lblot>A2\<rblot> \<longrightarrow> U \<in> \<lblot>A1\<rblot>"
          proof (intro ballI impI)
            fix U :: "'a term"
            assume U0: "U \<in> Vals0" and clU: "FVars U = {}"
              and mem: "(Q0[Q <- z])[U <- x][W <- f] \<in> \<T>\<lblot>A2\<rblot>"
            have vU: "val U" using U0 unfolding Vals0_def by simp
            have Tq: "(Q0[U <- x][Fix f x Q0 <- f])[Q <- z] = (Q0[Q <- z])[U <- x][W <- f]"
              using unfold_subst[OF clU fN(3) xN(3) fN(2) xN(2), of Q0] Weq by simp
            have Tn: "(Q0[U <- x][Fix f x Q0 <- f])[N <- z] = R[U <- x][V <- f]"
              using unfold_subst[OF clU fN(3) xN(3) fN(1) xN(1), of Q0] Q0N Veq by simp
            have "(Q0[U <- x][Fix f x Q0 <- f])[Q <- z] \<in> \<T>\<lblot>A2\<rblot>" using Tq mem by simp
            then have "(Q0[U <- x][Fix f x Q0 <- f])[N <- z] \<in> \<T>\<lblot>A2\<rblot>"
              using OnlyTo.IH(4)[OF fvA2, of "Q0[U <- x][Fix f x Q0 <- f]"] by blast
            then have "R[U <- x][V <- f] \<in> \<T>\<lblot>A2\<rblot>" using Tn by simp
            then show "U \<in> \<lblot>A1\<rblot>" using OnlyTo_unfold[OF iV vU clU Veq] by blast
          qed
          then show ?thesis unfolding Weq type_semantics.simps by blast
        qed
        then have "M[Q <- z] \<in> \<T>\<lblot>OnlyTo A1 A2\<rblot>" using sW vW unfolding tau_semantics.simps by auto
        then show ?thesis unfolding bottom_semantics.simps by simp
      qed
    qed
  next
    case 2
    then show ?case using not_fv_OnlyTo by blast
  }
next
  case Ok
  {
    case 1
    then consider (A) "diverge M[N <- z]" | (B) "\<exists>V. M[N <- z] \<rightarrow>* V \<and> val V"
      unfolding bottom_semantics.simps tau_semantics.simps type_semantics.simps
      by (auto simp: Vals0_def)
    then show ?case
    proof cases
      case A
      then have "diverge M[Q <- z]" using ls nzN less_defined_diverge_subst by auto
      then show ?thesis unfolding bottom_semantics.simps by simp
    next
      case B
      then obtain V where sV: "M[N <- z] \<rightarrow>* V" and vV: "val V" by auto
      have "diverge M[Q <- z] \<or> (\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z)"
        using b5[of V z N M Q] vV nzN sV ls by simp
      then show ?thesis
      proof
        assume "diverge M[Q <- z]"
        then show ?thesis unfolding bottom_semantics.simps by simp
      next
        assume "\<exists>W. val W \<and> M[Q <- z] \<rightarrow>* W \<and> b5_prop V W Q N z"
        then obtain W where "val W" and "M[Q <- z] \<rightarrow>* W" by auto
        then show ?thesis unfolding bottom_semantics.simps tau_semantics.simps type_semantics.simps
          by (auto simp: Vals0_def)
      qed
    qed
  next
    case 2
    then have notT: "M[N <- z] \<notin> \<T>\<lblot>Ok\<rblot>" by simp
    consider (B) "getStuck M[N <- z]" | (C) "diverge M[N <- z]"
    proof -
      have "diverge M[N <- z] \<or> normalizes M[N <- z]" by (rule diverge_or_normalizes)
      then show thesis
      proof
        assume "diverge M[N <- z]" then show thesis by (rule that(2))
      next
        assume "normalizes M[N <- z]"
        then obtain Nf where nf: "normal Nf" and st: "M[N <- z] \<rightarrow>* Nf"
          unfolding normalizes_def by auto
        have "val Nf \<or> stuck Nf" using val_stuck_step[of Nf] nf unfolding normal_def by auto
        then show thesis
        proof
          assume "val Nf"
          then have "M[N <- z] \<in> \<T>\<lblot>Ok\<rblot>" using st
            unfolding tau_semantics.simps type_semantics.simps by (auto simp: Vals0_def)
          then show thesis using notT by simp
        next
          assume "stuck Nf" then show thesis using st by (intro that(1)) (auto simp: getStuck_def)
        qed
      qed
    qed
    then show ?case
    proof cases
      case B
      then have disj: "diverge M[Q <- z] \<or> getStuck M[Q <- z]"
        using ls nzN b6[of M N z Q] by auto
      show ?thesis
      proof
        assume "M[Q <- z] \<in> \<T>\<lblot>Ok\<rblot>"
        then obtain W where vW: "val W" and sW: "M[Q <- z] \<rightarrow>* W"
          unfolding tau_semantics.simps type_semantics.simps by (auto simp: Vals0_def)
        from disj show False
        proof
          assume "diverge M[Q <- z]"
          then show False using sW vals_are_normal[OF vW] diverge_xor_normalizes normalizes_def by blast
        next
          assume "getStuck M[Q <- z]"
          then obtain S where sS0: "stuck S" and sS: "M[Q <- z] \<rightarrow>* S" unfolding getStuck_def by auto
          have "W = S" using beta_star_normal_unique[OF sW vals_are_normal[OF vW] sS stucks_are_normal[OF sS0]] .
          then show False using vW sS0 stuck_not_val by blast
        qed
      qed
    next
      case C
      then have "diverge M[Q <- z]" using ls nzN less_defined_diverge_subst by auto
      then show ?thesis unfolding tau_semantics.simps type_semantics.simps
        using diverge_xor_normalizes vals_are_normal normalizes_def by (auto simp: Vals0_def)
    qed
  }
qed

theorem b7:
  assumes cl: "FVars M[N <- z] = {}" and ls: "Q \<lesssim> N"
  shows "(safe A \<longrightarrow> M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<longrightarrow> M[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>)
       \<and> (finitely_verifiable A \<longrightarrow> M[N <- z] \<notin> \<T>\<lblot>A\<rblot> \<longrightarrow> M[Q <- z] \<notin> \<T>\<lblot>A\<rblot>)"
proof(cases "z \<in> FVars M")
  case True
  then have "z \<notin> FVars N" using cl FVars_usubst[of M N z] by auto
  then show ?thesis using cl ls b7_induction[of M N z Q A] by blast
next
  case False
  then show ?thesis using subst_idle[of z M] by auto
qed

section \<open>Fixpoint Approximants (Definition 4.3)\<close>

text \<open>For the second half of Theorem 4.7 (property (S2), Theorem B.8 of the paper) we need
  fixpoint approximants. These are built from lambda abstractions, which the paper treats as
  syntactic sugar: \<open>\<lambda>x. M\<close> stands for \<open>fix f(x). M\<close> where \<open>f\<close> is not free in \<open>M\<close>. We first make
  this precise; up to alpha-equivalence the choice of \<open>f\<close> does not matter.\<close>

lemma fresh_finite: "finite (A :: 'a::var set) \<Longrightarrow> \<exists>f. f \<notin> A"
  by (rule exists_fresh, rule finite_ordLess_infinite2[OF _ infinite_UNIV])

definition Lam :: "'a::var \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "Lam x M = Fix (SOME f. f \<notin> FVars M \<and> f \<noteq> x) x M"

lemma Lam_eq:
  fixes M :: "'a::var term"
  assumes f: "f \<notin> FVars M" "f \<noteq> x"
  shows "Lam x M = Fix f x M"
proof -
  define g where "g = (SOME f. f \<notin> FVars M \<and> f \<noteq> x)"
  have ex: "\<exists>f. f \<notin> FVars M \<and> f \<noteq> x"
    using fresh_finite[of "FVars M \<union> {x}"] by auto
  have g: "g \<notin> FVars M" "g \<noteq> x"
    using someI_ex[OF ex] unfolding g_def by auto
  have "Fix g x M = Fix f x M"
  proof (cases "g = f")
    case False
    have pM: "permute_term (g \<leftrightarrow> f) M = M"
      by (rule term.permute_cong_id[OF bij_swap supp_swap_bound[OF infinite_UNIV]])
        (use f g in \<open>auto simp: swap_def\<close>)
    have idon: "id_on (FVars M - {x, g}) (g \<leftrightarrow> f)"
      unfolding id_on_def using f g by (auto simp: swap_def)
    have xgf: "x \<noteq> g" "x \<noteq> f" using f g by auto
    show ?thesis
      unfolding term.inject(6)
      by (rule exI[of _ "g \<leftrightarrow> f"])
        (use f g xgf False pM idon in \<open>auto simp: infinite_UNIV\<close>)
  qed simp
  then show ?thesis unfolding Lam_def g_def[symmetric] .
qed

lemma val_Lam[simp]: "val (Lam x M)"
  unfolding Lam_def by (rule val.intros(4))

lemma FVars_Lam[simp]: "FVars (Lam x M) = FVars M - {x}"
proof -
  obtain f where f: "f \<notin> FVars M" "f \<noteq> x"
    using fresh_finite[of "FVars M \<union> {x}"] by auto
  show ?thesis unfolding Lam_eq[OF f] using f by auto
qed

lemma Lam_permute:
  fixes \<sigma> :: "'a::var \<Rightarrow> 'a"
  assumes b: "bij \<sigma>" and s: "|supp \<sigma>| <o |UNIV::'a set|"
  shows "permute_term \<sigma> (Lam x M) = Lam (\<sigma> x) (permute_term \<sigma> M)"
proof -
  obtain f where f: "f \<notin> FVars M" "f \<noteq> x"
    using fresh_finite[of "FVars M \<union> {x}"] by auto
  have "permute_term \<sigma> (Lam x M) = Fix (\<sigma> f) (\<sigma> x) (permute_term \<sigma> M)"
    unfolding Lam_eq[OF f] by (simp add: term.permute(7)[OF b s])
  also have "... = Lam (\<sigma> x) (permute_term \<sigma> M)"
    by (rule Lam_eq[symmetric])
      (use f b s in \<open>auto simp: term.FVars_permute[OF b s] bij_implies_inject\<close>)
  finally show ?thesis .
qed

lemma Lam_beta:
  fixes W :: "'a::var term"
  assumes "val W"
  shows "App (Lam x M) W \<rightarrow> M[W <- x]"
proof -
  obtain f where f: "f \<notin> FVars M \<union> FVars W \<union> {x}"
    using fresh_finite[of "FVars M \<union> FVars W \<union> {x}"] by auto
  have step: "App (Fix f x M) W \<rightarrow> M[W <- x][Fix f x M <- f]"
    by (rule beta.FixBeta) (use assms f in auto)
  have "f \<notin> FVars (M[W <- x])"
    using f by (auto simp: FVars_usubst split: if_splits)
  then show ?thesis
    using step Lam_eq[of f M x] f by (simp add: subst_idle)
qed

text \<open>A canonical diverging closed term, the paper's \<open>div\<close>: we use \<open>(fix f(x). f x) 0\<close>.\<close>

definition omega :: "'a::var term" where
  "omega = (SOME W. \<exists>f x. f \<noteq> x \<and> W = Fix f x (App (Var f) (Var x)))"

lemma Fix_selfapp_permute:
  fixes h :: "'a::var \<Rightarrow> 'a"
  assumes h: "bij h" "|supp h| <o |UNIV::'a set|"
  shows "Fix a b (App (Var a) (Var b)) = Fix (h a) (h b) (App (Var (h a)) (Var (h b)))"
proof -
  have "Fix a b (App (Var a) (Var b)) = permute_term h (Fix a b (App (Var a) (Var b)))"
    by (rule term.permute_cong_id[OF h, symmetric]) auto
  also have "... = Fix (h a) (h b) (App (Var (h a)) (Var (h b)))"
    by (simp add: term.permute[OF h])
  finally show ?thesis .
qed

lemma Fix_selfapp_alpha:
  fixes f x g y :: "'a::var"
  assumes fx: "f \<noteq> x" and gy: "g \<noteq> y"
  shows "Fix f x (App (Var f) (Var x)) = Fix g y (App (Var g) (Var y))"
proof -
  obtain f' where f1: "f' \<notin> {f, x, g, y}" using fresh_finite[of "{f,x,g,y}"] by auto
  obtain x' where x1: "x' \<notin> {f, x, g, y, f'}" using fresh_finite[of "{f,x,g,y,f'}"] by auto
  have b1: "bij ((x \<leftrightarrow> x') \<circ> (f \<leftrightarrow> f'))" "|supp ((x \<leftrightarrow> x') \<circ> (f \<leftrightarrow> f'))| <o |UNIV::'a set|"
    by (auto simp: supp_comp_bound infinite_UNIV bij_comp)
  have v1: "((x \<leftrightarrow> x') \<circ> (f \<leftrightarrow> f')) f = f'" and v2: "((x \<leftrightarrow> x') \<circ> (f \<leftrightarrow> f')) x = x'"
    using fx f1 x1 by auto
  have b2: "bij ((y \<leftrightarrow> x') \<circ> (g \<leftrightarrow> f'))" "|supp ((y \<leftrightarrow> x') \<circ> (g \<leftrightarrow> f'))| <o |UNIV::'a set|"
    by (auto simp: supp_comp_bound infinite_UNIV bij_comp)
  have w1: "((y \<leftrightarrow> x') \<circ> (g \<leftrightarrow> f')) g = f'" and w2: "((y \<leftrightarrow> x') \<circ> (g \<leftrightarrow> f')) y = x'"
    using gy f1 x1 by auto
  have e1: "Fix f x (App (Var f) (Var x)) = Fix f' x' (App (Var f') (Var x'))"
    using Fix_selfapp_permute[OF b1, of f x] unfolding v1 v2 .
  have e2: "Fix g y (App (Var g) (Var y)) = Fix f' x' (App (Var f') (Var x'))"
    using Fix_selfapp_permute[OF b2, of g y] unfolding w1 w2 .
  show ?thesis by (rule trans[OF e1 e2[symmetric]])
qed

lemma omega_eq:
  fixes f x :: "'a::var"
  assumes "f \<noteq> x"
  shows "omega = Fix f x (App (Var f) (Var x))"
proof -
  have ex: "\<exists>W::'a term. \<exists>g y. g \<noteq> y \<and> W = Fix g y (App (Var g) (Var y))"
    using assms by blast
  show ?thesis
    unfolding omega_def
    by (rule someI2_ex[OF ex]) (use assms in \<open>blast intro: Fix_selfapp_alpha\<close>)
qed

lemma ex_two_distinct: "\<exists>a b :: 'a::var. a \<noteq> b"
proof -
  obtain b where "(b::'a) \<notin> {undefined}" using fresh_finite[of "{undefined}"] by auto
  then show ?thesis by auto
qed

lemma val_omega[simp]: "val (omega :: 'a::var term)"
proof -
  obtain a b :: 'a where "a \<noteq> b" using ex_two_distinct by auto
  show ?thesis unfolding omega_eq[OF \<open>a \<noteq> b\<close>] by (rule val.intros(4))
qed

lemma FVars_omega[simp]: "FVars (omega :: 'a::var term) = {}"
proof -
  obtain a b :: 'a where "a \<noteq> b" using ex_two_distinct by auto
  then show ?thesis unfolding omega_eq[OF \<open>a \<noteq> b\<close>] by auto
qed

definition divt :: "'a::var term" where
  "divt = App omega Zero"

lemma omega_selfstep:
  fixes V :: "'a::var term"
  assumes "val V" and "FVars V = {}"
  shows "App omega V \<rightarrow> App omega V"
proof -
  obtain a b :: 'a where ab: "a \<noteq> b" using ex_two_distinct by auto
  have o: "omega = Fix a b (App (Var a) (Var b))" by (rule omega_eq[OF ab])
  have step: "App (Fix a b (App (Var a) (Var b))) V
      \<rightarrow> (App (Var a) (Var b))[V <- b][Fix a b (App (Var a) (Var b)) <- a]"
    by (rule beta.FixBeta) (use assms in auto)
  have "(App (Var a) (Var b))[V <- b][Fix a b (App (Var a) (Var b)) <- a]
      = App (Fix a b (App (Var a) (Var b))) (V[Fix a b (App (Var a) (Var b)) <- a])"
    using ab by simp
  also have "... = App (Fix a b (App (Var a) (Var b))) V"
    using assms(2) by (simp add: subst_idle)
  finally show ?thesis using step unfolding o by simp
qed

lemma divt_step: "(divt :: 'a::var term) \<rightarrow> divt"
  unfolding divt_def by (rule omega_selfstep) (auto intro: val.intros num.intros)

lemma divt_diverge: "(divt :: 'a::var term) \<Up>"
  apply (rule diverge.coinduct[of "\<lambda>M. M = divt"])
   apply simp
  by (metis divt_step)

lemma FVars_divt[simp]: "FVars (divt :: 'a::var term) = {}"
  unfolding divt_def by auto

lemma divt_permute[simp]:
  fixes \<sigma> :: "'a::var \<Rightarrow> 'a"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
  shows "permute_term \<sigma> (divt :: 'a term) = divt"
  by (rule term.permute_cong_id[OF assms]) auto

lemma divt_not_normalizes: "\<not> normalizes (divt :: 'a::var term)"
  using divt_diverge diverge_xor_normalizes by blast

lemma divt_in_taubot: "(divt :: 'a::var term) \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  using divt_diverge by auto

lemma divt_notin_tau: "(divt :: 'a::var term) \<notin> \<T>\<lblot>A\<rblot>"
proof
  assume "(divt :: 'a term) \<in> \<T>\<lblot>A\<rblot>"
  then obtain V where "divt \<rightarrow>* (V :: 'a term)" "val V" by auto
  then show False
    using divt_not_normalizes vals_are_normal unfolding normalizes_def by blast
qed

text \<open>The fixpoint approximants themselves (Definition 4.3):
  \<open>fix\<^sup>0 f(x). M = \<lambda>x. div\<close> and \<open>fix\<^sup>n\<^sup>+\<^sup>1 f(x). M = \<lambda>x. M[fix\<^sup>n f(x). M / f]\<close>.\<close>

primrec fixapp :: "nat \<Rightarrow> 'a::var \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "fixapp 0 f x M = Lam x divt"
| "fixapp (Suc n) f x M = Lam x (M[fixapp n f x M <- f])"

lemma FVars_fixapp: "FVars (fixapp n f x M) \<subseteq> FVars M - {f, x}"
  by (induction n) (auto simp: FVars_usubst split: if_splits)

lemma val_fixapp[simp]: "val (fixapp n f x M)"
  by (cases n) auto

lemma fixapp_permute:
  fixes \<sigma> :: "'a::var \<Rightarrow> 'a"
  assumes b: "bij \<sigma>" and s: "|supp \<sigma>| <o |UNIV::'a set|"
  shows "permute_term \<sigma> (fixapp n f x M) = fixapp n (\<sigma> f) (\<sigma> x) (permute_term \<sigma> M)"
  by (induction n)
    (auto simp: Lam_permute[OF assms] permute_usubst[OF assms] divt_permute[OF assms])

lemma fixapp_cong:
  fixes M :: "'a::var term"
  assumes "Fix f x M = Fix f' x' M'"
  shows "fixapp n f x M = fixapp n f' x' M'"
proof -
  obtain \<sigma> where \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" "id_on (FVars M - {x, f}) \<sigma>"
    "\<sigma> f = f'" "\<sigma> x = x'" "permute_term \<sigma> M = M'"
    using assms[unfolded term.inject(6)] by auto
  have "fixapp n f' x' M' = permute_term \<sigma> (fixapp n f x M)"
    by (simp add: fixapp_permute[OF \<sigma>(1,2)] \<sigma>(4,5,6))
  also have "permute_term \<sigma> (fixapp n f x M) = fixapp n f x M"
    by (rule term.permute_cong_id[OF \<sigma>(1,2)])
      (use FVars_fixapp[of n f x M] \<sigma>(3) in \<open>auto simp: id_on_def\<close>)
  finally show ?thesis by simp
qed

lemma fixapp_beta:
  fixes W :: "'a::var term"
  assumes "val W" and "f \<noteq> x" and "f \<notin> FVars W"
  shows "App (fixapp (Suc n) f x M) W \<rightarrow> M[W <- x][fixapp n f x M <- f]"
proof -
  have step: "App (Lam x (M[fixapp n f x M <- f])) W \<rightarrow> M[fixapp n f x M <- f][W <- x]"
    by (rule Lam_beta[OF assms(1)])
  have x_fresh: "x \<notin> FVars (fixapp n f x M)"
    using FVars_fixapp[of n f x M] by auto
  have "M[fixapp n f x M <- f][W <- x] = M[W <- x][(fixapp n f x M)[W <- x] <- f]"
    by (rule usubst_usubst[OF assms(2,3)])
  also have "... = M[W <- x][fixapp n f x M <- f]"
    unfolding subst_idle[OF x_fresh] ..
  finally have eq: "M[fixapp n f x M <- f][W <- x] = M[W <- x][fixapp n f x M <- f]" .
  show ?thesis using step unfolding fixapp.simps(2) eq .
qed

lemma fixapp0_beta:
  fixes W :: "'a::var term"
  assumes "val W"
  shows "App (fixapp 0 f x M) W \<rightarrow> divt"
  using Lam_beta[OF assms, of x divt] by (simp add: subst_idle)


subsection \<open>The approximation relation\<close>

text \<open>\<open>apx n P Q\<close> holds when \<open>Q\<close> is obtained from \<open>P\<close> by replacing some closed fixpoint
  subterms \<open>fix f(x). M\<close> of \<open>P\<close> by approximants \<open>fix\<^sup>k f(x). M\<close> with \<open>k \<ge> n\<close>. This makes precise
  the paper's informal talk (proof of Theorem B.8) of "replacing all descendants of occurrences of
  \<open>fix f(x). M\<close> by holes": different residuals of a fixpoint may have been unfolded a different
  number of times, so a single uniform index does not survive reduction, but a lower bound does.\<close>

inductive apx :: "nat \<Rightarrow> 'a::var term \<Rightarrow> 'a term \<Rightarrow> bool" where
  apx_Zero: "apx n Zero Zero"
| apx_Var: "apx n (Var v) (Var v)"
| apx_Succ: "apx n M M' \<Longrightarrow> apx n (Succ M) (Succ M')"
| apx_Pred: "apx n M M' \<Longrightarrow> apx n (Pred M) (Pred M')"
| apx_If: "apx n M M' \<Longrightarrow> apx n N N' \<Longrightarrow> apx n P P' \<Longrightarrow> apx n (If M N P) (If M' N' P')"
| apx_App: "apx n M M' \<Longrightarrow> apx n N N' \<Longrightarrow> apx n (App M N) (App M' N')"
| apx_Pair: "apx n M M' \<Longrightarrow> apx n N N' \<Longrightarrow> apx n (Pair M N) (Pair M' N')"
| apx_Fix: "apx n M M' \<Longrightarrow> apx n (Fix f x M) (Fix f x M')"
| apx_Let: "apx n M M' \<Longrightarrow> apx n N N' \<Longrightarrow> apx n (Let xy M N) (Let xy M' N')"
| apx_Ax: "FVars M \<subseteq> {f, x} \<Longrightarrow> f \<noteq> x \<Longrightarrow> n \<le> k \<Longrightarrow> apx n (Fix f x M) (fixapp k f x M)"

lemmas [equiv] = Lam_permute divt_permute fixapp_permute

text \<open>Equivariance is discharged automatically thanks to the \<open>equiv\<close> registrations above.
  Refreshability: the seven non-binding rules take \<open>B' = {}\<close>; the two congruence rules rename the
  binders freshly on both sides simultaneously (using the equivariance of the induction relation
  \<open>R\<close>, which the obligation provides), and the approximant rule additionally transports the
  approximant along the renaming via @{thm fixapp_cong}.\<close>
binder_inductive apx
  subgoal premises prems for R B n P Q
  proof -
    from prems(3) show ?thesis
    proof (elim disjE exE conjE, goal_cases)
      case (1 n') then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (2 n' v) then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (3 n' M M') then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (4 n' M M') then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (5 n' M M' N N' P' P'') then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (6 n' M M' N N') then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (7 n' M M' N N') then show ?case by (intro exI[of _ "{}"]) auto
    next
      case (8 n' M M' f x)
      have b1: "|{f, x}| <o |UNIV::'a set|"
        by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
      have b2: "|{f, x} \<union> FVars M \<union> FVars M'| <o |UNIV::'a set|"
        by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
      obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
          "g ` {f, x} \<inter> ({f, x} \<union> FVars M \<union> FVars M') = {}"
          "id_on ((FVars M \<union> FVars M') - {x, f}) g" "g \<circ> g = id"
        using eextend_fresh[OF b1 b2 infinite_UNIV, of "(FVars M \<union> FVars M') - {x, f}"]
        by (auto simp: insert_commute)
      have idM: "id_on (FVars M - {x, f}) g" and idM': "id_on (FVars M' - {x, f}) g"
        using g(4) by (auto simp: id_on_def)
      have eqM: "Fix f x M = Fix (g f) (g x) (permute_term g M)"
        using g(1,2) idM by (auto intro!: exI[of _ g])
      have eqM': "Fix f x M' = Fix (g f) (g x) (permute_term g M')"
        using g(1,2) idM' by (auto intro!: exI[of _ g])
      have Rg: "R n' (permute_term g M) (permute_term g M')"
        using prems(2)[OF g(1,2) 8(5)] by simp
      show ?case
        apply (rule exI[of _ "{g f, g x}"])
        apply (rule conjI)
        subgoal using g(3) unfolding 8(3,4) by auto
        subgoal
          apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2,
              rule disjI2, rule disjI1)
          apply (rule exI[of _ n'], rule exI[of _ "permute_term g M"],
              rule exI[of _ "permute_term g M'"], rule exI[of _ "g f"], rule exI[of _ "g x"])
          using 8(2,3,4) eqM eqM' Rg by auto
        done
    next
      case (9 n' M M' N N' xy)
      have b1: "|dset xy| <o |UNIV::'a set|"
        by (rule finite_ordLess_infinite2[OF finite_dset infinite_UNIV])
      have b2: "|dset xy \<union> FVars N \<union> FVars N' \<union> FVars M \<union> FVars M'| <o |UNIV::'a set|"
        by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) (simp add: finite_dset)
      obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
          "g ` dset xy \<inter> (dset xy \<union> FVars N \<union> FVars N' \<union> FVars M \<union> FVars M') = {}"
          "id_on ((FVars N \<union> FVars N') - dset xy) g" "g \<circ> g = id"
        using eextend_fresh[OF b1 b2 infinite_UNIV, of "(FVars N \<union> FVars N') - dset xy"]
        by (auto simp: insert_commute)
      have idN: "id_on (FVars N - dset xy) g" and idN': "id_on (FVars N' - dset xy) g"
        using g(4) by (auto simp: id_on_def)
      have eqN: "term.Let xy M N = term.Let (dmap g xy) M (permute_term g N)"
        using g(1,2) idN by (auto intro!: exI[of _ g])
      have eqN': "term.Let xy M' N' = term.Let (dmap g xy) M' (permute_term g N')"
        using g(1,2) idN' by (auto intro!: exI[of _ g])
      have Rg: "R n' (permute_term g N) (permute_term g N')"
        using prems(2)[OF g(1,2) 9(6)] by simp
      show ?case
        apply (rule exI[of _ "dset (dmap g xy)"])
        apply (rule conjI)
        subgoal using g(3) unfolding 9(3,4) by (auto simp: dpair.set_map[OF g(1,2)])
        subgoal
          apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2,
              rule disjI2, rule disjI2, rule disjI1)
          apply (rule exI[of _ n'], rule exI[of _ M], rule exI[of _ M'],
              rule exI[of _ "permute_term g N"], rule exI[of _ "permute_term g N'"],
              rule exI[of _ "dmap g xy"])
          using 9(2,3,4,5) eqN eqN' Rg by auto
        done
    next
      case (10 M f x n' k)
      have b1: "|{f, x}| <o |UNIV::'a set|"
        by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
      have b2: "|{f, x} \<union> FVars M| <o |UNIV::'a set|"
        by (rule finite_ordLess_infinite2[OF _ infinite_UNIV]) simp
      obtain g where g: "bij g" "|supp g| <o |UNIV::'a set|"
          "g ` {f, x} \<inter> ({f, x} \<union> FVars M) = {}"
          "id_on (FVars M - {x, f}) g" "g \<circ> g = id"
        using eextend_fresh[OF b1 b2 infinite_UNIV, of "FVars M - {x, f}"]
        by (auto simp: insert_commute)
      have eqM: "Fix f x M = Fix (g f) (g x) (permute_term g M)"
        using g(1,2,4) by (auto intro!: exI[of _ g])
      have eqF: "fixapp k f x M = fixapp k (g f) (g x) (permute_term g M)"
        by (rule fixapp_cong[OF eqM])
      have sub: "FVars (permute_term g M) \<subseteq> {g f, g x}"
        using 10(5) by (auto simp: term.FVars_permute[OF g(1,2)])
      have neq: "g f \<noteq> g x"
        using 10(6) g(1) by (simp add: bij_implies_inject)
      have fvP: "FVars P = {}" and fvQ: "FVars Q = {}"
        using 10(3,4,5) FVars_fixapp[of k f x M] by auto
      show ?case
        apply (rule exI[of _ "{g f, g x}"])
        apply (rule conjI)
        subgoal unfolding fvP fvQ by auto
        subgoal
          apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2,
              rule disjI2, rule disjI2, rule disjI2)
          apply (rule exI[of _ "permute_term g M"], rule exI[of _ "g f"], rule exI[of _ "g x"],
              rule exI[of _ n'], rule exI[of _ k])
          using 10(2,3,4,7) eqM eqF sub neq by auto
        done
    qed
  qed
  done

thm apx.strong_induct apx.equiv apx.cases

lemma apx_refl: "apx n M M"
  by (induction M) (auto intro: apx.intros)

lemma apx_mono:
  assumes "apx n M M'" and "m \<le> n"
  shows "apx m M M'"
  using assms by (induction n M M' arbitrary: m rule: apx.induct) (auto intro: apx.intros)

lemma apx_FVars: "apx n M M' \<Longrightarrow> FVars M' = FVars M"
  by (induction rule: apx.induct) (auto dest: subsetD[OF FVars_fixapp])

lemma not_num_Lam: "\<not> num (Lam x M)"
  unfolding Lam_def by (auto elim: num.cases)

lemma not_num_fixapp: "\<not> num (fixapp k f x M)"
  by (cases k) (auto simp: not_num_Lam)

lemma apx_num: "apx n M M' \<Longrightarrow> num M \<longleftrightarrow> num M'"
proof (induction rule: apx.induct)
  case (apx_Succ n M M')
  then show ?case by (auto elim: num.cases intro: num.intros)
qed (auto elim: num.cases simp: not_num_fixapp)

lemma apx_val: "apx n M M' \<Longrightarrow> val M \<longleftrightarrow> val M'"
proof (induction rule: apx.induct)
  case (apx_Succ n M M')
  then show ?case
    using apx_num[OF apx.apx_Succ[OF apx_Succ(1)]]
    by (auto dest!: val_Succ_num intro: val.intros num.intros elim: num.cases)
next
  case (apx_Pair n M M' N N')
  then show ?case by (auto dest!: val_Pair_D intro: val.intros)
qed (auto intro: val.intros simp: val_fixapp elim: val.cases num.cases)

subsubsection \<open>Inversion lemmas for @{const apx}\<close>

lemma apx_Zero_inv: "apx n Zero Q \<Longrightarrow> Q = Zero"
  by (erule apx.cases) auto

lemma apx_Var_inv: "apx n (Var v) Q \<Longrightarrow> Q = Var v"
  by (erule apx.cases) auto

lemma apx_Succ_inv: "apx n (Succ M) Q \<Longrightarrow> \<exists>M'. Q = Succ M' \<and> apx n M M'"
  by (erule apx.cases) auto

lemma apx_Pred_inv: "apx n (Pred M) Q \<Longrightarrow> \<exists>M'. Q = Pred M' \<and> apx n M M'"
  by (erule apx.cases) auto

lemma apx_If_inv:
  "apx n (If M N P) Q \<Longrightarrow> \<exists>M' N' P'. Q = If M' N' P' \<and> apx n M M' \<and> apx n N N' \<and> apx n P P'"
  by (erule apx.cases) auto

lemma apx_App_inv: "apx n (App M N) Q \<Longrightarrow> \<exists>M' N'. Q = App M' N' \<and> apx n M M' \<and> apx n N N'"
  by (erule apx.cases) auto

lemma apx_Pair_inv:
  "apx n (term.Pair M N) Q \<Longrightarrow> \<exists>M' N'. Q = term.Pair M' N' \<and> apx n M M' \<and> apx n N N'"
  by (erule apx.cases) auto

text \<open>The two binding constructors admit inversion with the \<^emph>\<open>given\<close> binder on the congruence
  side: the derivation may use an alpha-variant representation, but equivariance of @{const apx}
  lets us transport the body relation back along the alpha-witness.\<close>

lemma apx_Fix_inv:
  fixes M :: "'a::var term"
  assumes "apx n (Fix f x M) Q"
  shows "(\<exists>M'. Q = Fix f x M' \<and> apx n M M') \<or>
         (\<exists>g y R k. Fix f x M = Fix g y R \<and> FVars R \<subseteq> {g, y} \<and> g \<noteq> y \<and> n \<le> k \<and>
            Q = fixapp k g y R)"
  using assms
proof (cases rule: apx.cases)
  case (apx_Fix M0 M0' f0 x0)
  note Feq = apx_Fix(1) and Qeq = apx_Fix(2) and rel = apx_Fix(3)
  obtain \<sigma> where \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" "id_on (FVars M - {x, f}) \<sigma>"
    "\<sigma> f = f0" "\<sigma> x = x0" "permute_term \<sigma> M = M0"
    using Feq[unfolded term.inject(6)] by auto
  have i\<sigma>: "bij (inv \<sigma>)" "|supp (inv \<sigma>)| <o |UNIV::'a set|"
    using \<sigma>(1,2) by (auto simp: supp_inv_bound)
  define M' where "M' = permute_term (inv \<sigma>) M0'"
  have "apx n (permute_term (inv \<sigma>) M0) (permute_term (inv \<sigma>) M0')"
    by (rule apx.equiv[OF i\<sigma> rel])
  then have MM': "apx n M M'"
    unfolding M'_def \<sigma>(6)[symmetric] permute_term_inv_cancel[OF \<sigma>(1,2)] .
  have fvM': "FVars M' = FVars M"
    unfolding M'_def term.FVars_permute[OF i\<sigma>]
    unfolding apx_FVars[OF rel] \<sigma>(6)[symmetric] term.FVars_permute[OF \<sigma>(1,2)]
    by (simp add: image_inv_f_f[OF bij_is_inj[OF \<sigma>(1)]])
  have pM': "permute_term \<sigma> M' = M0'"
    unfolding M'_def
    using permute_term_inv_cancel[OF i\<sigma>, of M0'] inv_inv_eq[OF \<sigma>(1)] by simp
  have "Fix f x M' = Fix (\<sigma> f) (\<sigma> x) (permute_term \<sigma> M')"
    using \<sigma>(1,2) \<sigma>(3)[folded fvM'] by (auto intro!: exI[of _ \<sigma>])
  then have "Q = Fix f x M'"
    unfolding \<sigma>(4,5) pM' Qeq[symmetric] by (rule sym)
  then show ?thesis using MM' by blast
next
  case (apx_Ax M0 f0 x0 k)
  then show ?thesis by blast
qed auto

lemma apx_Let_inv:
  fixes M N :: "'a::var term"
  assumes "apx n (term.Let xy M N) Q"
  shows "\<exists>M' N'. Q = term.Let xy M' N' \<and> apx n M M' \<and> apx n N N'"
  using assms
proof (cases rule: apx.cases)
  case (apx_Let M0 M0' N0 N0' xy0)
  note Leq = apx_Let(1) and Qeq = apx_Let(2) and relM = apx_Let(3) and relN = apx_Let(4)
  have M0: "M0 = M"
    using Leq unfolding term.inject(8) by auto
  obtain \<sigma> where \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" "id_on (FVars N - dset xy) \<sigma>"
    "dmap \<sigma> xy = xy0" "permute_term \<sigma> N = N0"
    using Leq[unfolded term.inject(8)] by auto
  have i\<sigma>: "bij (inv \<sigma>)" "|supp (inv \<sigma>)| <o |UNIV::'a set|"
    using \<sigma>(1,2) by (auto simp: supp_inv_bound)
  define N' where "N' = permute_term (inv \<sigma>) N0'"
  have "apx n (permute_term (inv \<sigma>) N0) (permute_term (inv \<sigma>) N0')"
    by (rule apx.equiv[OF i\<sigma> relN])
  then have NN': "apx n N N'"
    unfolding N'_def \<sigma>(5)[symmetric] permute_term_inv_cancel[OF \<sigma>(1,2)] .
  have fvN': "FVars N' = FVars N"
    unfolding N'_def term.FVars_permute[OF i\<sigma>]
    unfolding apx_FVars[OF relN] \<sigma>(5)[symmetric] term.FVars_permute[OF \<sigma>(1,2)]
    by (simp add: image_inv_f_f[OF bij_is_inj[OF \<sigma>(1)]])
  have pN': "permute_term \<sigma> N' = N0'"
    unfolding N'_def
    using permute_term_inv_cancel[OF i\<sigma>, of N0'] inv_inv_eq[OF \<sigma>(1)] by simp
  have "term.Let xy M0' N' = term.Let (dmap \<sigma> xy) M0' (permute_term \<sigma> N')"
    using \<sigma>(1,2) \<sigma>(3)[folded fvN'] by (auto intro!: exI[of _ \<sigma>])
  then have "Q = term.Let xy M0' N'"
    unfolding \<sigma>(4) pN' Qeq[symmetric] by (rule sym)
  then show ?thesis using relM NN' M0 by blast
qed auto

subsubsection \<open>Substitution of closed approximated values\<close>

lemma apx_usubst:
  fixes V V' :: "'a::var term"
  shows "apx n B B' \<Longrightarrow> apx n V V' \<Longrightarrow> FVars V = {} \<Longrightarrow> apx n (B[V <- y]) (B'[V' <- y])"
proof (binder_induction n B B' avoiding: y V V' rule: apx.strong_induct)
  case (apx_Ax M f x n k)
  have fF: "y \<notin> FVars (Fix f x M)" and fA: "y \<notin> FVars (fixapp k f x M)"
    using apx_Ax FVars_fixapp[of k f x M] by auto
  show ?case
    unfolding subst_idle[OF fF] subst_idle[OF fA]
    using apx_Ax by (blast intro: apx.apx_Ax)
qed (auto simp: subst_idle usubst_Let intro!: apx.intros)

lemma apx_S: "apx (Suc n) M M' \<Longrightarrow> apx n M M'"
  by (erule apx_mono) simp

lemma is_Fix_Fix[simp]: "is_Fix (Fix f x M)"
  unfolding is_Fix_def by blast

lemma is_Fix_neg[simp]:
  "\<not> is_Fix Zero" "\<not> is_Fix (Var v)" "\<not> is_Fix (Succ M)" "\<not> is_Fix (Pred M)"
  "\<not> is_Fix (If M N P)" "\<not> is_Fix (App M N)" "\<not> is_Fix (term.Pair M N)"
  "\<not> is_Fix (term.Let xy M N)"
  unfolding is_Fix_def by auto

lemma is_Pair_Pair[simp]: "is_Pair (term.Pair M N)"
  unfolding is_Pair_def by blast

lemma is_Pair_neg[simp]:
  "\<not> is_Pair Zero" "\<not> is_Pair (Var v)" "\<not> is_Pair (Succ M)" "\<not> is_Pair (Pred M)"
  "\<not> is_Pair (If M N P)" "\<not> is_Pair (App M N)" "\<not> is_Pair (Fix f x M)"
  "\<not> is_Pair (term.Let xy M N)"
  unfolding is_Pair_def by auto

lemma is_Fix_fixapp[simp]: "is_Fix (fixapp k f x M)"
  by (cases k) (auto simp: Lam_def)

lemma not_is_Pair_fixapp[simp]: "\<not> is_Pair (fixapp k f x M)"
  by (cases k) (auto simp: Lam_def)

lemma apx_is_Fix: "apx n A A' \<Longrightarrow> is_Fix A' \<longleftrightarrow> is_Fix A"
  by (erule apx.cases) auto

lemma apx_is_Pair: "apx n A A' \<Longrightarrow> is_Pair A' \<longleftrightarrow> is_Pair A"
  by (erule apx.cases) auto

text \<open>Unfolding a fixpoint value is independent of its representation (an instance of the
  determinism of the reduction relation).\<close>
lemma Fix_unfold_cong:
  fixes V :: "'a::var term"
  assumes eq: "Fix f x M = Fix g y R" and v: "val V" and fV: "f \<notin> FVars V" and gV: "g \<notin> FVars V"
  shows "M[V <- x][Fix f x M <- f] = R[V <- y][Fix g y R <- g]"
proof -
  have s1: "App (Fix f x M) V \<rightarrow> M[V <- x][Fix f x M <- f]" by (rule beta.FixBeta[OF v fV])
  have s2: "App (Fix f x M) V \<rightarrow> R[V <- y][Fix g y R <- g]"
    unfolding eq by (rule beta.FixBeta[OF v gV])
  show ?thesis by (rule beta_deterministic[OF s1 s2])
qed

subsubsection \<open>Approximation preserves stuckness and normality\<close>

lemma apx_stuck:
  fixes A A' :: "'a::var term"
  shows "apx n A A' \<Longrightarrow> stuck A \<Longrightarrow> stuck A'"
proof (binder_induction n A A' avoiding: divt rule: apx.strong_induct)
  case apx_Zero then show ?case using not_stuck_Zero by blast
next
  case (apx_Var v) then show ?case using not_stuck_Var by blast
next
  case (apx_Fix n M M' f x) then show ?case using not_stuck_Fix by blast
next
  case (apx_Ax M f x n k) then show ?case using not_stuck_Fix by blast
next
  case (apx_Succ n M M')
  from stuck_Succ[OF \<open>stuck (Succ M)\<close>] show ?case
  proof (elim disjE conjE)
    assume "val M" and "\<not> num M"
    then have "stuckEx (Succ M')"
      using apx_val[OF \<open>apx n M M'\<close>] apx_num[OF \<open>apx n M M'\<close>]
      by (auto intro: stuckEx.intros(1))
    then show ?thesis by (rule stuckEx_imp_stuck)
  next
    assume "stuck M"
    then have sM': "stuck M'" by (rule apx_Succ.IH)
    obtain h where h: "h \<notin> FVars M'" by (meson arb_element finite_FVars)
    have ctx: "eval_ctx h (Succ (Var h))" by (rule eval_ctx.intros(4)[OF eval_ctx.intros(1)])
    show ?thesis using stuck_ctx[OF ctx sM' h] by simp
  qed
next
  case (apx_Pred n M M')
  from stuck_Pred[OF \<open>stuck (Pred M)\<close>] show ?case
  proof (elim disjE conjE)
    assume "val M" and "\<not> num M"
    then have "stuckEx (Pred M')"
      using apx_val[OF \<open>apx n M M'\<close>] apx_num[OF \<open>apx n M M'\<close>]
      by (auto intro: stuckEx.intros(5))
    then show ?thesis by (rule stuckEx_imp_stuck)
  next
    assume "stuck M"
    then have sM': "stuck M'" by (rule apx_Pred.IH)
    obtain h where h: "h \<notin> FVars M'" by (meson arb_element finite_FVars)
    have ctx: "eval_ctx h (Pred (Var h))" by (rule eval_ctx.intros(5)[OF eval_ctx.intros(1)])
    show ?thesis using stuck_ctx[OF ctx sM' h] by simp
  qed
next
  case (apx_If n M M' N N' P P')
  from stuck_If[OF \<open>stuck (If M N P)\<close>] show ?case
  proof (elim disjE conjE)
    assume "val M" and "\<not> num M"
    then have "stuckEx (If M' N' P')"
      using apx_val[OF \<open>apx n M M'\<close>] apx_num[OF \<open>apx n M M'\<close>]
      by (auto intro: stuckEx.intros(2))
    then show ?thesis by (rule stuckEx_imp_stuck)
  next
    assume "stuck M"
    then have sM': "stuck M'" by (rule apx_If.IH(1))
    obtain h where h: "h \<notin> FVars M' \<union> FVars N' \<union> FVars P'"
      by (meson arb_element finite_FVars finite_UnI)
    have ctx: "eval_ctx h (If (Var h) N' P')"
      by (rule eval_ctx.intros(9)[OF eval_ctx.intros(1)]) (use h in auto)
    have "stuck ((If (Var h) N' P')[M' <- h])"
      by (rule stuck_ctx[OF ctx sM']) (use h in auto)
    then show ?thesis using h by (auto simp: subst_idle)
  qed
next
  case (apx_App n M M' N N')
  from stuck_App[OF \<open>stuck (App M N)\<close>] show ?case
  proof (elim disjE conjE)
    assume "val M" and "\<not> is_Fix M"
    then have "stuckEx (App M' N')"
      using apx_val[OF \<open>apx n M M'\<close>] apx_is_Fix[OF \<open>apx n M M'\<close>]
      by (auto intro: stuckEx.intros(3))
    then show ?thesis by (rule stuckEx_imp_stuck)
  next
    assume "stuck M"
    then have sM': "stuck M'" by (rule apx_App.IH(1))
    obtain h where h: "h \<notin> FVars M' \<union> FVars N'"
      by (meson arb_element finite_FVars finite_UnI)
    have ctx: "eval_ctx h (App (Var h) N')"
      by (rule eval_ctx.intros(3)[OF eval_ctx.intros(1)]) (use h in auto)
    have "stuck ((App (Var h) N')[M' <- h])"
      by (rule stuck_ctx[OF ctx sM']) (use h in auto)
    then show ?thesis using h by (auto simp: subst_idle)
  next
    assume "is_Fix M" and "stuck N"
    then have "is_Fix M'" using apx_is_Fix[OF \<open>apx n M M'\<close>] by simp
    then obtain g y B where M'e: "M' = Fix g y B" unfolding is_Fix_def by blast
    have sN': "stuck N'" by (rule apx_App.IH(2)[OF \<open>stuck N\<close>])
    obtain h where h: "h \<notin> FVars B \<union> FVars N'"
      by (meson arb_element finite_FVars finite_UnI)
    have ctx: "eval_ctx h (App (Fix g y B) (Var h))"
      by (rule eval_ctx.intros(2)[OF eval_ctx.intros(1)]) (use h in auto)
    have "stuck ((App (Fix g y B) (Var h))[N' <- h])"
      by (rule stuck_ctx[OF ctx sN']) (use h in auto)
    moreover have "(App (Fix g y B) (Var h))[N' <- h] = App (Fix g y B) N'"
      using h by (auto simp: subst_idle)
    ultimately show ?thesis unfolding M'e by simp
  qed
next
  case (apx_Pair n M M' N N')
  from stuck_Pair[OF \<open>stuck (term.Pair M N)\<close>] show ?case
  proof (elim disjE conjE)
    assume "stuck M"
    then have sM': "stuck M'" by (rule apx_Pair.IH(1))
    obtain h where h: "h \<notin> FVars M' \<union> FVars N'"
      by (meson arb_element finite_FVars finite_UnI)
    have ctx: "eval_ctx h (term.Pair (Var h) N')"
      by (rule eval_ctx.intros(6)[OF eval_ctx.intros(1)]) (use h in auto)
    have "stuck ((term.Pair (Var h) N')[M' <- h])"
      by (rule stuck_ctx[OF ctx sM']) (use h in auto)
    then show ?thesis using h by (auto simp: subst_idle)
  next
    assume "val M" and "stuck N"
    then have vM': "val M'" using apx_val[OF \<open>apx n M M'\<close>] by simp
    have sN': "stuck N'" by (rule apx_Pair.IH(2)[OF \<open>stuck N\<close>])
    obtain h where h: "h \<notin> FVars M' \<union> FVars N'"
      by (meson arb_element finite_FVars finite_UnI)
    have ctx: "eval_ctx h (term.Pair M' (Var h))"
      by (rule eval_ctx.intros(7)[OF vM' eval_ctx.intros(1)]) (use h in auto)
    have "stuck ((term.Pair M' (Var h))[N' <- h])"
      by (rule stuck_ctx[OF ctx sN']) (use h in auto)
    then show ?thesis using h by (auto simp: subst_idle)
  qed
next
  case (apx_Let n M M' N N' xy)
  from stuck_Let[OF \<open>stuck (term.Let xy M N)\<close>] show ?case
  proof (elim disjE conjE)
    assume "val M" and "\<not> is_Pair M"
    then have "stuckEx (term.Let xy M' N')"
      using apx_val[OF \<open>apx n M M'\<close>] apx_is_Pair[OF \<open>apx n M M'\<close>]
      by (auto intro: stuckEx.intros(4))
    then show ?thesis by (rule stuckEx_imp_stuck)
  next
    assume "stuck M"
    then have sM': "stuck M'" using apx_Let by blast
    obtain xy' N'' where eq: "term.Let xy M' N' = term.Let xy' M' N''"
      and d: "dset xy' \<inter> FVars M' = {}"
      using Let_refresh[of "FVars M'" xy M' N'] finite_FVars by blast
    obtain h where h: "h \<notin> FVars M' \<union> FVars N'' \<union> dset xy'"
      by (meson arb_element finite_FVars finite_dset finite_UnI)
    have ctx: "eval_ctx h (term.Let xy' (Var h) N'')"
      by (rule eval_ctx.intros(8)[OF eval_ctx.intros(1)]) (use h in auto)
    have st: "stuck ((term.Let xy' (Var h) N'')[M' <- h])"
      by (rule stuck_ctx[OF ctx sM']) (use h in auto)
    have peq: "(term.Let xy' (Var h) N'')[M' <- h] = term.Let xy' M' N''"
      using usubst_Let[of h xy' M' "Var h" N''] h d by (auto simp: subst_idle)
    show ?thesis unfolding eq using st[unfolded peq] .
  qed
qed

lemma apx_normal:
  fixes A A' :: "'a::var term"
  assumes "apx n A A'" and "normal A"
  shows "normal A'"
  using progress[OF assms(2)] apx_val[OF assms(1)] apx_stuck[OF assms(1)]
    vals_are_normal stucks_are_normal by blast

subsubsection \<open>Forward simulation\<close>

text \<open>One step of a closed term is matched by one step of any approximation with positive
  index; the residual approximation loses at most one unfolding. This is the formal content of
  the paper's descendant-tracking in the proof of Theorem B.8.\<close>

lemma apx_step:
  fixes P P' Q :: "'a::var term"
  shows "P \<rightarrow> P' \<Longrightarrow> apx (Suc n) P Q \<Longrightarrow> FVars P = {} \<Longrightarrow> \<exists>Q'. Q \<rightarrow> Q' \<and> apx n P' Q'"
proof (induction P P' arbitrary: Q rule: beta.induct)
  case (OrdApp2 N N' f x M)
  obtain Q1 Q2 where Q: "Q = App Q1 Q2" and r1: "apx (Suc n) (Fix f x M) Q1"
    and r2: "apx (Suc n) N Q2"
    using apx_App_inv[OF OrdApp2.prems(1)] by blast
  obtain Q2' where s2: "Q2 \<rightarrow> Q2'" and r2': "apx n N' Q2'"
    using OrdApp2.IH[OF r2] OrdApp2.prems(2) by auto
  have "is_Fix Q1" using apx_is_Fix[OF r1] by simp
  then obtain g y B where Q1e: "Q1 = Fix g y B" unfolding is_Fix_def by blast
  have "App (Fix g y B) Q2 \<rightarrow> App (Fix g y B) Q2'" by (rule beta.OrdApp2[OF s2])
  moreover have "apx n (App (Fix f x M) N') (App Q1 Q2')"
    by (intro apx.apx_App apx_S[OF r1] r2')
  ultimately show ?case unfolding Q Q1e by blast
next
  case (OrdApp1 M M' N)
  obtain Q1 Q2 where Q: "Q = App Q1 Q2" and r1: "apx (Suc n) M Q1" and r2: "apx (Suc n) N Q2"
    using apx_App_inv[OF OrdApp1.prems(1)] by blast
  obtain Q1' where s1: "Q1 \<rightarrow> Q1'" and r1': "apx n M' Q1'"
    using OrdApp1.IH[OF r1] OrdApp1.prems(2) by auto
  show ?case unfolding Q
    using beta.OrdApp1[OF s1] apx.apx_App[OF r1' apx_S[OF r2]] by blast
next
  case (OrdSucc M M')
  obtain Q1 where Q: "Q = Succ Q1" and r1: "apx (Suc n) M Q1"
    using apx_Succ_inv[OF OrdSucc.prems(1)] by blast
  obtain Q1' where s1: "Q1 \<rightarrow> Q1'" and r1': "apx n M' Q1'"
    using OrdSucc.IH[OF r1] OrdSucc.prems(2) by auto
  show ?case unfolding Q using beta.OrdSucc[OF s1] apx.apx_Succ[OF r1'] by blast
next
  case (OrdPred M M')
  obtain Q1 where Q: "Q = Pred Q1" and r1: "apx (Suc n) M Q1"
    using apx_Pred_inv[OF OrdPred.prems(1)] by blast
  obtain Q1' where s1: "Q1 \<rightarrow> Q1'" and r1': "apx n M' Q1'"
    using OrdPred.IH[OF r1] OrdPred.prems(2) by auto
  show ?case unfolding Q using beta.OrdPred[OF s1] apx.apx_Pred[OF r1'] by blast
next
  case (OrdPair1 M M' N)
  obtain Q1 Q2 where Q: "Q = term.Pair Q1 Q2" and r1: "apx (Suc n) M Q1"
    and r2: "apx (Suc n) N Q2"
    using apx_Pair_inv[OF OrdPair1.prems(1)] by blast
  obtain Q1' where s1: "Q1 \<rightarrow> Q1'" and r1': "apx n M' Q1'"
    using OrdPair1.IH[OF r1] OrdPair1.prems(2) by auto
  show ?case unfolding Q
    using beta.OrdPair1[OF s1] apx.apx_Pair[OF r1' apx_S[OF r2]] by blast
next
  case (OrdPair2 V N N')
  obtain Q1 Q2 where Q: "Q = term.Pair Q1 Q2" and r1: "apx (Suc n) V Q1"
    and r2: "apx (Suc n) N Q2"
    using apx_Pair_inv[OF OrdPair2.prems(1)] by blast
  have vQ1: "val Q1" using apx_val[OF r1] OrdPair2.hyps(1) by blast
  obtain Q2' where s2: "Q2 \<rightarrow> Q2'" and r2': "apx n N' Q2'"
    using OrdPair2.IH[OF r2] OrdPair2.prems(2) by auto
  show ?case unfolding Q
    using beta.OrdPair2[OF vQ1 s2] apx.apx_Pair[OF apx_S[OF r1] r2'] by blast
next
  case (OrdLet M M' xy N)
  obtain Q1 Q2 where Q: "Q = term.Let xy Q1 Q2" and r1: "apx (Suc n) M Q1"
    and r2: "apx (Suc n) N Q2"
    using apx_Let_inv[OF OrdLet.prems(1)] by blast
  obtain Q1' where s1: "Q1 \<rightarrow> Q1'" and r1': "apx n M' Q1'"
    using OrdLet.IH[OF r1] OrdLet.prems(2) by auto
  show ?case unfolding Q
    using beta.OrdLet[OF s1] apx.apx_Let[OF r1' apx_S[OF r2]] by blast
next
  case (OrdIf M M' N P)
  obtain Q1 Q2 Q3 where Q: "Q = If Q1 Q2 Q3" and r1: "apx (Suc n) M Q1"
    and r2: "apx (Suc n) N Q2" and r3: "apx (Suc n) P Q3"
    using apx_If_inv[OF OrdIf.prems(1)] by blast
  obtain Q1' where s1: "Q1 \<rightarrow> Q1'" and r1': "apx n M' Q1'"
    using OrdIf.IH[OF r1] OrdIf.prems(2) by auto
  show ?case unfolding Q
    using beta.OrdIf[OF s1] apx.apx_If[OF r1' apx_S[OF r2] apx_S[OF r3]] by blast
next
  case (Ifz N P)
  obtain Q1 Q2 Q3 where Q: "Q = If Q1 Q2 Q3" and r1: "apx (Suc n) Zero Q1"
    and r2: "apx (Suc n) N Q2" and r3: "apx (Suc n) P Q3"
    using apx_If_inv[OF Ifz.prems(1)] by blast
  have Q1e: "Q1 = Zero" using apx_Zero_inv[OF r1] .
  show ?case unfolding Q Q1e using beta.Ifz apx_S[OF r2] by blast
next
  case (Ifs v N P)
  obtain Q1 Q2 Q3 where Q: "Q = If Q1 Q2 Q3" and r1: "apx (Suc n) (Succ v) Q1"
    and r2: "apx (Suc n) N Q2" and r3: "apx (Suc n) P Q3"
    using apx_If_inv[OF Ifs.prems(1)] by blast
  obtain v2 where Q1e: "Q1 = Succ v2" and rv: "apx (Suc n) v v2"
    using apx_Succ_inv[OF r1] by blast
  have nv2: "num v2" using apx_num[OF rv] Ifs.hyps by blast
  show ?case unfolding Q Q1e using beta.Ifs[OF nv2] apx_S[OF r3] by blast
next
  case (Let V W xy M)
  obtain Q1 Q2 where Q: "Q = term.Let xy Q1 Q2" and r1: "apx (Suc n) (term.Pair V W) Q1"
    and r2: "apx (Suc n) M Q2"
    using apx_Let_inv[OF Let.prems(1)] by blast
  obtain V2 W2 where Q1e: "Q1 = term.Pair V2 W2" and rV: "apx (Suc n) V V2"
    and rW: "apx (Suc n) W W2"
    using apx_Pair_inv[OF r1] by blast
  have vV2: "val V2" and vW2: "val W2"
    using apx_val[OF rV] apx_val[OF rW] Let.hyps(1,2) by blast+
  have clV: "FVars V = {}" and clW: "FVars W = {}" using Let.prems(2) by auto
  have fvV2: "dset xy \<inter> FVars V2 = {}" using apx_FVars[OF rV] clV by simp
  have step: "term.Let xy (term.Pair V2 W2) Q2 \<rightarrow> Q2[V2 <- dfst xy][W2 <- dsnd xy]"
    by (rule beta.Let[OF vV2 vW2 fvV2])
  have rel: "apx n (M[V <- dfst xy][W <- dsnd xy]) (Q2[V2 <- dfst xy][W2 <- dsnd xy])"
    by (rule apx_usubst[OF apx_usubst[OF apx_S[OF r2] apx_S[OF rV] clV] apx_S[OF rW] clW])
  show ?case unfolding Q Q1e using step rel by blast
next
  case (PredZ)
  obtain Q1 where Q: "Q = Pred Q1" and r1: "apx (Suc n) Zero Q1"
    using apx_Pred_inv[OF PredZ.prems(1)] by blast
  have Q1e: "Q1 = Zero" using apx_Zero_inv[OF r1] .
  show ?case unfolding Q Q1e using beta.PredZ apx.apx_Zero by blast
next
  case (PredS v)
  obtain Q1 where Q: "Q = Pred Q1" and r1: "apx (Suc n) (Succ v) Q1"
    using apx_Pred_inv[OF PredS.prems(1)] by blast
  obtain v2 where Q1e: "Q1 = Succ v2" and rv: "apx (Suc n) v v2"
    using apx_Succ_inv[OF r1] by blast
  have nv2: "num v2" using apx_num[OF rv] PredS.hyps by blast
  show ?case unfolding Q Q1e using beta.PredS[OF nv2] apx_S[OF rv] by blast
next
  case (FixBeta V f x M)
  have clF: "FVars (Fix f x M) = {}" and clV: "FVars V = {}" using FixBeta.prems(2) by auto
  obtain Q1 Q2 where Q: "Q = App Q1 Q2" and r1: "apx (Suc n) (Fix f x M) Q1"
    and r2: "apx (Suc n) V Q2"
    using apx_App_inv[OF FixBeta.prems(1)] by blast
  have vQ2: "val Q2" using apx_val[OF r2] FixBeta.hyps(1) by blast
  have clQ2: "FVars Q2 = {}" using apx_FVars[OF r2] clV by simp
  from apx_Fix_inv[OF r1] show ?case
  proof (elim disjE exE conjE)
    fix M1' assume Q1e: "Q1 = Fix f x M1'" and relM: "apx (Suc n) M M1'"
    have step: "App (Fix f x M1') Q2 \<rightarrow> M1'[Q2 <- x][Fix f x M1' <- f]"
      by (rule beta.FixBeta[OF vQ2]) (use clQ2 in simp)
    have rel: "apx n (M[V <- x][Fix f x M <- f]) (M1'[Q2 <- x][Fix f x M1' <- f])"
      by (rule apx_usubst[OF apx_usubst[OF apx_S[OF relM] apx_S[OF r2] clV]
            apx.apx_Fix[OF apx_S[OF relM]] clF])
    show ?thesis unfolding Q Q1e using step rel by blast
  next
    fix g y R k
    assume eqF: "Fix f x M = Fix g y R" and fvR: "FVars R \<subseteq> {g, y}" and gy: "g \<noteq> y"
      and nk: "Suc n \<le> k" and Q1e: "Q1 = fixapp k g y R"
    obtain k' where ke: "k = Suc k'" and k'n: "n \<le> k'" using nk by (cases k) auto
    have gQ2: "g \<notin> FVars Q2" using clQ2 by simp
    have step: "App (fixapp (Suc k') g y R) Q2 \<rightarrow> R[Q2 <- y][fixapp k' g y R <- g]"
      by (rule fixapp_beta[OF vQ2 gy gQ2])
    have clFg: "FVars (Fix g y R) = {}" using fvR by auto
    have unf: "M[V <- x][Fix f x M <- f] = R[V <- y][Fix g y R <- g]"
      by (rule Fix_unfold_cong[OF eqF FixBeta.hyps(1) FixBeta.hyps(2)]) (use clV in simp)
    have rel: "apx n (R[V <- y][Fix g y R <- g]) (R[Q2 <- y][fixapp k' g y R <- g])"
      by (rule apx_usubst[OF apx_usubst[OF apx_refl apx_S[OF r2] clV]
            apx.apx_Ax[OF fvR gy k'n] clFg])
    show ?thesis unfolding Q Q1e ke unf using step rel by blast
  qed
qed

lemma apx_steps:
  fixes P P'' Q :: "'a::var term"
  shows "P \<rightarrow>[k] P'' \<Longrightarrow> apx (n + k) P Q \<Longrightarrow> FVars P = {} \<Longrightarrow>
    \<exists>Q''. Q \<rightarrow>[k] Q'' \<and> apx n P'' Q''"
proof (induction P k P'' arbitrary: Q rule: betas.induct)
  case (refl M)
  then show ?case by (auto intro: betas.refl)
next
  case (step M N k P'')
  have "apx (Suc (n + k)) M Q" using step.prems(1) by simp
  then obtain Q' where s1: "Q \<rightarrow> Q'" and r1: "apx (n + k) N Q'"
    using apx_step[OF step.hyps(1) _ step.prems(2)] by blast
  have clN: "FVars N = {}" using FVars_beta[OF step.hyps(1)] step.prems(2) by auto
  obtain Q'' where "Q' \<rightarrow>[k] Q''" "apx n P'' Q''" using step.IH[OF r1 clN] by blast
  then show ?case using s1 by (blast intro: betas.step)
qed

section \<open>Theorem B.8: fixpoint approximants decide non-membership\<close>

lemma val_not_diverge: "val V \<Longrightarrow> \<not> (V \<Up>)"
  using vals_are_normal unfolding normal_def by (metis diverge.cases)

lemma val_in_taubot: "val V \<Longrightarrow> V \<in> \<lblot>A\<rblot> \<Longrightarrow> V \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  using val_tau_iff by auto

lemma not_val_taubot: "val V \<Longrightarrow> V \<notin> \<lblot>A\<rblot> \<Longrightarrow> V \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  using val_tau_iff val_not_diverge by auto

lemma Prod_is_Pair: "X \<in> \<lblot>Prod A B\<rblot> \<Longrightarrow> is_Pair X"
  by (auto simp: is_Pair_def)

lemma To_is_Fix: "X \<in> \<lblot>To A B\<rblot> \<Longrightarrow> is_Fix X"
  by (auto simp: is_Fix_def)

lemma OnlyTo_is_Fix: "X \<in> \<lblot>OnlyTo A B\<rblot> \<Longrightarrow> is_Fix X"
  by (auto simp: is_Fix_def)

text \<open>Fixpoint-approximant analogues of @{thm To_unfold} and @{thm OnlyTo_unfold}: the
  approximant unfolds to the body with the next-lower approximant substituted for the
  recursion variable, independently of the representation used for the membership.\<close>

lemma To_unfold_fixapp:
  fixes U :: "'a::var term"
  assumes iW: "fixapp (Suc j) g y R \<in> \<lblot>To A B\<rblot>" and vU: "val U" and clU: "FVars U = {}"
    and iU: "U \<in> \<lblot>A\<rblot>" and gy: "g \<noteq> y"
  shows "R[U <- y][fixapp j g y R <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
proof -
  from iW obtain f' x' M0' where W': "fixapp (Suc j) g y R = Fix f' x' M0'"
    and prop': "\<forall>U'\<in>Vals0. FVars U' = {} \<longrightarrow> U' \<in> \<lblot>A\<rblot> \<longrightarrow>
      M0'[U' <- x'][Fix f' x' M0' <- f'] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
    unfolding type_semantics.simps by blast
  have m: "M0'[U <- x'][fixapp (Suc j) g y R <- f'] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
    using prop' vU clU iU W' unfolding Vals0_def by auto
  have f'U: "f' \<notin> FVars U" and gU: "g \<notin> FVars U" using clU by auto
  have "App (fixapp (Suc j) g y R) U \<rightarrow> M0'[U <- x'][fixapp (Suc j) g y R <- f']"
    using beta.FixBeta[OF vU f'U, of x' M0'] W' by simp
  moreover have "App (fixapp (Suc j) g y R) U \<rightarrow> R[U <- y][fixapp j g y R <- g]"
    by (rule fixapp_beta[OF vU gy gU])
  ultimately have "R[U <- y][fixapp j g y R <- g] = M0'[U <- x'][fixapp (Suc j) g y R <- f']"
    using beta_deterministic by blast
  then show ?thesis using m by simp
qed

lemma OnlyTo_unfold_fixapp:
  fixes U :: "'a::var term"
  assumes iW: "fixapp (Suc j) g y R \<in> \<lblot>OnlyTo A B\<rblot>" and vU: "val U" and clU: "FVars U = {}"
    and gy: "g \<noteq> y" and mem: "R[U <- y][fixapp j g y R <- g] \<in> \<T>\<lblot>B\<rblot>"
  shows "U \<in> \<lblot>A\<rblot>"
proof -
  from iW obtain f' x' M0' where W': "fixapp (Suc j) g y R = Fix f' x' M0'"
    and prop': "\<forall>U'\<in>Vals0. FVars U' = {} \<longrightarrow>
      M0'[U' <- x'][Fix f' x' M0' <- f'] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> U' \<in> \<lblot>A\<rblot>"
    unfolding type_semantics.simps by blast
  have f'U: "f' \<notin> FVars U" and gU: "g \<notin> FVars U" using clU by auto
  have "App (fixapp (Suc j) g y R) U \<rightarrow> M0'[U <- x'][fixapp (Suc j) g y R <- f']"
    using beta.FixBeta[OF vU f'U, of x' M0'] W' by simp
  moreover have "App (fixapp (Suc j) g y R) U \<rightarrow> R[U <- y][fixapp j g y R <- g]"
    by (rule fixapp_beta[OF vU gy gU])
  ultimately have "R[U <- y][fixapp j g y R <- g] = M0'[U <- x'][fixapp (Suc j) g y R <- f']"
    using beta_deterministic by blast
  then have "M0'[U <- x'][Fix f' x' M0' <- f'] \<in> \<T>\<lblot>B\<rblot>" using mem W' by simp
  then show ?thesis using prop' vU clU unfolding Vals0_def by auto
qed

lemma notin_taubot_of_normal_reach:
  fixes Q :: "'a::var term"
  assumes sQ: "Q \<rightarrow>[k] Qf" and nf: "normal Qf" and nv: "\<not> (val Qf \<and> Qf \<in> \<lblot>A\<rblot>)"
  shows "Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
proof -
  have norm: "normalizes Q" using sQ nf unfolding normalizes_def beta_star_def by blast
  have ndiv: "\<not> diverge Q" using norm diverge_xor_normalizes by blast
  have "Q \<notin> \<T>\<lblot>A\<rblot>"
  proof
    assume "Q \<in> \<T>\<lblot>A\<rblot>"
    then obtain W where iW: "W \<in> \<lblot>A\<rblot>" and sW: "Q \<rightarrow>* W" and vW: "val W" by auto
    have "W = Qf"
      using beta_star_normal_unique[OF sW vals_are_normal[OF vW] _ nf] sQ
      unfolding beta_star_def by blast
    then show False using nv vW iW by blast
  qed
  then show ?thesis using ndiv by simp
qed

text \<open>The two directions of Theorem B.8 share a common skeleton: run the (closed) term to its
  normal form, simulate the run on the approximant side via @{thm apx_steps}, and analyse the
  reached normal forms. The analysis of reached \<^emph>\<open>values\<close> is the only type-dependent part, so we
  factor the skeleton into two gluing lemmas parameterised by the value-level property.\<close>

lemma b8i_glue:
  fixes P :: "'a::var term"
  assumes cl: "FVars P = {}" and notin: "P \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    and vals: "\<And>V :: 'a term. val V \<Longrightarrow> FVars V = {} \<Longrightarrow> V \<notin> \<lblot>A\<rblot> \<Longrightarrow>
      \<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>A\<rblot>"
  shows "\<exists>n0. \<forall>n\<ge>n0. \<forall>Q. apx n P Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
proof -
  have ndiv: "\<not> diverge P" using notin by auto
  then have "normalizes P" using diverge_or_normalizes by blast
  then obtain k Pf where st: "P \<rightarrow>[k] Pf" and nf: "normal Pf"
    unfolding normalizes_def beta_star_def by blast
  have clPf: "FVars Pf = {}" using FVars_betas[OF st] cl by auto
  from progress[OF nf] show ?thesis
  proof
    assume sPf: "stuck Pf"
    have "\<forall>n\<ge>k. \<forall>Q. apx n P Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    proof (intro allI impI)
      fix n Q assume nk: "k \<le> n" and aQ: "apx n P Q"
      have "apx ((n - k) + k) P Q" using aQ nk by simp
      then obtain Qf where sQ: "Q \<rightarrow>[k] Qf" and aQf: "apx (n - k) Pf Qf"
        using apx_steps[OF st _ cl] by blast
      have "stuck Qf" using apx_stuck[OF aQf sPf] .
      then show "Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        using notin_taubot_of_normal_reach[OF sQ stucks_are_normal] stuck_not_val by blast
    qed
    then show ?thesis by blast
  next
    assume vPf: "val Pf"
    have "Pf \<notin> \<lblot>A\<rblot>"
    proof
      assume "Pf \<in> \<lblot>A\<rblot>"
      then have "P \<in> \<T>\<lblot>A\<rblot>"
        using st vPf unfolding tau_semantics.simps beta_star_def by blast
      then show False using notin by simp
    qed
    then obtain m0 where m0: "\<forall>m\<ge>m0. \<forall>W. apx m Pf W \<longrightarrow> W \<notin> \<lblot>A\<rblot>"
      using vals[OF vPf clPf] by blast
    have "\<forall>n\<ge>k + m0. \<forall>Q. apx n P Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    proof (intro allI impI)
      fix n Q assume nk: "k + m0 \<le> n" and aQ: "apx n P Q"
      have "apx ((n - k) + k) P Q" using aQ nk by simp
      then obtain Qf where sQ: "Q \<rightarrow>[k] Qf" and aQf: "apx (n - k) Pf Qf"
        using apx_steps[OF st _ cl] by blast
      have "m0 \<le> n - k" using nk by arith
      then have "Qf \<notin> \<lblot>A\<rblot>" using m0 aQf by blast
      moreover have "val Qf" using apx_val[OF aQf] vPf by blast
      ultimately show "Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        using notin_taubot_of_normal_reach[OF sQ vals_are_normal] by blast
    qed
    then show ?thesis by blast
  qed
qed

lemma b8ii_glue:
  fixes P :: "'a::var term"
  assumes cl: "FVars P = {}" and inT: "P \<in> \<T>\<lblot>A\<rblot>"
    and vals: "\<And>V :: 'a term. val V \<Longrightarrow> FVars V = {} \<Longrightarrow> V \<in> \<lblot>A\<rblot> \<Longrightarrow>
      \<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>A\<rblot>"
  shows "\<exists>n0. \<forall>n\<ge>n0. \<forall>Q. apx n P Q \<longrightarrow> Q \<in> \<T>\<lblot>A\<rblot>"
proof -
  from inT obtain V where iV: "V \<in> \<lblot>A\<rblot>" and sV: "P \<rightarrow>* V" and vV: "val V" by auto
  obtain k where st: "P \<rightarrow>[k] V" using sV unfolding beta_star_def by blast
  have clV: "FVars V = {}" using FVars_betas[OF st] cl by auto
  obtain m0 where m0: "\<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>A\<rblot>"
    using vals[OF vV clV iV] by blast
  have "\<forall>n\<ge>k + m0. \<forall>Q. apx n P Q \<longrightarrow> Q \<in> \<T>\<lblot>A\<rblot>"
  proof (intro allI impI)
    fix n Q assume nk: "k + m0 \<le> n" and aQ: "apx n P Q"
    have "apx ((n - k) + k) P Q" using aQ nk by simp
    then obtain W where sQ: "Q \<rightarrow>[k] W" and aW: "apx (n - k) V W"
      using apx_steps[OF st _ cl] by blast
    have "m0 \<le> n - k" using nk by arith
    then have "W \<in> \<lblot>A\<rblot>" using m0 aW by blast
    moreover have "val W" using apx_val[OF aW] vV by blast
    ultimately show "Q \<in> \<T>\<lblot>A\<rblot>"
      using sQ unfolding tau_semantics.simps beta_star_def by blast
  qed
  then show ?thesis by blast
qed

theorem b8_induction:
  fixes P :: "'a::var term"
  shows "safe A \<Longrightarrow> FVars P = {} \<Longrightarrow> P \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow>
      \<exists>n0. \<forall>n\<ge>n0. \<forall>Q. apx n P Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    and "finitely_verifiable A \<Longrightarrow> FVars P = {} \<Longrightarrow> P \<in> \<T>\<lblot>A\<rblot> \<Longrightarrow>
      \<exists>n0. \<forall>n\<ge>n0. \<forall>Q. apx n P Q \<longrightarrow> Q \<in> \<T>\<lblot>A\<rblot>"
proof (induction A arbitrary: P)
  case Nat
  {
    case 1
    show ?case
    proof (rule b8i_glue[OF 1(2,3)])
      fix V :: "'a term" assume "V \<notin> \<lblot>Nat\<rblot>"
      then have "\<forall>m\<ge>(0::nat). \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Nat\<rblot>"
        using apx_num by fastforce
      then show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Nat\<rblot>" by blast
    qed
  next
    case 2
    show ?case
    proof (rule b8ii_glue[OF 2(2,3)])
      fix V :: "'a term" assume "V \<in> \<lblot>Nat\<rblot>"
      then have "\<forall>m\<ge>(0::nat). \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>Nat\<rblot>"
        using apx_num by fastforce
      then show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>Nat\<rblot>" by blast
    qed
  }
next
  case Ok
  {
    case 1
    show ?case
    proof (rule b8i_glue[OF 1(2,3)])
      fix V :: "'a term" assume "val V" and "V \<notin> \<lblot>Ok\<rblot>"
      then show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Ok\<rblot>"
        by (simp add: Vals0_def)
    qed
  next
    case 2
    show ?case
    proof (rule b8ii_glue[OF 2(2,3)])
      fix V :: "'a term" assume "val V"
      then have "\<forall>m\<ge>(0::nat). \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>Ok\<rblot>"
        using apx_val by (fastforce simp: Vals0_def)
      then show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>Ok\<rblot>" by blast
    qed
  }
next
  case (Prod A1 A2)
  {
    case 1
    have sA1: "safe A1" and sA2: "safe A2" using safe_Prod[OF 1(1)] by auto
    show ?case
    proof (rule b8i_glue[OF 1(2,3)])
      fix V :: "'a term" assume vV: "val V" and clV: "FVars V = {}" and nin: "V \<notin> \<lblot>Prod A1 A2\<rblot>"
      show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Prod A1 A2\<rblot>"
      proof (cases "is_Pair V")
        case False
        then have "\<forall>m\<ge>(0::nat). \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Prod A1 A2\<rblot>"
          using apx_is_Pair Prod_is_Pair by blast
        then show ?thesis by blast
      next
        case True
        then obtain V1 V2 where Ve: "V = term.Pair V1 V2" unfolding is_Pair_def by blast
        have vV1: "val V1" and vV2: "val V2" using val_Pair_D[OF vV[unfolded Ve]] by auto
        have clV1: "FVars V1 = {}" and clV2: "FVars V2 = {}" using clV Ve by auto
        have "V1 \<notin> \<lblot>A1\<rblot> \<or> V2 \<notin> \<lblot>A2\<rblot>" using nin Ve by auto
        then show ?thesis
        proof
          assume n1: "V1 \<notin> \<lblot>A1\<rblot>"
          have "V1 \<notin> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>" using not_val_taubot[OF vV1 n1] .
          then obtain m1 where m1: "\<forall>m\<ge>m1. \<forall>X. apx m V1 X \<longrightarrow> X \<notin> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>"
            using Prod.IH(1)[OF sA1 clV1] by blast
          have "\<forall>m\<ge>m1. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Prod A1 A2\<rblot>"
          proof (intro allI impI)
            fix m W assume mm: "m1 \<le> m" and aW: "apx m V W"
            obtain W1 W2 where We: "W = term.Pair W1 W2" and a1: "apx m V1 W1"
              using apx_Pair_inv[OF aW[unfolded Ve]] by blast
            have "W1 \<notin> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>" using m1 mm a1 by blast
            then have "W1 \<notin> \<lblot>A1\<rblot>"
              using val_in_taubot apx_val[OF a1] vV1 by blast
            then show "W \<notin> \<lblot>Prod A1 A2\<rblot>" unfolding We by auto
          qed
          then show ?thesis by blast
        next
          assume n2: "V2 \<notin> \<lblot>A2\<rblot>"
          have "V2 \<notin> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" using not_val_taubot[OF vV2 n2] .
          then obtain m2 where m2: "\<forall>m\<ge>m2. \<forall>X. apx m V2 X \<longrightarrow> X \<notin> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
            using Prod.IH(3)[OF sA2 clV2] by blast
          have "\<forall>m\<ge>m2. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>Prod A1 A2\<rblot>"
          proof (intro allI impI)
            fix m W assume mm: "m2 \<le> m" and aW: "apx m V W"
            obtain W1 W2 where We: "W = term.Pair W1 W2" and a2: "apx m V2 W2"
              using apx_Pair_inv[OF aW[unfolded Ve]] by blast
            have "W2 \<notin> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" using m2 mm a2 by blast
            then have "W2 \<notin> \<lblot>A2\<rblot>"
              using val_in_taubot apx_val[OF a2] vV2 by blast
            then show "W \<notin> \<lblot>Prod A1 A2\<rblot>" unfolding We by auto
          qed
          then show ?thesis by blast
        qed
      qed
    qed
  next
    case 2
    have f1: "finitely_verifiable A1" and f2: "finitely_verifiable A2"
      using fv_Prod[OF 2(1)] by auto
    show ?case
    proof (rule b8ii_glue[OF 2(2,3)])
      fix V :: "'a term" assume vV: "val V" and clV: "FVars V = {}" and iV: "V \<in> \<lblot>Prod A1 A2\<rblot>"
      obtain V1 V2 where Ve: "V = term.Pair V1 V2" and i1: "V1 \<in> \<lblot>A1\<rblot>" and i2: "V2 \<in> \<lblot>A2\<rblot>"
        using iV by auto
      have vV1: "val V1" and vV2: "val V2" using val_Pair_D[OF vV[unfolded Ve]] by auto
      have clV1: "FVars V1 = {}" and clV2: "FVars V2 = {}" using clV Ve by auto
      have t1: "V1 \<in> \<T>\<lblot>A1\<rblot>" using val_tau_iff[OF vV1] i1 by simp
      have t2: "V2 \<in> \<T>\<lblot>A2\<rblot>" using val_tau_iff[OF vV2] i2 by simp
      obtain m1 where m1: "\<forall>m\<ge>m1. \<forall>X. apx m V1 X \<longrightarrow> X \<in> \<T>\<lblot>A1\<rblot>"
        using Prod.IH(2)[OF f1 clV1 t1] by blast
      obtain m2 where m2: "\<forall>m\<ge>m2. \<forall>X. apx m V2 X \<longrightarrow> X \<in> \<T>\<lblot>A2\<rblot>"
        using Prod.IH(4)[OF f2 clV2 t2] by blast
      have "\<forall>m\<ge>max m1 m2. \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>Prod A1 A2\<rblot>"
      proof (intro allI impI)
        fix m W assume mm: "max m1 m2 \<le> m" and aW: "apx m V W"
        obtain W1 W2 where We: "W = term.Pair W1 W2" and a1: "apx m V1 W1" and a2: "apx m V2 W2"
          using apx_Pair_inv[OF aW[unfolded Ve]] by blast
        have "W1 \<in> \<T>\<lblot>A1\<rblot>" using m1 mm a1 by auto
        then have j1: "W1 \<in> \<lblot>A1\<rblot>" using val_tau_iff apx_val[OF a1] vV1 by blast
        have "W2 \<in> \<T>\<lblot>A2\<rblot>" using m2 mm a2 by auto
        then have j2: "W2 \<in> \<lblot>A2\<rblot>" using val_tau_iff apx_val[OF a2] vV2 by blast
        show "W \<in> \<lblot>Prod A1 A2\<rblot>" unfolding We using j1 j2 by auto
      qed
      then show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<in> \<lblot>Prod A1 A2\<rblot>" by blast
    qed
  }
next
  case (To A1 A2)
  {
    case 1
    have sA2: "safe A2" using safe_To[OF 1(1)] by auto
    show ?case
    proof (rule b8i_glue[OF 1(2,3)])
      fix V :: "'a term" assume vV: "val V" and clV: "FVars V = {}" and nin: "V \<notin> \<lblot>To A1 A2\<rblot>"
      show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>To A1 A2\<rblot>"
      proof (cases "is_Fix V")
        case False
        then have "\<forall>m\<ge>(0::nat). \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>To A1 A2\<rblot>"
          using apx_is_Fix To_is_Fix by blast
        then show ?thesis by blast
      next
        case True
        then obtain g y R where Ve: "V = Fix g y R" unfolding is_Fix_def by blast
        have "\<not> (\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow> U \<in> \<lblot>A1\<rblot> \<longrightarrow>
          R[U <- y][Fix g y R <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>)"
        proof
          assume "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow> U \<in> \<lblot>A1\<rblot> \<longrightarrow>
            R[U <- y][Fix g y R <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
          then have "V \<in> \<lblot>To A1 A2\<rblot>" unfolding Ve type_semantics.simps by blast
          then show False using nin by simp
        qed
        then obtain U where vU: "val U" and clU: "FVars U = {}" and iU: "U \<in> \<lblot>A1\<rblot>"
          and P2nin: "R[U <- y][Fix g y R <- g] \<notin> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
          unfolding Vals0_def by blast
        have clP2: "FVars (R[U <- y][Fix g y R <- g]) = {}"
          using clV clU unfolding Ve by (auto simp: FVars_usubst split: if_splits)
        obtain m1 where m1: "\<forall>m\<ge>m1. \<forall>X. apx m (R[U <- y][Fix g y R <- g]) X \<longrightarrow> X \<notin> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
          using To.IH(3)[OF sA2 clP2 P2nin] by blast
        have "\<forall>m\<ge>Suc m1. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>To A1 A2\<rblot>"
        proof (intro allI impI)
          fix m W assume mm: "Suc m1 \<le> m" and aW: "apx m V W"
          from apx_Fix_inv[OF aW[unfolded Ve]] show "W \<notin> \<lblot>To A1 A2\<rblot>"
          proof (elim disjE exE conjE)
            fix R' assume We: "W = Fix g y R'" and aR: "apx m R R'"
            show ?thesis
            proof
              assume Win: "W \<in> \<lblot>To A1 A2\<rblot>"
              have unf: "R'[U <- y][W <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
                by (rule To_unfold[OF Win vU clU iU We])
              have rel: "apx m1 (R[U <- y][Fix g y R <- g]) (R'[U <- y][W <- g])"
                unfolding We
                by (rule apx_usubst[OF apx_usubst[OF apx_mono[OF aR] apx_refl clU]
                      apx.apx_Fix[OF apx_mono[OF aR]] clV[unfolded Ve]])
                  (use mm in auto)
              show False using m1 rel unf by auto
            qed
          next
            fix g2 y2 R2 j
            assume eqF: "Fix g y R = Fix g2 y2 R2" and fvR2: "FVars R2 \<subseteq> {g2, y2}"
              and gy2: "g2 \<noteq> y2" and mj: "m \<le> j" and We: "W = fixapp j g2 y2 R2"
            obtain j' where je: "j = Suc j'" and j'm: "m1 \<le> j'"
              using mj mm by (cases j) auto
            have clF2: "FVars (Fix g2 y2 R2) = {}" using fvR2 by auto
            have unfeq: "R[U <- y][Fix g y R <- g] = R2[U <- y2][Fix g2 y2 R2 <- g2]"
              by (rule Fix_unfold_cong[OF eqF vU]) (use clU in auto)
            show ?thesis
            proof
              assume Win: "W \<in> \<lblot>To A1 A2\<rblot>"
              have unf: "R2[U <- y2][fixapp j' g2 y2 R2 <- g2] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>"
                by (rule To_unfold_fixapp[OF Win[unfolded We je] vU clU iU gy2])
              have rel: "apx m1 (R2[U <- y2][Fix g2 y2 R2 <- g2])
                  (R2[U <- y2][fixapp j' g2 y2 R2 <- g2])"
                by (rule apx_usubst[OF apx_refl apx.apx_Ax[OF fvR2 gy2 j'm] clF2])
              show False using m1 rel unf unfolding unfeq by auto
            qed
          qed
        qed
        then show ?thesis by blast
      qed
    qed
  next
    case 2
    then show ?case using not_fv_To by blast
  }
next
  case (OnlyTo A1 A2)
  {
    case 1
    have fA2: "finitely_verifiable A2" using safe_OnlyTo[OF 1(1)] by auto
    show ?case
    proof (rule b8i_glue[OF 1(2,3)])
      fix V :: "'a term" assume vV: "val V" and clV: "FVars V = {}" and nin: "V \<notin> \<lblot>OnlyTo A1 A2\<rblot>"
      show "\<exists>m0. \<forall>m\<ge>m0. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>OnlyTo A1 A2\<rblot>"
      proof (cases "is_Fix V")
        case False
        then have "\<forall>m\<ge>(0::nat). \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>OnlyTo A1 A2\<rblot>"
          using apx_is_Fix OnlyTo_is_Fix by blast
        then show ?thesis by blast
      next
        case True
        then obtain g y R where Ve: "V = Fix g y R" unfolding is_Fix_def by blast
        have "\<not> (\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow>
          R[U <- y][Fix g y R <- g] \<in> \<T>\<lblot>A2\<rblot> \<longrightarrow> U \<in> \<lblot>A1\<rblot>)"
        proof
          assume "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow>
            R[U <- y][Fix g y R <- g] \<in> \<T>\<lblot>A2\<rblot> \<longrightarrow> U \<in> \<lblot>A1\<rblot>"
          then have "V \<in> \<lblot>OnlyTo A1 A2\<rblot>" unfolding Ve type_semantics.simps by blast
          then show False using nin by simp
        qed
        then obtain U where vU: "val U" and clU: "FVars U = {}"
          and P2in: "R[U <- y][Fix g y R <- g] \<in> \<T>\<lblot>A2\<rblot>" and nU: "U \<notin> \<lblot>A1\<rblot>"
          unfolding Vals0_def by blast
        have clP2: "FVars (R[U <- y][Fix g y R <- g]) = {}"
          using clV clU unfolding Ve by (auto simp: FVars_usubst split: if_splits)
        obtain m1 where m1: "\<forall>m\<ge>m1. \<forall>X. apx m (R[U <- y][Fix g y R <- g]) X \<longrightarrow> X \<in> \<T>\<lblot>A2\<rblot>"
          using OnlyTo.IH(4)[OF fA2 clP2 P2in] by blast
        have "\<forall>m\<ge>Suc m1. \<forall>W. apx m V W \<longrightarrow> W \<notin> \<lblot>OnlyTo A1 A2\<rblot>"
        proof (intro allI impI)
          fix m W assume mm: "Suc m1 \<le> m" and aW: "apx m V W"
          from apx_Fix_inv[OF aW[unfolded Ve]] show "W \<notin> \<lblot>OnlyTo A1 A2\<rblot>"
          proof (elim disjE exE conjE)
            fix R' assume We: "W = Fix g y R'" and aR: "apx m R R'"
            show ?thesis
            proof
              assume Win: "W \<in> \<lblot>OnlyTo A1 A2\<rblot>"
              have rel: "apx m1 (R[U <- y][Fix g y R <- g]) (R'[U <- y][W <- g])"
                unfolding We
                by (rule apx_usubst[OF apx_usubst[OF apx_mono[OF aR] apx_refl clU]
                      apx.apx_Fix[OF apx_mono[OF aR]] clV[unfolded Ve]])
                  (use mm in auto)
              have unf: "R'[U <- y][W <- g] \<in> \<T>\<lblot>A2\<rblot>" using m1 rel by auto
              have "U \<in> \<lblot>A1\<rblot>" by (rule OnlyTo_unfold[OF Win vU clU We unf])
              then show False using nU by simp
            qed
          next
            fix g2 y2 R2 j
            assume eqF: "Fix g y R = Fix g2 y2 R2" and fvR2: "FVars R2 \<subseteq> {g2, y2}"
              and gy2: "g2 \<noteq> y2" and mj: "m \<le> j" and We: "W = fixapp j g2 y2 R2"
            obtain j' where je: "j = Suc j'" and j'm: "m1 \<le> j'"
              using mj mm by (cases j) auto
            have clF2: "FVars (Fix g2 y2 R2) = {}" using fvR2 by auto
            have unfeq: "R[U <- y][Fix g y R <- g] = R2[U <- y2][Fix g2 y2 R2 <- g2]"
              by (rule Fix_unfold_cong[OF eqF vU]) (use clU in auto)
            show ?thesis
            proof
              assume Win: "W \<in> \<lblot>OnlyTo A1 A2\<rblot>"
              have rel: "apx m1 (R2[U <- y2][Fix g2 y2 R2 <- g2])
                  (R2[U <- y2][fixapp j' g2 y2 R2 <- g2])"
                by (rule apx_usubst[OF apx_refl apx.apx_Ax[OF fvR2 gy2 j'm] clF2])
              have unf: "R2[U <- y2][fixapp j' g2 y2 R2 <- g2] \<in> \<T>\<lblot>A2\<rblot>"
                using m1 rel unfolding unfeq by auto
              have "U \<in> \<lblot>A1\<rblot>"
                by (rule OnlyTo_unfold_fixapp[OF Win[unfolded We je] vU clU gy2 unf])
              then show False using nU by simp
            qed
          qed
        qed
        then show ?thesis by blast
      qed
    qed
  next
    case 2
    then show ?case using not_fv_OnlyTo by blast
  }
qed

text \<open>Theorem B.8 in the paper's formulation: multi-hole contexts are represented by
  substitution of a distinguished variable \<open>z\<close>.\<close>

theorem b8:
  fixes C :: "'a::var term"
  assumes clF: "FVars (Fix f x M) = {}" and fx: "f \<noteq> x"
    and cl: "FVars (C[Fix f x M <- z]) = {}"
  shows "safe A \<Longrightarrow> C[Fix f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow>
      \<exists>n0. \<forall>n\<ge>n0. C[fixapp n f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    and "finitely_verifiable A \<Longrightarrow> C[Fix f x M <- z] \<in> \<T>\<lblot>A\<rblot> \<Longrightarrow>
      \<exists>n0. \<forall>n\<ge>n0. C[fixapp n f x M <- z] \<in> \<T>\<lblot>A\<rblot>"
proof -
  have fvM: "FVars M \<subseteq> {f, x}" using clF by auto
  have rel: "\<And>n. apx n (C[Fix f x M <- z]) (C[fixapp n f x M <- z])"
    by (rule apx_usubst[OF apx_refl apx.apx_Ax[OF fvM fx] clF]) simp
  {
    assume "safe A" and "C[Fix f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    then obtain n0 where "\<forall>n\<ge>n0. \<forall>Q. apx n (C[Fix f x M <- z]) Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
      using b8_induction(1)[OF _ cl] by blast
    then have "\<forall>n\<ge>n0. C[fixapp n f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>" using rel by blast
    then show "\<exists>n0. \<forall>n\<ge>n0. C[fixapp n f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>" by blast
  }
  {
    assume "finitely_verifiable A" and "C[Fix f x M <- z] \<in> \<T>\<lblot>A\<rblot>"
    then obtain n0 where "\<forall>n\<ge>n0. \<forall>Q. apx n (C[Fix f x M <- z]) Q \<longrightarrow> Q \<in> \<T>\<lblot>A\<rblot>"
      using b8_induction(2)[OF _ cl] by blast
    then have "\<forall>n\<ge>n0. C[fixapp n f x M <- z] \<in> \<T>\<lblot>A\<rblot>" using rel by blast
    then show "\<exists>n0. \<forall>n\<ge>n0. C[fixapp n f x M <- z] \<in> \<T>\<lblot>A\<rblot>" by blast
  }
qed

section \<open>Safety Properties (Definition 4.4 and Theorem 4.7)\<close>

text \<open>A type defines a safety property (Definition 4.4) if membership in \<open>\<T>\<^sub>\<bottom>\<close> is (S1) downwards
  closed in the termination order \<open>\<lesssim>\<close> and (S2) admits finite counterexamples, witnessed by
  fixpoint approximants. Multi-hole contexts \<open>C[\<cdot>]\<close> are represented by terms with a
  distinguished free variable \<open>z\<close>. The \<open>itself\<close> argument fixes the variable type of the terms.\<close>

definition safety_property :: "'a::var itself \<Rightarrow> type \<Rightarrow> bool" where
  "safety_property tt A \<longleftrightarrow>
    ((\<forall>(C::'a term) N P z. FVars (C[N <- z]) = {} \<longrightarrow> P \<lesssim> N \<longrightarrow>
        C[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<longrightarrow> C[P <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>) \<and>
     (\<forall>(C::'a term) f x M z. f \<noteq> x \<longrightarrow> FVars (Fix f x M) = {} \<longrightarrow>
        FVars (C[Fix f x M <- z]) = {} \<longrightarrow> C[Fix f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<longrightarrow>
        (\<exists>k. C[fixapp k f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>)))"

text \<open>Theorem 4.7: every type in the safety fragment defines a safety property. (S1) is
  Theorem B.7, (S2) is Theorem B.8.\<close>

theorem safety_of_safe: \<comment> \<open>Theorem 4.7\<close>
  assumes "safe A"
  shows "safety_property (tt :: 'a::var itself) A"
  unfolding safety_property_def
proof (intro conjI allI impI)
  fix C N P z :: "'a term" and za :: 'a
  {
    fix z :: 'a
    assume "FVars (C[N <- z]) = {}" and "P \<lesssim> N" and "C[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    then show "C[P <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
      using b7[of C N z P A] assms by blast
  }
next
  fix C M :: "'a term" and f x z :: 'a
  assume "f \<noteq> x" and "FVars (Fix f x M) = {}" and "FVars (C[Fix f x M <- z]) = {}"
    and "C[Fix f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  then show "\<exists>k. C[fixapp k f x M <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    using b8(1)[of f x M C z A] assms by blast
qed

section \<open>Theorem B.9: Fixpoint Closure\<close>

lemma Lam_usubst:
  fixes V :: "'a::var term"
  assumes "x \<noteq> f" and "x \<notin> FVars V"
  shows "(Lam x M)[V <- f] = Lam x (M[V <- f])"
proof -
  obtain g where g: "g \<notin> FVars M \<union> FVars V \<union> {x, f}"
    using fresh_finite[of "FVars M \<union> FVars V \<union> {x, f}"] by auto
  have "(Fix g x M)[V <- f] = Fix g x (M[V <- f])"
    by (rule usubst_simps(7)) (use assms g in auto)
  moreover have "Lam x M = Fix g x M" by (rule Lam_eq) (use g in auto)
  moreover have "Lam x (M[V <- f]) = Fix g x (M[V <- f])"
    by (rule Lam_eq) (use g in \<open>auto simp: FVars_usubst split: if_splits\<close>)
  ultimately show ?thesis by simp
qed

lemma fixapp_closed: "FVars M \<subseteq> {f, x} \<Longrightarrow> FVars (fixapp n f x M) = {}"
  using FVars_fixapp[of n f x M] by auto

lemma divt_not_reaches_val: "divt \<rightarrow>* V \<Longrightarrow> \<not> val V"
  using divt_not_normalizes vals_are_normal unfolding normalizes_def by blast

theorem b9_To:
  fixes M :: "'a::var term"
  assumes fx: "f \<noteq> x" and cl: "FVars M \<subseteq> {f, x}" and sA: "safe (To A B)"
    and H: "\<And>V :: 'a term. val V \<Longrightarrow> FVars V = {} \<Longrightarrow> V \<in> \<lblot>To A B\<rblot> \<Longrightarrow>
      Lam x (M[V <- f]) \<in> \<lblot>To A B\<rblot>"
  shows "Fix f x M \<in> \<T>\<^sub>\<bottom>\<lblot>To A B\<rblot>"
proof (rule ccontr)
  assume nin: "Fix f x M \<notin> \<T>\<^sub>\<bottom>\<lblot>To A B\<rblot>"
  have clF: "FVars (Fix f x M) = {}" using cl by auto
  obtain n0 where n0: "\<forall>n\<ge>n0. \<forall>Q. apx n (Fix f x M) Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>To A B\<rblot>"
    using b8_induction(1)[OF sA clF nin] by blast
  have all: "fixapp n f x M \<in> \<lblot>To A B\<rblot>" for n
  proof (induction n)
    case 0
    obtain g where g: "g \<noteq> x" using fresh_finite[of "{x}"] by auto
    have Le: "Lam x divt = Fix g x (divt :: 'a term)"
      by (rule Lam_eq) (use g in auto)
    have bodyprop: "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow> U \<in> \<lblot>A\<rblot> \<longrightarrow>
      divt[U <- x][Fix g x divt <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
      by (auto simp: subst_idle divt_diverge)
    show ?case unfolding fixapp.simps(1) Le type_semantics.simps
      using bodyprop by blast
  next
    case (Suc n)
    have clfa: "FVars (fixapp n f x M) = {}" by (rule fixapp_closed[OF cl])
    show ?case unfolding fixapp.simps(2)
      by (rule H[OF val_fixapp clfa Suc.IH])
  qed
  have "apx n0 (Fix f x M) (fixapp n0 f x M)" by (rule apx.apx_Ax[OF cl fx]) simp
  then have "fixapp n0 f x M \<notin> \<T>\<^sub>\<bottom>\<lblot>To A B\<rblot>" using n0 by blast
  moreover have "fixapp n0 f x M \<in> \<T>\<^sub>\<bottom>\<lblot>To A B\<rblot>"
    using val_in_taubot[OF val_fixapp all] by blast
  ultimately show False by blast
qed

theorem b9_OnlyTo:
  fixes M :: "'a::var term"
  assumes fx: "f \<noteq> x" and cl: "FVars M \<subseteq> {f, x}" and sA: "safe (OnlyTo A B)"
    and H: "\<And>V :: 'a term. val V \<Longrightarrow> FVars V = {} \<Longrightarrow> V \<in> \<lblot>OnlyTo A B\<rblot> \<Longrightarrow>
      Lam x (M[V <- f]) \<in> \<lblot>OnlyTo A B\<rblot>"
  shows "Fix f x M \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A B\<rblot>"
proof (rule ccontr)
  assume nin: "Fix f x M \<notin> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A B\<rblot>"
  have clF: "FVars (Fix f x M) = {}" using cl by auto
  obtain n0 where n0: "\<forall>n\<ge>n0. \<forall>Q. apx n (Fix f x M) Q \<longrightarrow> Q \<notin> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A B\<rblot>"
    using b8_induction(1)[OF sA clF nin] by blast
  have all: "fixapp n f x M \<in> \<lblot>OnlyTo A B\<rblot>" for n
  proof (induction n)
    case 0
    obtain g where g: "g \<noteq> x" using fresh_finite[of "{x}"] by auto
    have Le: "Lam x divt = Fix g x (divt :: 'a term)"
      by (rule Lam_eq) (use g in auto)
    have bodyprop: "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow>
      divt[U <- x][Fix g x divt <- g] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> U \<in> \<lblot>A\<rblot>"
      by (auto simp: subst_idle dest: divt_not_reaches_val)
    show ?case unfolding fixapp.simps(1) Le type_semantics.simps
      using bodyprop by blast
  next
    case (Suc n)
    have clfa: "FVars (fixapp n f x M) = {}" by (rule fixapp_closed[OF cl])
    show ?case unfolding fixapp.simps(2)
      by (rule H[OF val_fixapp clfa Suc.IH])
  qed
  have "apx n0 (Fix f x M) (fixapp n0 f x M)" by (rule apx.apx_Ax[OF cl fx]) simp
  then have "fixapp n0 f x M \<notin> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A B\<rblot>" using n0 by blast
  moreover have "fixapp n0 f x M \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A B\<rblot>"
    using val_in_taubot[OF val_fixapp all] by blast
  ultimately show False by blast
qed

section \<open>Theorem 4.8: Semantic Soundness — infrastructure\<close>

subsection \<open>Properties of valuations\<close>

lemma eval_Cons: "eval (p # ps) M = eval ps (M[snd p <- fst p])"
  by (cases p) simp

lemma cvs_Nil[simp]: "closed_val_subst []"
  by (simp add: closed_val_subst_def)

lemma cvs_Cons: "closed_val_subst (p # \<theta>) \<longleftrightarrow>
  val (snd p) \<and> FVars (snd p) = {} \<and> closed_val_subst \<theta>"
  by (auto simp: closed_val_subst_def)

lemma eval_closed: "FVars M = {} \<Longrightarrow> eval \<theta> M = M"
  by (induction \<theta>) (auto simp: eval_Cons subst_idle)

lemma eval_Zero[simp]: "eval \<theta> Zero = Zero"
  by (induction \<theta>) (auto simp: eval_Cons)

lemma eval_Succ[simp]: "eval \<theta> (Succ M) = Succ (eval \<theta> M)"
  by (induction \<theta> arbitrary: M) (auto simp: eval_Cons)

lemma eval_Pred[simp]: "eval \<theta> (Pred M) = Pred (eval \<theta> M)"
  by (induction \<theta> arbitrary: M) (auto simp: eval_Cons)

lemma eval_If[simp]: "eval \<theta> (If M N P) = If (eval \<theta> M) (eval \<theta> N) (eval \<theta> P)"
  by (induction \<theta> arbitrary: M N P) (auto simp: eval_Cons)

lemma eval_App[simp]: "eval \<theta> (App M N) = App (eval \<theta> M) (eval \<theta> N)"
  by (induction \<theta> arbitrary: M N) (auto simp: eval_Cons)

lemma eval_Pair[simp]: "eval \<theta> (term.Pair M N) = term.Pair (eval \<theta> M) (eval \<theta> N)"
  by (induction \<theta> arbitrary: M N) (auto simp: eval_Cons)

lemma eval_Var:
  "closed_val_subst \<theta> \<Longrightarrow>
   eval \<theta> (Var v) = Var v \<or> (val (eval \<theta> (Var v)) \<and> FVars (eval \<theta> (Var v)) = {})"
  by (induction \<theta> arbitrary: v)
    (auto simp: eval_Cons cvs_Cons eval_closed)

lemma eval_Fix:
  "closed_val_subst \<theta> \<Longrightarrow> {f, x} \<inter> fst ` set \<theta> = {} \<Longrightarrow>
   eval \<theta> (Fix f x M) = Fix f x (eval \<theta> M)"
proof (induction \<theta> arbitrary: M)
  case Nil then show ?case by simp
next
  case (Cons p \<theta>)
  have "(Fix f x M)[snd p <- fst p] = Fix f x (M[snd p <- fst p])"
    by (rule usubst_simps(7)) (use Cons.prems in \<open>auto simp: cvs_Cons\<close>)
  then show ?case using Cons by (simp add: eval_Cons cvs_Cons)
qed

lemma eval_Let:
  "closed_val_subst \<theta> \<Longrightarrow> dset xy \<inter> fst ` set \<theta> = {} \<Longrightarrow>
   eval \<theta> (term.Let xy M N) = term.Let xy (eval \<theta> M) (eval \<theta> N)"
proof (induction \<theta> arbitrary: M N)
  case Nil then show ?case by simp
next
  case (Cons p \<theta>)
  have "(term.Let xy M N)[snd p <- fst p] = term.Let xy (M[snd p <- fst p]) (N[snd p <- fst p])"
    by (rule usubst_Let) (use Cons.prems in \<open>auto simp: cvs_Cons\<close>)
  then show ?case using Cons by (simp add: eval_Cons cvs_Cons)
qed

lemma eval_usubst:
  "closed_val_subst \<theta> \<Longrightarrow> y \<notin> fst ` set \<theta> \<Longrightarrow> FVars V = {} \<Longrightarrow>
   eval \<theta> (M[V <- y]) = (eval \<theta> M)[V <- y]"
proof (induction \<theta> arbitrary: M)
  case Nil then show ?case by simp
next
  case (Cons p \<theta>)
  have "M[V <- y][snd p <- fst p] = M[snd p <- fst p][V[snd p <- fst p] <- y]"
    by (rule usubst_usubst) (use Cons.prems in \<open>auto simp: cvs_Cons\<close>)
  also have "\<dots> = M[snd p <- fst p][V <- y]"
    using Cons.prems(3) by (simp add: subst_idle)
  finally show ?case using Cons by (simp add: eval_Cons cvs_Cons)
qed

lemma FVars_eval: "closed_val_subst \<theta> \<Longrightarrow> FVars (eval \<theta> M) \<subseteq> FVars M"
proof (induction \<theta> arbitrary: M)
  case Nil then show ?case by simp
next
  case (Cons p \<theta>)
  have "FVars (M[snd p <- fst p]) \<subseteq> FVars M"
    using Cons.prems by (auto simp: FVars_usubst cvs_Cons split: if_splits)
  then show ?case using Cons by (fastforce simp: eval_Cons cvs_Cons)
qed

lemma cvs_filter: "closed_val_subst \<theta> \<Longrightarrow> closed_val_subst (filter Q \<theta>)"
  by (auto simp: closed_val_subst_def)

lemma eval_filter:
  "closed_val_subst \<theta> \<Longrightarrow> FVars M \<subseteq> S \<Longrightarrow>
   eval (filter (\<lambda>p. fst p \<in> S) \<theta>) M = eval \<theta> M"
proof (induction \<theta> arbitrary: M)
  case Nil then show ?case by simp
next
  case (Cons p \<theta>)
  show ?case
  proof (cases "fst p \<in> S")
    case True
    have "FVars (M[snd p <- fst p]) \<subseteq> S"
      using Cons.prems by (auto simp: FVars_usubst cvs_Cons split: if_splits)
    then show ?thesis using Cons True by (simp add: eval_Cons cvs_Cons)
  next
    case False
    then have "fst p \<notin> FVars M" using Cons.prems(2) by auto
    then have "M[snd p <- fst p] = M" by (rule subst_idle)
    then show ?thesis using Cons False by (simp add: eval_Cons cvs_Cons)
  qed
qed

subsection \<open>Divergence propagation and evaluation inversions\<close>

lemma div_Succ: "diverge A \<Longrightarrow> diverge (Succ (A::'a::var term))"
proof -
  assume d: "diverge A"
  obtain h where h: "h \<notin> FVars (A::'a term)" by (meson arb_element finite_FVars)
  have ctx: "eval_ctx h (Succ (Var h))" by (rule eval_ctx.intros(4)[OF eval_ctx.intros(1)])
  show ?thesis using div_ctx[OF ctx d] by simp
qed

lemma div_Pred: "diverge A \<Longrightarrow> diverge (Pred (A::'a::var term))"
proof -
  assume d: "diverge A"
  obtain h where h: "h \<notin> FVars (A::'a term)" by (meson arb_element finite_FVars)
  have ctx: "eval_ctx h (Pred (Var h))" by (rule eval_ctx.intros(5)[OF eval_ctx.intros(1)])
  show ?thesis using div_ctx[OF ctx d] by simp
qed

lemma div_If: "diverge A \<Longrightarrow> diverge (If (A::'a::var term) N P)"
proof -
  assume d: "diverge A"
  obtain h where h: "h \<notin> FVars (A::'a term) \<union> FVars N \<union> FVars P"
    by (meson arb_element finite_FVars finite_UnI)
  have ctx: "eval_ctx h (If (Var h) N P)"
    by (rule eval_ctx.intros(9)[OF eval_ctx.intros(1)]) (use h in auto)
  show ?thesis using div_ctx[OF ctx d] h by (auto simp: subst_idle)
qed

lemma div_App1: "diverge A \<Longrightarrow> diverge (App (A::'a::var term) N)"
proof -
  assume d: "diverge A"
  obtain h where h: "h \<notin> FVars (A::'a term) \<union> FVars N"
    by (meson arb_element finite_FVars finite_UnI)
  have ctx: "eval_ctx h (App (Var h) N)"
    by (rule eval_ctx.intros(3)[OF eval_ctx.intros(1)]) (use h in auto)
  show ?thesis using div_ctx[OF ctx d] h by (auto simp: subst_idle)
qed

lemma div_AppFix2: "diverge B \<Longrightarrow> diverge (App (Fix g y R) (B::'a::var term))"
proof -
  assume d: "diverge B"
  obtain h where h: "h \<notin> FVars (B::'a term) \<union> FVars R"
    by (meson arb_element finite_FVars finite_UnI)
  have ctx: "eval_ctx h (App (Fix g y R) (Var h))"
    by (rule eval_ctx.intros(2)[OF eval_ctx.intros(1)]) (use h in auto)
  have "(App (Fix g y R) (Var h))[B <- h] = App (Fix g y R) B"
    using h by (auto simp: subst_idle)
  then show ?thesis using div_ctx[OF ctx d] by simp
qed

lemma div_Let1: "diverge A \<Longrightarrow> diverge (term.Let xy (A::'a::var term) N)"
proof -
  assume d: "diverge A"
  obtain xy' N' where eq: "term.Let xy A N = term.Let xy' A N'"
    and dd: "dset xy' \<inter> FVars A = {}"
    using Let_refresh[of "FVars A" xy A N] finite_FVars by blast
  obtain h where h: "h \<notin> FVars (A::'a term) \<union> FVars N' \<union> dset xy'"
    by (meson arb_element finite_FVars finite_dset finite_UnI)
  have ctx: "eval_ctx h (term.Let xy' (Var h) N')"
    by (rule eval_ctx.intros(8)[OF eval_ctx.intros(1)]) (use h in auto)
  have peq: "(term.Let xy' (Var h) N')[A <- h] = term.Let xy' A N'"
    using usubst_Let[of h xy' A "Var h" N'] h dd by (auto simp: subst_idle)
  show ?thesis unfolding eq using div_ctx[OF ctx d, unfolded peq] .
qed

lemma normal_betas: "W \<rightarrow>[k] N \<Longrightarrow> normal W \<Longrightarrow> N = W"
  by (induction rule: betas.induct) (auto simp: normal_def)

lemma beta_star_pass:
  fixes M :: "'a::var term"
  assumes MW: "M \<rightarrow>* W" and nW: "normal W" and MN: "M \<rightarrow>* N"
  shows "N \<rightarrow>* W"
proof -
  obtain a where a: "M \<rightarrow>[a] W" using MW beta_star_def by blast
  obtain b where b: "M \<rightarrow>[b] N" using MN beta_star_def by blast
  show ?thesis
  proof (cases "b \<le> a")
    case True
    then show ?thesis using betas_prefix[OF b a] beta_star_def by blast
  next
    case False
    then have "W \<rightarrow>[b - a] N" using betas_prefix[OF a b] by simp
    then have "N = W" using normal_betas nW by blast
    then show ?thesis using beta_star_def betas.refl by blast
  qed
qed

lemma App2_betas: "N \<rightarrow>[k] N' \<Longrightarrow> App (Fix g y R) N \<rightarrow>[k] App (Fix g y R) N'"
  by (induction rule: betas.induct) (auto intro: betas.intros beta.OrdApp2)

lemma App2_beta_star: "N \<rightarrow>* N' \<Longrightarrow> App (Fix g y R) N \<rightarrow>* App (Fix g y R) N'"
  using App2_betas beta_star_def by metis

lemma Succ_betas_inv:
  fixes A :: "'a::var term"
  shows "X \<rightarrow>[k] W \<Longrightarrow> X = Succ A \<Longrightarrow> val W \<Longrightarrow> \<exists>V. W = Succ V \<and> A \<rightarrow>* V \<and> num V"
proof (induction arbitrary: A rule: betas.induct)
  case (refl M)
  then show ?case using val_Succ_num beta_star_def betas.refl by blast
next
  case (step M N k P)
  from step.hyps(1)[unfolded step.prems(1)] show ?case
  proof (cases rule: beta.cases)
    case (OrdSucc M0 M0')
    obtain V where "P = Succ V" "M0' \<rightarrow>* V" "num V"
      using step.IH[OF _ step.prems(2)] OrdSucc by blast
    then show ?thesis
      using OrdSucc beta_star_def betas.step by (metis term.inject(1))
  qed (auto simp: step.prems)
qed

lemma Pred_betas_inv:
  fixes A :: "'a::var term"
  shows "X \<rightarrow>[k] W \<Longrightarrow> X = Pred A \<Longrightarrow> val W \<Longrightarrow> \<exists>V. A \<rightarrow>* V \<and> num V"
proof (induction arbitrary: A rule: betas.induct)
  case (refl M)
  then show ?case using not_val_Pred by blast
next
  case (step M N k P)
  from step.hyps(1)[unfolded step.prems(1)] show ?case
  proof (cases rule: beta.cases)
    case (OrdPred M0 M0')
    obtain V where "M0' \<rightarrow>* V" "num V"
      using step.IH[OF _ step.prems(2)] OrdPred by blast
    then show ?thesis
      using OrdPred beta_star_def betas.step by (metis term.inject(2))
  next
    case PredZ
    then show ?thesis using beta_star_def betas.refl num.intros(1)
      by (metis term.inject(2))
  next
    case PredS
    then show ?thesis using beta_star_def betas.refl num.intros(2)
      by (metis term.inject(2))
  qed (auto simp: step.prems)
qed

lemma Pair_betas_inv:
  fixes A B :: "'a::var term"
  shows "X \<rightarrow>[k] W \<Longrightarrow> X = term.Pair A B \<Longrightarrow> val W \<Longrightarrow>
    \<exists>V1 V2. W = term.Pair V1 V2 \<and> A \<rightarrow>* V1 \<and> B \<rightarrow>* V2 \<and> val V1 \<and> val V2"
proof (induction arbitrary: A B rule: betas.induct)
  case (refl M)
  then show ?case using val_Pair_D beta_star_def betas.refl by blast
next
  case (step M N k P)
  from step.hyps(1)[unfolded step.prems(1)] show ?case
  proof (cases rule: beta.cases)
    case (OrdPair1 M0 M0' N0)
    obtain V1 V2 where "P = term.Pair V1 V2" "M0' \<rightarrow>* V1" "N0 \<rightarrow>* V2" "val V1" "val V2"
      using step.IH[OF _ step.prems(2)] OrdPair1 by blast
    then show ?thesis
      using OrdPair1 beta_star_def betas.step by (metis term.inject(7))
  next
    case (OrdPair2 V0 N0 N0')
    obtain V1 V2 where "P = term.Pair V1 V2" "V0 \<rightarrow>* V1" "N0' \<rightarrow>* V2" "val V1" "val V2"
      using step.IH[OF _ step.prems(2)] OrdPair2 by blast
    then show ?thesis
      using OrdPair2 beta_star_def betas.step by (metis term.inject(7))
  qed (auto simp: step.prems)
qed

lemma If_betas_inv:
  fixes A N P :: "'a::var term"
  shows "X \<rightarrow>[k] W \<Longrightarrow> X = If A N P \<Longrightarrow> val W \<Longrightarrow>
    \<exists>nv. num nv \<and> A \<rightarrow>* nv \<and> ((nv = Zero \<and> N \<rightarrow>* W) \<or> ((\<exists>m. nv = Succ m) \<and> P \<rightarrow>* W))"
proof (induction arbitrary: A N P rule: betas.induct)
  case (refl M)
  then show ?case using not_val_If by blast
next
  case (step M N0 k P0)
  from step.hyps(1)[unfolded step.prems(1)] show ?case
  proof (cases rule: beta.cases)
    case (OrdIf Ma M' Na Pa)
    obtain nv where "num nv" "M' \<rightarrow>* nv"
      "((nv = Zero \<and> Na \<rightarrow>* P0) \<or> ((\<exists>m. nv = Succ m) \<and> Pa \<rightarrow>* P0))"
      using step.IH[OF _ step.prems(2)] OrdIf by blast
    then show ?thesis
      using OrdIf beta_star_def betas.step by (metis term.inject(3))
  next
    case (Ifz Pa)
    then show ?thesis
      using step.hyps(2) beta_star_def betas.refl num.intros(1)
      by (metis term.inject(3))
  next
    case (Ifs n Na)
    then show ?thesis
      using step.hyps(2) beta_star_def betas.refl num.intros(2)
      by (metis term.inject(3))
  qed (auto simp: step.prems)
qed

lemma App_betas_inv:
  fixes A B :: "'a::var term"
  shows "X \<rightarrow>[k] W \<Longrightarrow> X = App A B \<Longrightarrow> val W \<Longrightarrow>
    \<exists>g y R V. A \<rightarrow>* Fix g y R \<and> B \<rightarrow>* V \<and> val V \<and> g \<notin> FVars V \<and>
      R[V <- y][Fix g y R <- g] \<rightarrow>* W"
proof (induction arbitrary: A B rule: betas.induct)
  case (refl M)
  then show ?case using not_val_App by blast
next
  case (step M N k P)
  from step.hyps(1)[unfolded step.prems(1)] show ?case
  proof (cases rule: beta.cases)
    case (OrdApp2 N0 N0' f0 x0 M0)
    obtain g y R V where "Fix f0 x0 M0 \<rightarrow>* Fix g y R" "N0' \<rightarrow>* V" "val V" "g \<notin> FVars V"
      "R[V <- y][Fix g y R <- g] \<rightarrow>* P"
      using step.IH[OF _ step.prems(2)] OrdApp2 by blast
    then show ?thesis
      using OrdApp2 beta_star_def betas.step by (metis term.inject(5))
  next
    case (OrdApp1 M0 M0' N0)
    obtain g y R V where "M0' \<rightarrow>* Fix g y R" "N0 \<rightarrow>* V" "val V" "g \<notin> FVars V"
      "R[V <- y][Fix g y R <- g] \<rightarrow>* P"
      using step.IH[OF _ step.prems(2)] OrdApp1 by blast
    then show ?thesis
      using OrdApp1 beta_star_def betas.step by (metis term.inject(5))
  next
    case (FixBeta V0 f0 x0 M0)
    have AB: "A = Fix f0 x0 M0" "B = V0" using FixBeta(1) by auto
    have r1: "A \<rightarrow>* Fix f0 x0 M0" and r2: "B \<rightarrow>* V0"
      unfolding AB using beta_star_def betas.refl by blast+
    have "M0[V0 <- x0][Fix f0 x0 M0 <- f0] \<rightarrow>* P"
      using FixBeta(2) step.hyps(2) beta_star_def by blast
    then show ?thesis using r1 r2 FixBeta(3,4) by blast
  qed (auto simp: step.prems)
qed

lemma Let_betas_inv:
  fixes A B :: "'a::var term"
  shows "X \<rightarrow>[k] W \<Longrightarrow> X = term.Let xy A B \<Longrightarrow> val W \<Longrightarrow>
    \<exists>V1 V2. A \<rightarrow>* term.Pair V1 V2 \<and> val V1 \<and> val V2"
proof (induction arbitrary: xy A B rule: betas.induct)
  case (refl M)
  then show ?case using not_val_Let by blast
next
  case (step M N k P)
  from step.hyps(1)[unfolded step.prems(1)] show ?case
  proof (cases rule: beta.cases)
    case (OrdLet M0 M0' xy0 N0)
    have A0: "M0 = A" using OrdLet(1) unfolding term.inject(8) by auto
    obtain V1 V2 where "M0' \<rightarrow>* term.Pair V1 V2" "val V1" "val V2"
      using step.IH[OF OrdLet(2) step.prems(2)] by blast
    then show ?thesis
      using OrdLet(3) A0 beta_star_def betas.step by metis
  next
    case (Let V0 W0 xy0 M0)
    have "A = term.Pair V0 W0" using Let(1) unfolding term.inject(8) by auto
    then show ?thesis using Let(3,4) beta_star_def betas.refl by metis
  qed (auto simp: step.prems)
qed

subsection \<open>Semantic helper lemmas\<close>

lemma val_taubot_iff: "val V \<Longrightarrow> (V \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>) = (V \<in> \<lblot>A\<rblot>)"
  using val_tau_iff val_not_diverge by auto

lemma tau_backward:
  assumes "M \<rightarrow>* N" and "N \<in> \<T>\<lblot>A\<rblot>" shows "M \<in> \<T>\<lblot>A\<rblot>"
proof -
  obtain V where "V \<in> \<lblot>A\<rblot>" "N \<rightarrow>* V" "val V" using assms(2) by auto
  then show ?thesis using beta_star_sums[OF assms(1)] by auto
qed

lemma taubot_backward:
  assumes "M \<rightarrow>* N" and "N \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>" shows "M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  using assms tau_backward[OF assms(1)] beta_star_diverge_back[OF assms(1)] by auto

lemma tau_forward:
  fixes M :: "'a::var term"
  assumes "M \<rightarrow>* N" and "M \<in> \<T>\<lblot>A\<rblot>"
  shows "N \<in> \<T>\<lblot>A\<rblot>"
proof -
  obtain V where V: "V \<in> \<lblot>A\<rblot>" "M \<rightarrow>* V" "val V" using assms(2) by auto
  have "N \<rightarrow>* V" using beta_star_pass[OF V(2) vals_are_normal[OF V(3)] assms(1)] .
  then show ?thesis using V by auto
qed

lemma disjoint_sem: "A || B \<Longrightarrow> V \<in> \<lblot>A\<rblot> \<Longrightarrow> V \<in> \<lblot>B\<rblot> \<Longrightarrow> False"
proof (induction arbitrary: V rule: disjunction.induct)
  case 1
  then have "num V" and "is_Pair V" using Prod_is_Pair by auto
  then show ?case by (cases rule: num.cases) auto
next
  case 2
  then have "num V" and "is_Fix V" using To_is_Fix by auto
  then show ?case by (cases rule: num.cases) auto
next
  case 3
  then have "num V" and "is_Fix V" using OnlyTo_is_Fix by auto
  then show ?case by (cases rule: num.cases) auto
next
  case 4
  then have "is_Pair V" and "is_Fix V" using Prod_is_Pair To_is_Fix by auto
  then show ?case by (auto simp: is_Pair_def is_Fix_def)
next
  case 5
  then have "is_Pair V" and "is_Fix V" using Prod_is_Pair OnlyTo_is_Fix by auto
  then show ?case by (auto simp: is_Pair_def is_Fix_def)
next
  case 6
  then show ?case by blast
qed

lemma fix_in_OnlyTo_Ok:
  fixes F :: "'a::var term"
  assumes "is_Fix F"
  shows "F \<in> \<lblot>OnlyTo Ok A\<rblot>"
proof -
  obtain g y R where Fe: "F = Fix g y R" using assms unfolding is_Fix_def by blast
  have "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow> R[U <- y][Fix g y R <- g] \<in> \<T>\<lblot>A\<rblot> \<longrightarrow> U \<in> \<lblot>Ok\<rblot>"
    by (auto simp: Vals0_def)
  then show ?thesis unfolding Fe type_semantics.simps by blast
qed

lemma dfst_neq_dsnd: "dfst xy \<noteq> dsnd xy"
  by transfer auto

lemma num_Pred:
  fixes n :: "'a::var term"
  assumes "num n"
  shows "\<exists>m. num m \<and> Pred n \<rightarrow> m"
  using assms by (cases rule: num.cases) (auto intro: beta.PredZ beta.PredS num.intros)


subsection \<open>Semantic content of the individual typing rules\<close>

lemma tau_dest:
  fixes M :: "'a::var term"
  assumes "M \<in> \<T>\<lblot>A\<rblot>"
  obtains W where "M \<rightarrow>* W" and "val W" and "W \<in> \<lblot>A\<rblot>"
  using assms by auto

lemma tau_intro: "M \<rightarrow>* W \<Longrightarrow> val W \<Longrightarrow> W \<in> \<lblot>A\<rblot> \<Longrightarrow> M \<in> \<T>\<lblot>A\<rblot>"
  by auto

lemma tau_unique:
  fixes M :: "'a::var term"
  assumes "M \<in> \<T>\<lblot>A\<rblot>" and "M \<rightarrow>* W" and "val W"
  shows "W \<in> \<lblot>A\<rblot>"
proof -
  obtain W' where W': "M \<rightarrow>* W'" "val W'" "W' \<in> \<lblot>A\<rblot>" using assms(1) by auto
  have "W = W'"
    using beta_star_normal_unique assms(2,3) W'(1,2) vals_are_normal
    unfolding beta_star_def by blast
  then show ?thesis using W'(3) by simp
qed

lemma sem_Succ_Nat:
  fixes M :: "'a::var term"
  assumes "M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
  shows "Succ M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
proof -
  from assms consider (v) "M \<in> \<T>\<lblot>Nat\<rblot>" | (d) "M \<Up>" by auto
  then show ?thesis
  proof cases
    case v
    then obtain n where "M \<rightarrow>* n" "num n" by auto
    then have "Succ M \<rightarrow>* Succ n" "num (Succ n)"
      using Succ_beta_star num.intros(2) by auto
    then show ?thesis using val.intros(2) by auto
  next
    case d
    then show ?thesis using div_Succ by auto
  qed
qed

lemma sem_Pred_Nat:
  fixes M :: "'a::var term"
  assumes "M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
  shows "Pred M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
proof -
  from assms consider (v) "M \<in> \<T>\<lblot>Nat\<rblot>" | (d) "M \<Up>" by auto
  then show ?thesis
  proof cases
    case v
    then obtain n where n: "M \<rightarrow>* n" "num n" by auto
    obtain m where m: "num m" "Pred n \<rightarrow> m" using num_Pred[OF n(2)] by blast
    have "Pred M \<rightarrow>* m"
      using Pred_beta_star[OF n(1)] m(2) beta_star_sums beta_star_def
        betas.step betas.refl by metis
    then show ?thesis using m(1) val.intros(2) by auto
  next
    case d
    then show ?thesis using div_Pred by auto
  qed
qed

lemma sem_Pair:
  fixes M N :: "'a::var term"
  assumes "M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>" and "N \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
  shows "term.Pair M N \<in> \<T>\<^sub>\<bottom>\<lblot>Prod A B\<rblot>"
proof (cases "M \<Up>")
  case True
  then show ?thesis using Pair_div by auto
next
  case False
  then have "M \<in> \<T>\<lblot>A\<rblot>" using assms(1) by auto
  then obtain V where V: "M \<rightarrow>* V" "val V" "V \<in> \<lblot>A\<rblot>" by (rule tau_dest)
  show ?thesis
  proof (cases "N \<Up>")
    case True
    have "term.Pair M N \<rightarrow>* term.Pair V N"
      using Pair_beta_star[OF V(1) _ V(2)] beta_star_def betas.refl by blast
    then show ?thesis
      using beta_star_diverge_back Pair_div2[OF V(2) True] by auto
  next
    case False
    then have "N \<in> \<T>\<lblot>B\<rblot>" using assms(2) by auto
    then obtain W where W: "N \<rightarrow>* W" "val W" "W \<in> \<lblot>B\<rblot>" by (rule tau_dest)
    have "term.Pair M N \<rightarrow>* term.Pair V W" by (rule Pair_beta_star[OF V(1) W(1) V(2)])
    moreover have "term.Pair V W \<in> \<lblot>Prod A B\<rblot>" using V(3) W(3) by auto
    ultimately have "term.Pair M N \<in> \<T>\<lblot>Prod A B\<rblot>"
      using val.intros(3)[OF V(2) W(2)] by (blast intro: tau_intro)
    then show ?thesis by auto
  qed
qed

lemma sem_If:
  fixes M N P :: "'a::var term"
  assumes "M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>" and "N \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>" and "P \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  shows "If M N P \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
proof (cases "M \<Up>")
  case True
  then show ?thesis using div_If by auto
next
  case False
  then have "M \<in> \<T>\<lblot>Nat\<rblot>" using assms(1) by auto
  then obtain n where n: "M \<rightarrow>* n" "num n" by auto
  have steps: "If M N P \<rightarrow>* If n N P" by (rule If_beta_star[OF n(1)])
  show ?thesis
  proof (cases rule: num.cases[OF n(2)])
    case 1
    have "If n N P \<rightarrow> N" unfolding 1 by (rule beta.Ifz)
    then have "If M N P \<rightarrow>* N"
      using steps beta_star_sums beta_star_def betas.step betas.refl by metis
    then show ?thesis using assms(2) taubot_backward by blast
  next
    case (2 m)
    have "If n N P \<rightarrow> P" unfolding 2 by (rule beta.Ifs) (use 2 in simp)
    then have "If M N P \<rightarrow>* P"
      using steps beta_star_sums beta_star_def betas.step betas.refl by metis
    then show ?thesis using assms(3) taubot_backward by blast
  qed
qed

lemma sem_App:
  fixes M N :: "'a::var term"
  assumes M: "M \<in> \<T>\<^sub>\<bottom>\<lblot>To B A\<rblot>" and N: "N \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>" and clN: "FVars N = {}"
  shows "App M N \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
proof (cases "M \<Up>")
  case True
  then show ?thesis using div_App1 by auto
next
  case False
  then have "M \<in> \<T>\<lblot>To B A\<rblot>" using M by auto
  then obtain F where F: "M \<rightarrow>* F" "val F" "F \<in> \<lblot>To B A\<rblot>" by (rule tau_dest)
  obtain g y R where Fe: "F = Fix g y R" using To_is_Fix[OF F(3)] unfolding is_Fix_def by blast
  have stepsM: "App M N \<rightarrow>* App (Fix g y R) N" using App_beta_star[OF F(1)] Fe by simp
  show ?thesis
  proof (cases "N \<Up>")
    case True
    show ?thesis
      using beta_star_diverge_back[OF stepsM div_AppFix2[OF True]] by auto
  next
    case False
    then have "N \<in> \<T>\<lblot>B\<rblot>" using N by auto
    then obtain V where V: "N \<rightarrow>* V" "val V" "V \<in> \<lblot>B\<rblot>" by (rule tau_dest)
    have clV: "FVars V = {}" using FVars_beta_star V(1) clN by auto
    have steps2: "App (Fix g y R) N \<rightarrow>* App (Fix g y R) V" by (rule App2_beta_star[OF V(1)])
    have "App (Fix g y R) V \<rightarrow> R[V <- y][Fix g y R <- g]"
      by (rule beta.FixBeta[OF V(2)]) (use clV in simp)
    then have steps3: "App M N \<rightarrow>* R[V <- y][Fix g y R <- g]"
      using stepsM steps2 beta_star_sums beta_star_def betas.step betas.refl by metis
    have "R[V <- y][Fix g y R <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
      using To_unfold[OF F(3)[unfolded Fe] V(2) clV V(3) HOL.refl] .
    then show ?thesis using taubot_backward[OF steps3] by blast
  qed
qed

lemma sem_Let:
  fixes M N :: "'a::var term"
  assumes M: "M \<in> \<T>\<^sub>\<bottom>\<lblot>Prod B C\<rblot>" and clM: "FVars M = {}"
    and body: "\<And>V W. val V \<Longrightarrow> val W \<Longrightarrow> FVars V = {} \<Longrightarrow> FVars W = {} \<Longrightarrow>
      V \<in> \<lblot>B\<rblot> \<Longrightarrow> W \<in> \<lblot>C\<rblot> \<Longrightarrow> N[V <- dfst xy][W <- dsnd xy] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  shows "term.Let xy M N \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
proof (cases "M \<Up>")
  case True
  then show ?thesis using div_Let1 by auto
next
  case False
  then have "M \<in> \<T>\<lblot>Prod B C\<rblot>" using M by auto
  then obtain P where P: "M \<rightarrow>* P" "val P" "P \<in> \<lblot>Prod B C\<rblot>" by (rule tau_dest)
  obtain V W where Pe: "P = term.Pair V W" and V: "V \<in> \<lblot>B\<rblot>" and W: "W \<in> \<lblot>C\<rblot>"
    using P(3) by auto
  have vV: "val V" and vW: "val W" using val_Pair_D P(2) Pe by auto
  have clP: "FVars P = {}" using FVars_beta_star P(1) clM by auto
  then have clV: "FVars V = {}" and clW: "FVars W = {}" unfolding Pe by auto
  have steps: "term.Let xy M N \<rightarrow>* term.Let xy (term.Pair V W) N"
    using Let_beta_star[OF P(1)] Pe by simp
  have "term.Let xy (term.Pair V W) N \<rightarrow> N[V <- dfst xy][W <- dsnd xy]"
    by (rule beta.Let[OF vV vW]) (use clV in simp)
  then have steps2: "term.Let xy M N \<rightarrow>* N[V <- dfst xy][W <- dsnd xy]"
    using steps beta_star_sums beta_star_def betas.step betas.refl by metis
  show ?thesis
    using taubot_backward[OF steps2 body[OF vV vW clV clW V W]] .
qed

lemma ext_Succ:
  fixes M :: "'a::var term"
  assumes "Succ M \<in> \<T>\<lblot>A\<rblot>"
  shows "M \<in> \<T>\<lblot>Nat\<rblot>"
proof -
  obtain W where W: "Succ M \<rightarrow>* W" "val W" using assms by auto
  obtain V where "M \<rightarrow>* V" "num V"
    using Succ_betas_inv W beta_star_def by blast
  then show ?thesis using val.intros(2) by auto
qed

lemma ext_Pred:
  fixes M :: "'a::var term"
  assumes "Pred M \<in> \<T>\<lblot>A\<rblot>"
  shows "M \<in> \<T>\<lblot>Nat\<rblot>"
proof -
  obtain W where W: "Pred M \<rightarrow>* W" "val W" using assms by auto
  obtain V where "M \<rightarrow>* V" "num V"
    using Pred_betas_inv W beta_star_def by blast
  then show ?thesis using val.intros(2) by auto
qed

lemma ext_If1:
  fixes M :: "'a::var term"
  assumes "If M N P \<in> \<T>\<lblot>A\<rblot>"
  shows "M \<in> \<T>\<lblot>Nat\<rblot>"
proof -
  obtain W where W: "If M N P \<rightarrow>* W" "val W" using assms by auto
  obtain nv where "num nv" "M \<rightarrow>* nv"
    using If_betas_inv W beta_star_def by blast
  then show ?thesis using val.intros(2) by auto
qed

lemma ext_If2:
  fixes M :: "'a::var term"
  assumes "If M N P \<in> \<T>\<lblot>A\<rblot>"
  shows "N \<in> \<T>\<lblot>A\<rblot> \<or> P \<in> \<T>\<lblot>A\<rblot>"
proof -
  obtain W where W: "If M N P \<rightarrow>* W" "val W" "W \<in> \<lblot>A\<rblot>"
    using assms by (rule tau_dest)
  obtain k where k: "If M N P \<rightarrow>[k] W" using W(1) beta_star_def by blast
  obtain nv :: "'a term" where "(nv = Zero \<and> N \<rightarrow>* W) \<or> (\<exists>m. nv = Succ m) \<and> P \<rightarrow>* W"
    using If_betas_inv[OF k HOL.refl W(2)] by blast
  then show ?thesis using W(2,3) by (auto intro: tau_intro)
qed

lemma ext_Pair:
  fixes M N :: "'a::var term"
  assumes "term.Pair M N \<in> \<T>\<lblot>Prod A B\<rblot>"
  shows "M \<in> \<T>\<lblot>A\<rblot> \<and> N \<in> \<T>\<lblot>B\<rblot>"
proof -
  obtain W where W: "term.Pair M N \<rightarrow>* W" "val W" "W \<in> \<lblot>Prod A B\<rblot>"
    using assms by (rule tau_dest)
  obtain V1 V2 where V: "W = term.Pair V1 V2" "M \<rightarrow>* V1" "N \<rightarrow>* V2" "val V1" "val V2"
    using Pair_betas_inv W(1,2) beta_star_def by blast
  have "V1 \<in> \<lblot>A\<rblot>" "V2 \<in> \<lblot>B\<rblot>" using W(3) unfolding V(1) by auto
  then show ?thesis using V by auto
qed

lemma ext_Pair_Ok:
  fixes M N :: "'a::var term"
  assumes "term.Pair M N \<in> \<T>\<lblot>A\<rblot>"
  shows "M \<in> \<T>\<lblot>Ok\<rblot> \<and> N \<in> \<T>\<lblot>Ok\<rblot>"
proof -
  obtain W where W: "term.Pair M N \<rightarrow>* W" "val W" using assms by auto
  obtain V1 V2 where V: "M \<rightarrow>* V1" "N \<rightarrow>* V2" "val V1" "val V2"
    using Pair_betas_inv W beta_star_def by blast
  then show ?thesis by (auto simp: Vals0_def)
qed

lemma ext_App_fix:
  fixes M N :: "'a::var term"
  assumes "App M N \<in> \<T>\<lblot>A\<rblot>"
  shows "M \<in> \<T>\<lblot>OnlyTo Ok B\<rblot>"
proof -
  obtain W where W: "App M N \<rightarrow>* W" "val W" using assms by auto
  obtain k where k: "App M N \<rightarrow>[k] W" using W(1) beta_star_def by blast
  obtain g y R where "M \<rightarrow>* Fix g y R"
    using App_betas_inv[OF k HOL.refl W(2)] by blast
  then show ?thesis
    using fix_in_OnlyTo_Ok[of "Fix g y R"] val.intros(4) by (auto intro: tau_intro)
qed

lemma ext_App2_Ok:
  fixes M N :: "'a::var term"
  assumes "App M N \<in> \<T>\<lblot>A\<rblot>"
  shows "N \<in> \<T>\<lblot>Ok\<rblot>"
proof -
  obtain W where W: "App M N \<rightarrow>* W" "val W" using assms by auto
  obtain V where "N \<rightarrow>* V" "val V"
    using App_betas_inv W beta_star_def by blast
  then show ?thesis by (auto simp: Vals0_def)
qed

lemma ext_AppL:
  fixes M N :: "'a::var term"
  assumes MN: "App M N \<in> \<T>\<lblot>A\<rblot>" and M: "M \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo B A\<rblot>" and clN: "FVars N = {}"
  shows "N \<in> \<T>\<lblot>B\<rblot>"
proof -
  obtain W where W: "App M N \<rightarrow>* W" "val W" "W \<in> \<lblot>A\<rblot>" using MN by (rule tau_dest)
  obtain k where k: "App M N \<rightarrow>[k] W" using W(1) beta_star_def by blast
  obtain g y R V where inv: "M \<rightarrow>* Fix g y R" "N \<rightarrow>* V" "val V"
    "R[V <- y][Fix g y R <- g] \<rightarrow>* W"
    using App_betas_inv[OF k HOL.refl W(2)] by blast
  have clV: "FVars V = {}" using FVars_beta_star inv(2) clN by auto
  have "\<not> M \<Up>"
    using inv(1) vals_are_normal val.intros(4) diverge_xor_normalizes
    unfolding normalizes_def by blast
  then have "M \<in> \<T>\<lblot>OnlyTo B A\<rblot>" using M by auto
  then have Fmem: "Fix g y R \<in> \<lblot>OnlyTo B A\<rblot>"
    using tau_unique inv(1) val.intros(4) by blast
  have "R[V <- y][Fix g y R <- g] \<in> \<T>\<lblot>A\<rblot>"
    using inv(4) W(2,3) by (auto intro: tau_intro)
  then have "V \<in> \<lblot>B\<rblot>" using OnlyTo_unfold[OF Fmem inv(3) clV HOL.refl] by blast
  then show ?thesis using inv(2,3) by (auto intro: tau_intro)
qed

lemma ext_Let:
  fixes M N :: "'a::var term"
  assumes L: "term.Let xy M N \<in> \<T>\<lblot>A\<rblot>" and clM: "FVars M = {}"
  shows "\<exists>V W. M \<rightarrow>* term.Pair V W \<and> val V \<and> val W \<and> FVars V = {} \<and> FVars W = {} \<and>
    N[V <- dfst xy][W <- dsnd xy] \<in> \<T>\<lblot>A\<rblot>"
proof -
  obtain Wf where Wf: "term.Let xy M N \<rightarrow>* Wf" "val Wf" "Wf \<in> \<lblot>A\<rblot>" using L by (rule tau_dest)
  obtain k where k: "term.Let xy M N \<rightarrow>[k] Wf" using Wf(1) beta_star_def by blast
  obtain V W where VW: "M \<rightarrow>* term.Pair V W" "val V" "val W"
    using Let_betas_inv[OF k HOL.refl Wf(2)] by blast
  have clVW: "FVars (term.Pair V W) = {}" using FVars_beta_star[OF VW(1)] clM by auto
  then have clV: "FVars V = {}" and clW: "FVars W = {}" by auto
  have steps: "term.Let xy M N \<rightarrow>* term.Let xy (term.Pair V W) N"
    using Let_beta_star[OF VW(1)] by simp
  have "term.Let xy (term.Pair V W) N \<rightarrow> N[V <- dfst xy][W <- dsnd xy]"
    by (rule beta.Let[OF VW(2,3)]) (use clV in simp)
  then have steps2: "term.Let xy M N \<rightarrow>* N[V <- dfst xy][W <- dsnd xy]"
    using steps beta_star_sums beta_star_def betas.step betas.refl by metis
  have "N[V <- dfst xy][W <- dsnd xy] \<rightarrow>* Wf"
    using beta_star_pass[OF Wf(1) vals_are_normal[OF Wf(2)] steps2] .
  then have "N[V <- dfst xy][W <- dsnd xy] \<in> \<T>\<lblot>A\<rblot>"
    using Wf(2,3) by (auto intro: tau_intro)
  then show ?thesis using VW clV clW by blast
qed

subsection \<open>Valuation bookkeeping\<close>

lemma semantic_judgementI:
  assumes "\<And>\<theta>. closed_val_subst \<theta> \<Longrightarrow> closes \<theta> (L |\<union>| R) \<Longrightarrow>
    (\<forall>\<tau>. \<tau> |\<in>| L \<longrightarrow> satL \<theta> \<tau>) \<Longrightarrow> \<exists>\<tau>. \<tau> |\<in>| R \<and> satR \<theta> \<tau>"
  shows "L \<Turnstile> R"
  using assms unfolding semantic_judgement_def by blast

lemma semantic_judgementD:
  "L \<Turnstile> R \<Longrightarrow> closed_val_subst \<theta> \<Longrightarrow> closes \<theta> (L |\<union>| R) \<Longrightarrow>
   (\<forall>\<tau>. \<tau> |\<in>| L \<longrightarrow> satL \<theta> \<tau>) \<Longrightarrow> \<exists>\<tau>. \<tau> |\<in>| R \<and> satR \<theta> \<tau>"
  unfolding semantic_judgement_def by blast

lemma satL_pair[simp]: "satL \<theta> (M :. A) \<longleftrightarrow> eval \<theta> M \<in> \<T>\<lblot>A\<rblot>"
  by (simp add: satL_def)

lemma satR_pair[simp]: "satR \<theta> (M :. A) \<longleftrightarrow> eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
  by (simp add: satR_def)

lemma satL_satR: "satL \<theta> \<tau> \<Longrightarrow> satR \<theta> \<tau>"
  by (auto simp: satL_def satR_def)

lemma closes_finsert[simp]: "closes \<theta> ((M :. A) ; G) \<longleftrightarrow>
  FVars (eval \<theta> M) = {} \<and> closes \<theta> G"
  by (auto simp: closes_def)

lemma closes_union[simp]: "closes \<theta> (G |\<union>| H) \<longleftrightarrow> closes \<theta> G \<and> closes \<theta> H"
  by (auto simp: closes_def)

lemma closes_member: "closes \<theta> G \<Longrightarrow> (M :. A) |\<in>| G \<Longrightarrow> FVars (eval \<theta> M) = {}"
  unfolding closes_def by (metis fst_conv)

lemma FVarsC_member: "(M :. A) |\<in>| G \<Longrightarrow> FVars M \<subseteq> FVarsC G"
  unfolding FVarsC_def by force

lemma eval_Cons_Var_same: "FVars V = {} \<Longrightarrow> eval ((v, V) # \<theta>) (Var v) = V"
  by (simp add: eval_Cons eval_closed)

lemma eval_Cons_idle: "v \<notin> FVars M \<Longrightarrow> eval ((v, V) # \<theta>) M = eval \<theta> M"
  by (simp add: eval_Cons subst_idle)

lemma eval_Cons2_subst:
  fixes M :: "'a::var term"
  assumes cvs: "closed_val_subst \<theta>" and f: "f \<notin> fst ` set \<theta>" and x: "x \<notin> fst ` set \<theta>"
    and fx: "f \<noteq> x" and clV: "FVars V = {}" and clW: "FVars W = {}"
  shows "eval ((f, V) # (x, W) # \<theta>) M = (eval \<theta> M)[V <- f][W <- x]"
proof -
  have "eval ((f, V) # (x, W) # \<theta>) M = eval \<theta> (M[V <- f][W <- x])"
    by (simp add: eval_Cons)
  also have "\<dots> = (eval \<theta> (M[V <- f]))[W <- x]"
    by (rule eval_usubst[OF cvs x clW])
  also have "\<dots> = (eval \<theta> M)[V <- f][W <- x]"
    using eval_usubst[OF cvs f clV] by simp
  finally show ?thesis .
qed


subsection \<open>The safety-fragment judgement\<close>

text \<open>For Theorem 4.8 we work with a judgement \<open>\<Gamma> \<turnstile>\<^sub>s \<Delta>\<close> that follows the paper's Figure 2
  faithfully and restricts the two fixpoint rules to the safety fragment (Definition 4.6): the
  function types introduced by @{text sFixsR}/@{text sFixnR} must be @{const safe}, which for the
  necessity arrow means a finitely verifiable target. This is slightly more liberal than the
  paper's fragment (which restricts \<^emph>\<open>all\<close> types in a derivation): safety is only needed where
  fixpoints are introduced, so soundness of this system subsumes the paper's Theorem 4.8.

  The rules deviate from the @{const judgement} relation defined earlier in this file in the
  following respects, where the earlier relation disagrees with the paper's Figure 2 (in each case
  the earlier variant is not semantically sound in the sense of Definition 4.2, which can be
  checked by direct countermodels):
  \<^item> in @{text AppR}, @{text LetR} and @{text AppL} the first premise puts the function
    (resp.\ scrutinee) typing on the \<^emph>\<open>right\<close> of the turnstile, as in the paper, not on the left;
  \<^item> @{text LetL2} requires \<^emph>\<open>both\<close> projection premises in a single rule (the paper's \<open>\<forall>i\<close>),
    rather than being split into two rules of one projection each;
  \<^item> @{text PairL} has both component variants (the paper's \<open>i \<in> {1,2}\<close>);
  \<^item> the fixpoint rules require the two bound variables to be distinct (the paper's
    \<open>fix f(x). M\<close> notation presumes this; for \<open>f = x\<close> the semantic argument breaks down).\<close>

inductive sjudgement :: "'var::var typing fset \<Rightarrow> 'var::var typing fset \<Rightarrow> bool" (infix "\<turnstile>\<^sub>s" 10) where
  sId : "(Var x :. A) ; \<Gamma> \<turnstile>\<^sub>s (Var x :. A) ; \<Delta>"
| sZeroR : "\<Gamma> \<turnstile>\<^sub>s (Zero :. Nat) ; \<Delta>"
| sSuccR: "\<Gamma> \<turnstile>\<^sub>s (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (Succ M :. Nat) ; \<Delta>"
| sPredR: "\<Gamma> \<turnstile>\<^sub>s (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (Pred M :. Nat) ; \<Delta>"
| sFixsR: "safe (To A B) \<Longrightarrow> f \<noteq> x \<Longrightarrow>
    (Var f :. To A B) ; (Var x :. A) ; \<Gamma> \<turnstile>\<^sub>s (M :. B) ; \<Delta> \<Longrightarrow>
    {f, x} \<inter> (FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (Fix f x M :. To A B) ; \<Delta>"
| sFixnR: "safe (OnlyTo A B) \<Longrightarrow> f \<noteq> x \<Longrightarrow>
    (Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma> \<turnstile>\<^sub>s (Var x :. A) ; \<Delta> \<Longrightarrow>
    {f, x} \<inter> (FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (Fix f x M :. OnlyTo A B) ; \<Delta>"
| sAppR: "\<Gamma> \<turnstile>\<^sub>s (M :. To B A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (N :. B) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (App M N :. A) ; \<Delta>"
| sPairR: "\<Gamma> \<turnstile>\<^sub>s (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (N :. B) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (Pair M N :. Prod A B) ; \<Delta>"
| sLetR: "\<Gamma> \<turnstile>\<^sub>s (M :. Prod B C) ; \<Delta> \<Longrightarrow>
    (Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma> \<turnstile>\<^sub>s (N :. A) ; \<Delta> \<Longrightarrow>
    dset x \<inter> (FVarsC \<Gamma> \<union> FVarsC \<Delta> \<union> FVars M) = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (Let x M N :. A) ; \<Delta>"
| sIfzR: "\<Gamma> \<turnstile>\<^sub>s (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (P :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (N :. A) ; \<Delta> \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>s (If M N P :. A) ; \<Delta>"
| sDis: "A || B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (M :. B) ; \<Delta> \<Longrightarrow> (M :. A); \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sPairL1: "(M :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Pair M N :. Prod A B) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sPairL2: "(N :. B) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Pair M N :. Prod A B) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sAppL: "\<Gamma> \<turnstile>\<^sub>s (M :. OnlyTo B A) ; \<Delta> \<Longrightarrow> (N :. B) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (App M N :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sSuccL: "(M :. Nat) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Succ M :. Nat) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sPredL: "(M :. Nat) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Pred M :. Nat) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sIfzL1: "(M :. Nat) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sIfzL2: "(N :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (P :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sLetL1: "(N :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> dset x \<inter> (FVars M \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow>
    (Let x M N :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sLetL2: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow>
    (N :. A) ; \<Gamma> \<turnstile>\<^sub>s (Var (dfst x) :. B1) ; \<Delta> \<Longrightarrow>
    (N :. A) ; \<Gamma> \<turnstile>\<^sub>s (Var (dsnd x) :. B2) ; \<Delta> \<Longrightarrow>
    dset x \<inter> (FVars M \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>) = {} \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkVarR: "\<Gamma> \<turnstile>\<^sub>s (Var x :. Ok) ; \<Delta>"
| sOkL: "(M :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkR: "\<Gamma> \<turnstile>\<^sub>s (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s (M :. Ok) ; \<Delta>"
| sOkApL1: "(M :. OnlyTo Ok A) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkApL2: "(N :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkSL: "(M :. Nat); \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Succ M :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkPL: "(M :. Nat) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Pred M :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkPrL_1: "(M1 :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"
| sOkPrL_2: "(M2 :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile>\<^sub>s \<Delta>"

thm sjudgement.induct


subsection \<open>Theorem 4.8: Semantic Soundness\<close>

lemma satR_casesD:
  "(\<exists>\<tau>. \<tau> |\<in>| ((M :. T) ; \<Delta>) \<and> satR \<theta> \<tau>) \<Longrightarrow>
   eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>T\<rblot> \<or> (\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>)"
  by auto

lemma exR_head: "satR \<theta> (M :. T) \<Longrightarrow> \<exists>\<tau>. \<tau> |\<in>| ((M :. T) ; \<Delta>) \<and> satR \<theta> \<tau>"
  by (intro exI[of _ "(M :. T)"] conjI) simp_all

lemma exR_tail: "\<tau> |\<in>| \<Delta> \<Longrightarrow> satR \<theta> \<tau> \<Longrightarrow> \<exists>\<tau>'. \<tau>' |\<in>| ((M :. T) ; \<Delta>) \<and> satR \<theta> \<tau>'"
  by (intro exI[of _ \<tau>] conjI) simp_all

lemma satL_cong: "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>) \<Longrightarrow> satL \<theta>' \<tau> = satL \<theta> \<tau>"
  by (simp add: satL_def)

lemma satR_cong: "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>) \<Longrightarrow> satR \<theta>' \<tau> = satR \<theta> \<tau>"
  by (simp add: satR_def)

lemma FVarsC_member': "\<tau> |\<in>| G \<Longrightarrow> FVars (fst \<tau>) \<subseteq> FVarsC G"
  unfolding FVarsC_def by force

lemma tau_Ok: "M \<in> \<T>\<lblot>A\<rblot> \<Longrightarrow> M \<in> \<T>\<lblot>Ok\<rblot>"
  by (auto simp: Vals0_def)

lemma taubot_Ok: "M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow> M \<in> \<T>\<^sub>\<bottom>\<lblot>Ok\<rblot>"
  using tau_Ok by auto

theorem semantic_soundness: \<comment> \<open>Theorem 4.8\<close>
  fixes \<Gamma> \<Delta> :: "'a::var typing fset"
  assumes "\<Gamma> \<turnstile>\<^sub>s \<Delta>"
  shows "\<Gamma> \<Turnstile> \<Delta>"
  using assms
proof (induction rule: sjudgement.induct)
  case (sId x A \<Gamma> \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume "closed_val_subst \<theta>" "closes \<theta> (((Var x :. A) ; \<Gamma>) |\<union>| ((Var x :. A) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Var x :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "satL \<theta> (Var x :. A)" using satl by auto
    then have "satR \<theta> (Var x :. A)" by (rule satL_satR)
    then show "\<exists>\<tau>. \<tau> |\<in>| ((Var x :. A) ; \<Delta>) \<and> satR \<theta> \<tau>" by (rule exR_head)
  qed
next
  case (sZeroR \<Gamma> \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume "closed_val_subst \<theta>" "closes \<theta> (\<Gamma> |\<union>| ((Zero :. Nat) ; \<Delta>))"
      "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    have "(Zero :: 'a term) \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
      by (intro val_in_taubot) (auto intro: val.intros num.intros)
    then have "satR \<theta> (Zero :. Nat)" by simp
    then show "\<exists>\<tau>. \<tau> |\<in>| ((Zero :. Nat) ; \<Delta>) \<and> satR \<theta> \<tau>" by (rule exR_head)
  qed
next
  case (sSuccR \<Gamma> M \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((Succ M :. Nat) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    have clsP: "closes \<theta> (\<Gamma> |\<union>| ((M :. Nat) ; \<Delta>))" using cls by auto
    from satR_casesD[OF semantic_judgementD[OF sSuccR.IH cvs clsP satl]]
    show "\<exists>\<tau>. \<tau> |\<in>| ((Succ M :. Nat) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (elim disjE)
      assume "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
      then have "satR \<theta> (Succ M :. Nat)" using sem_Succ_Nat by simp
      then show ?thesis by (rule exR_head)
    qed (blast intro: exR_tail)
  qed
next
  case (sPredR \<Gamma> M \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((Pred M :. Nat) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    have clsP: "closes \<theta> (\<Gamma> |\<union>| ((M :. Nat) ; \<Delta>))" using cls by auto
    from satR_casesD[OF semantic_judgementD[OF sPredR.IH cvs clsP satl]]
    show "\<exists>\<tau>. \<tau> |\<in>| ((Pred M :. Nat) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (elim disjE)
      assume "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
      then have "satR \<theta> (Pred M :. Nat)" using sem_Pred_Nat by simp
      then show ?thesis by (rule exR_head)
    qed (blast intro: exR_tail)
  qed
next
  case (sFixsR A B f x \<Gamma> M \<Delta>)
  note safeT = sFixsR.hyps(1) and fx = sFixsR.hyps(2) and freshGD = sFixsR.hyps(4)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((Fix f x M :. To A B) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    define S where "S = FVars (Fix f x M) \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>"
    define \<theta>R where "\<theta>R = filter (\<lambda>p. fst p \<in> S) \<theta>"
    have cvsR: "closed_val_subst \<theta>R" unfolding \<theta>R_def by (rule cvs_filter[OF cvs])
    have domR: "fst ` set \<theta>R \<subseteq> S" unfolding \<theta>R_def by auto
    have fS: "f \<notin> S" and xS: "x \<notin> S" using freshGD unfolding S_def by auto
    have evG: "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evD: "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evF: "eval \<theta>R (Fix f x M) = eval \<theta> (Fix f x M)"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have pushF: "eval \<theta>R (Fix f x M) = Fix f x (eval \<theta>R M)"
      by (rule eval_Fix[OF cvsR]) (use domR fS xS in auto)
    define B0 where "B0 = eval \<theta>R M"
    have eqFB: "Fix f x B0 = eval \<theta> (Fix f x M)" unfolding B0_def by (metis evF pushF)
    have "FVars (Fix f x B0) = {}" unfolding eqFB using cls by auto
    then have clB0: "FVars B0 \<subseteq> {f, x}" by auto
    show "\<exists>\<tau>. \<tau> |\<in>| ((Fix f x M :. To A B) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis using exR_tail by blast
    next
      case False
      have Hcol: "B0[V <- f][W <- x] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
        if vV: "val V" and clV: "FVars V = {}" and iV: "V \<in> \<lblot>To A B\<rblot>"
          and vW: "val W" and clW: "FVars W = {}" and iW: "W \<in> \<lblot>A\<rblot>"
        for V W :: "'a term"
      proof -
        define \<theta>' where "\<theta>' = (f, V) # (x, W) # \<theta>R"
        have cvs': "closed_val_subst \<theta>'"
          unfolding \<theta>'_def using cvsR vV clV vW clW by (auto simp: cvs_Cons)
        have evf: "eval \<theta>' (Var f) = V"
          unfolding \<theta>'_def by (rule eval_Cons_Var_same[OF clV])
        have evx: "eval \<theta>' (Var x) = W"
          unfolding \<theta>'_def using fx clW
          by (simp add: eval_Cons eval_Cons_Var_same eval_closed)
        have evM: "eval \<theta>' M = B0[V <- f][W <- x]"
          unfolding \<theta>'_def B0_def
          by (rule eval_Cons2_subst[OF cvsR _ _ fx clV clW]) (use domR fS xS in auto)
        have evG': "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
        proof -
          fix \<tau> assume m: "\<tau> |\<in>| \<Gamma>"
          have "f \<notin> FVars (fst \<tau>)" "x \<notin> FVars (fst \<tau>)"
            using FVarsC_member'[OF m] freshGD by auto
          then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
            unfolding \<theta>'_def by (simp add: eval_Cons_idle)
          then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evG[OF m] by simp
        qed
        have evD': "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
        proof -
          fix \<tau> assume m: "\<tau> |\<in>| \<Delta>"
          have "f \<notin> FVars (fst \<tau>)" "x \<notin> FVars (fst \<tau>)"
            using FVarsC_member'[OF m] freshGD by auto
          then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
            unfolding \<theta>'_def by (simp add: eval_Cons_idle)
          then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evD[OF m] by simp
        qed
        have satl': "\<forall>\<tau>. \<tau> |\<in>| ((Var f :. To A B) ; (Var x :. A) ; \<Gamma>) \<longrightarrow> satL \<theta>' \<tau>"
        proof (intro allI impI)
          fix \<tau> assume "\<tau> |\<in>| ((Var f :. To A B) ; (Var x :. A) ; \<Gamma>)"
          then consider "\<tau> = (Var f :. To A B)" | "\<tau> = (Var x :. A)" | "\<tau> |\<in>| \<Gamma>" by auto
          then show "satL \<theta>' \<tau>"
          proof cases
            case 1
            show ?thesis unfolding 1 satL_pair evf using val_tau_iff[OF vV] iV by blast
          next
            case 2
            show ?thesis unfolding 2 satL_pair evx using val_tau_iff[OF vW] iW by blast
          next
            case 3
            then show ?thesis using satl satL_cong[OF evG'[OF 3]] by blast
          qed
        qed
        have cls': "closes \<theta>' (((Var f :. To A B) ; (Var x :. A) ; \<Gamma>) |\<union>| ((M :. B) ; \<Delta>))"
        proof -
          have "FVars (eval \<theta>' (Var f)) = {}" using evf clV by simp
          moreover have "FVars (eval \<theta>' (Var x)) = {}" using evx clW by simp
          moreover have "FVars (eval \<theta>' M) = {}"
            unfolding evM using clB0 clV clW fx by (auto simp: FVars_usubst split: if_splits)
          moreover have "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
            using evG' cls by (auto simp: closes_def)
          moreover have "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
            using evD' cls by (auto simp: closes_def)
          ultimately show ?thesis by (auto simp: closes_def)
        qed
        from semantic_judgementD[OF sFixsR.IH cvs' cls' satl']
        obtain \<tau> where t: "\<tau> |\<in>| ((M :. B) ; \<Delta>)" "satR \<theta>' \<tau>" by blast
        show ?thesis
        proof (cases "\<tau> |\<in>| \<Delta>")
          case True
          then have "satR \<theta> \<tau>" using t(2) satR_cong[OF evD'[OF True]] by simp
          then show ?thesis using False True by blast
        next
          case False
          then have "\<tau> = (M :. B)" using t(1) by auto
          then show ?thesis using t(2) evM by simp
        qed
      qed
      have H: "Lam x (B0[V <- f]) \<in> \<lblot>To A B\<rblot>"
        if vV: "val V" and clV: "FVars V = {}" and iV: "V \<in> \<lblot>To A B\<rblot>" for V :: "'a term"
      proof -
        obtain g where g: "g \<notin> FVars (B0[V <- f]) \<union> {x}"
          using fresh_finite[of "FVars (B0[V <- f]) \<union> {x}"] by auto
        have Le: "Lam x (B0[V <- f]) = Fix g x (B0[V <- f])"
          by (rule Lam_eq) (use g in auto)
        have bodyprop: "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow> U \<in> \<lblot>A\<rblot> \<longrightarrow>
          (B0[V <- f])[U <- x][Fix g x (B0[V <- f]) <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
        proof (intro ballI impI)
          fix U :: "'a term" assume "U \<in> Vals0" and clU: "FVars U = {}" and iU: "U \<in> \<lblot>A\<rblot>"
          then have vU: "val U" by (simp add: Vals0_def)
          have "g \<notin> FVars ((B0[V <- f])[U <- x])"
            using g clU by (auto simp: FVars_usubst split: if_splits)
          then have "(B0[V <- f])[U <- x][Fix g x (B0[V <- f]) <- g] = (B0[V <- f])[U <- x]"
            by (rule subst_idle)
          then show "(B0[V <- f])[U <- x][Fix g x (B0[V <- f]) <- g] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
            using Hcol[OF vV clV iV vU clU iU] by simp
        qed
        show ?thesis unfolding Le type_semantics.simps using bodyprop by blast
      qed
      have FB: "Fix f x B0 \<in> \<T>\<^sub>\<bottom>\<lblot>To A B\<rblot>"
        by (rule b9_To[OF fx clB0 safeT]) (rule H)
      have "satR \<theta> (Fix f x M :. To A B)"
        unfolding satR_pair eqFB[symmetric] by (rule FB)
      then show ?thesis by (rule exR_head)
    qed
  qed
next
  case (sFixnR A B f x M \<Gamma> \<Delta>)
  note safeT = sFixnR.hyps(1) and fx = sFixnR.hyps(2) and freshGD = sFixnR.hyps(4)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((Fix f x M :. OnlyTo A B) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    define S where "S = FVars (Fix f x M) \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>"
    define \<theta>R where "\<theta>R = filter (\<lambda>p. fst p \<in> S) \<theta>"
    have cvsR: "closed_val_subst \<theta>R" unfolding \<theta>R_def by (rule cvs_filter[OF cvs])
    have domR: "fst ` set \<theta>R \<subseteq> S" unfolding \<theta>R_def by auto
    have fS: "f \<notin> S" and xS: "x \<notin> S" using freshGD unfolding S_def by auto
    have evG: "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evD: "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evF: "eval \<theta>R (Fix f x M) = eval \<theta> (Fix f x M)"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have pushF: "eval \<theta>R (Fix f x M) = Fix f x (eval \<theta>R M)"
      by (rule eval_Fix[OF cvsR]) (use domR fS xS in auto)
    define B0 where "B0 = eval \<theta>R M"
    have eqFB: "Fix f x B0 = eval \<theta> (Fix f x M)" unfolding B0_def by (metis evF pushF)
    have "FVars (Fix f x B0) = {}" unfolding eqFB using cls by auto
    then have clB0: "FVars B0 \<subseteq> {f, x}" by auto
    show "\<exists>\<tau>. \<tau> |\<in>| ((Fix f x M :. OnlyTo A B) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis using exR_tail by blast
    next
      case False
      have Hcol: "W \<in> \<lblot>A\<rblot>"
        if vV: "val V" and clV: "FVars V = {}" and iV: "V \<in> \<lblot>OnlyTo A B\<rblot>"
          and vW: "val W" and clW: "FVars W = {}"
          and mem: "B0[V <- f][W <- x] \<in> \<T>\<lblot>B\<rblot>"
        for V W :: "'a term"
      proof -
        define \<theta>' where "\<theta>' = (f, V) # (x, W) # \<theta>R"
        have cvs': "closed_val_subst \<theta>'"
          unfolding \<theta>'_def using cvsR vV clV vW clW by (auto simp: cvs_Cons)
        have evf: "eval \<theta>' (Var f) = V"
          unfolding \<theta>'_def by (rule eval_Cons_Var_same[OF clV])
        have evx: "eval \<theta>' (Var x) = W"
          unfolding \<theta>'_def using fx clW
          by (simp add: eval_Cons eval_Cons_Var_same eval_closed)
        have evM: "eval \<theta>' M = B0[V <- f][W <- x]"
          unfolding \<theta>'_def B0_def
          by (rule eval_Cons2_subst[OF cvsR _ _ fx clV clW]) (use domR fS xS in auto)
        have evG': "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
        proof -
          fix \<tau> assume m: "\<tau> |\<in>| \<Gamma>"
          have "f \<notin> FVars (fst \<tau>)" "x \<notin> FVars (fst \<tau>)"
            using FVarsC_member'[OF m] freshGD by auto
          then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
            unfolding \<theta>'_def by (simp add: eval_Cons_idle)
          then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evG[OF m] by simp
        qed
        have evD': "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
        proof -
          fix \<tau> assume m: "\<tau> |\<in>| \<Delta>"
          have "f \<notin> FVars (fst \<tau>)" "x \<notin> FVars (fst \<tau>)"
            using FVarsC_member'[OF m] freshGD by auto
          then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
            unfolding \<theta>'_def by (simp add: eval_Cons_idle)
          then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evD[OF m] by simp
        qed
        have satl': "\<forall>\<tau>. \<tau> |\<in>| ((Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma>) \<longrightarrow> satL \<theta>' \<tau>"
        proof (intro allI impI)
          fix \<tau> assume "\<tau> |\<in>| ((Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma>)"
          then consider "\<tau> = (Var f :. OnlyTo A B)" | "\<tau> = (M :. B)" | "\<tau> |\<in>| \<Gamma>" by auto
          then show "satL \<theta>' \<tau>"
          proof cases
            case 1
            show ?thesis unfolding 1 satL_pair evf using val_tau_iff[OF vV] iV by blast
          next
            case 2
            show ?thesis unfolding 2 satL_pair evM by (rule mem)
          next
            case 3
            then show ?thesis using satl satL_cong[OF evG'[OF 3]] by blast
          qed
        qed
        have cls': "closes \<theta>' (((Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma>) |\<union>| ((Var x :. A) ; \<Delta>))"
        proof -
          have "FVars (eval \<theta>' (Var f)) = {}" using evf clV by simp
          moreover have "FVars (eval \<theta>' (Var x)) = {}" using evx clW by simp
          moreover have "FVars (eval \<theta>' M) = {}"
            unfolding evM using clB0 clV clW fx by (auto simp: FVars_usubst split: if_splits)
          moreover have "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
            using evG' cls by (auto simp: closes_def)
          moreover have "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
            using evD' cls by (auto simp: closes_def)
          ultimately show ?thesis by (auto simp: closes_def)
        qed
        from semantic_judgementD[OF sFixnR.IH cvs' cls' satl']
        obtain \<tau> where t: "\<tau> |\<in>| ((Var x :. A) ; \<Delta>)" "satR \<theta>' \<tau>" by blast
        show ?thesis
        proof (cases "\<tau> |\<in>| \<Delta>")
          case True
          then have "satR \<theta> \<tau>" using t(2) satR_cong[OF evD'[OF True]] by simp
          then show ?thesis using False True by blast
        next
          case False
          then have "\<tau> = (Var x :. A)" using t(1) by auto
          then have "W \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>" using t(2) evx by simp
          then show ?thesis using val_taubot_iff[OF vW] by simp
        qed
      qed
      have H: "Lam x (B0[V <- f]) \<in> \<lblot>OnlyTo A B\<rblot>"
        if vV: "val V" and clV: "FVars V = {}" and iV: "V \<in> \<lblot>OnlyTo A B\<rblot>" for V :: "'a term"
      proof -
        obtain g where g: "g \<notin> FVars (B0[V <- f]) \<union> {x}"
          using fresh_finite[of "FVars (B0[V <- f]) \<union> {x}"] by auto
        have Le: "Lam x (B0[V <- f]) = Fix g x (B0[V <- f])"
          by (rule Lam_eq) (use g in auto)
        have bodyprop: "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow>
          (B0[V <- f])[U <- x][Fix g x (B0[V <- f]) <- g] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> U \<in> \<lblot>A\<rblot>"
        proof (intro ballI impI)
          fix U :: "'a term" assume "U \<in> Vals0" and clU: "FVars U = {}"
            and mem: "(B0[V <- f])[U <- x][Fix g x (B0[V <- f]) <- g] \<in> \<T>\<lblot>B\<rblot>"
          then have vU: "val U" by (simp add: Vals0_def)
          have "g \<notin> FVars ((B0[V <- f])[U <- x])"
            using g clU by (auto simp: FVars_usubst split: if_splits)
          then have "(B0[V <- f])[U <- x][Fix g x (B0[V <- f]) <- g] = (B0[V <- f])[U <- x]"
            by (rule subst_idle)
          then show "U \<in> \<lblot>A\<rblot>"
            using Hcol[OF vV clV iV vU clU] mem by simp
        qed
        show ?thesis unfolding Le type_semantics.simps using bodyprop by blast
      qed
      have FB: "Fix f x B0 \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo A B\<rblot>"
        by (rule b9_OnlyTo[OF fx clB0 safeT]) (rule H)
      have "satR \<theta> (Fix f x M :. OnlyTo A B)"
        unfolding satR_pair eqFB[symmetric] by (rule FB)
      then show ?thesis by (rule exR_head)
    qed
  qed
next
  case (sAppR \<Gamma> M B A \<Delta> N)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((App M N :. A) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    show "\<exists>\<tau>. \<tau> |\<in>| ((App M N :. A) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis using exR_tail by blast
    next
      case False
      have clsM: "closes \<theta> (\<Gamma> |\<union>| ((M :. To B A) ; \<Delta>))" using cls by auto
      have clsN: "closes \<theta> (\<Gamma> |\<union>| ((N :. B) ; \<Delta>))" using cls by auto
      have M: "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>To B A\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sAppR.IH(1) cvs clsM satl]] False by blast
      have N: "eval \<theta> N \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sAppR.IH(2) cvs clsN satl]] False by blast
      have clN: "FVars (eval \<theta> N) = {}" using cls by auto
      have "satR \<theta> (App M N :. A)" using sem_App[OF M N clN] by simp
      then show ?thesis by (rule exR_head)
    qed
  qed
next
  case (sPairR \<Gamma> M A \<Delta> N B)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((Pair M N :. Prod A B) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    show "\<exists>\<tau>. \<tau> |\<in>| ((term.Pair M N :. Prod A B) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis using exR_tail by blast
    next
      case False
      have clsM: "closes \<theta> (\<Gamma> |\<union>| ((M :. A) ; \<Delta>))" using cls by auto
      have clsN: "closes \<theta> (\<Gamma> |\<union>| ((N :. B) ; \<Delta>))" using cls by auto
      have M: "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sPairR.IH(1) cvs clsM satl]] False by blast
      have N: "eval \<theta> N \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sPairR.IH(2) cvs clsN satl]] False by blast
      have "satR \<theta> (term.Pair M N :. Prod A B)" using sem_Pair[OF M N] by simp
      then show ?thesis by (rule exR_head)
    qed
  qed
next
  case (sLetR \<Gamma> M B C \<Delta> x N A)
  note freshGD = sLetR.hyps(3)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((term.Let x M N :. A) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    define S where "S = FVars (term.Let x M N) \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>"
    define \<theta>R where "\<theta>R = filter (\<lambda>p. fst p \<in> S) \<theta>"
    have cvsR: "closed_val_subst \<theta>R" unfolding \<theta>R_def by (rule cvs_filter[OF cvs])
    have domR: "fst ` set \<theta>R \<subseteq> S" unfolding \<theta>R_def by auto
    have dS: "dset x \<inter> S = {}" using freshGD unfolding S_def by auto
    have evG: "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evD: "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evL: "eval \<theta>R (term.Let x M N) = eval \<theta> (term.Let x M N)"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have evMag: "eval \<theta>R M = eval \<theta> M"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have pushL: "eval \<theta>R (term.Let x M N) = term.Let x (eval \<theta>R M) (eval \<theta>R N)"
      by (rule eval_Let[OF cvsR]) (use domR dS in auto)
    have clLet: "FVars (eval \<theta>R (term.Let x M N)) = {}" using cls evL by auto
    have clM: "FVars (eval \<theta>R M) = {}" using clLet pushL by auto
    have clN: "FVars (eval \<theta>R N) \<subseteq> dset x" using clLet pushL by auto
    show "\<exists>\<tau>. \<tau> |\<in>| ((term.Let x M N :. A) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis using exR_tail by blast
    next
      case False
      have noD: "\<not> (\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta>R \<tau>)"
        using False satR_cong evD by blast
      have clsM': "closes \<theta>R (\<Gamma> |\<union>| ((M :. Prod B C) ; \<Delta>))"
        using cls evG evD evMag clM by (auto simp: closes_def)
      have satlR: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta>R \<tau>"
        using satl satL_cong evG by blast
      have Mmem: "eval \<theta>R M \<in> \<T>\<^sub>\<bottom>\<lblot>Prod B C\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sLetR.IH(1) cvsR clsM' satlR]] noD by blast
      have body: "(eval \<theta>R N)[V <- dfst x][W <- dsnd x] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        if vV: "val V" and vW: "val W" and clV: "FVars V = {}" and clW: "FVars W = {}"
          and iV: "V \<in> \<lblot>B\<rblot>" and iW: "W \<in> \<lblot>C\<rblot>"
        for V W :: "'a term"
      proof -
        define \<theta>' where "\<theta>' = (dfst x, V) # (dsnd x, W) # \<theta>R"
        have cvs': "closed_val_subst \<theta>'"
          unfolding \<theta>'_def using cvsR vV clV vW clW by (auto simp: cvs_Cons)
        have evfst: "eval \<theta>' (Var (dfst x)) = V"
          unfolding \<theta>'_def by (rule eval_Cons_Var_same[OF clV])
        have evsnd: "eval \<theta>' (Var (dsnd x)) = W"
          unfolding \<theta>'_def using dfst_neq_dsnd[of x] clW
          by (simp add: eval_Cons eval_Cons_Var_same eval_closed)
        have dfstR: "dfst x \<notin> fst ` set \<theta>R" and dsndR: "dsnd x \<notin> fst ` set \<theta>R"
          using domR dS dsel_dset[of x] by blast+
        have evN: "eval \<theta>' N = (eval \<theta>R N)[V <- dfst x][W <- dsnd x]"
          unfolding \<theta>'_def
          by (rule eval_Cons2_subst[OF cvsR dfstR dsndR dfst_neq_dsnd clV clW])
        have evG': "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
        proof -
          fix \<tau> assume m: "\<tau> |\<in>| \<Gamma>"
          have "dfst x \<notin> FVars (fst \<tau>)" "dsnd x \<notin> FVars (fst \<tau>)"
            using FVarsC_member'[OF m] freshGD dsel_dset[of x] by blast+
          then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
            unfolding \<theta>'_def by (simp add: eval_Cons_idle)
          then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evG[OF m] by simp
        qed
        have evD': "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
        proof -
          fix \<tau> assume m: "\<tau> |\<in>| \<Delta>"
          have "dfst x \<notin> FVars (fst \<tau>)" "dsnd x \<notin> FVars (fst \<tau>)"
            using FVarsC_member'[OF m] freshGD dsel_dset[of x] by blast+
          then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
            unfolding \<theta>'_def by (simp add: eval_Cons_idle)
          then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evD[OF m] by simp
        qed
        have satl': "\<forall>\<tau>. \<tau> |\<in>| ((Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma>) \<longrightarrow> satL \<theta>' \<tau>"
        proof (intro allI impI)
          fix \<tau> assume "\<tau> |\<in>| ((Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma>)"
          then consider "\<tau> = (Var (dfst x) :. B)" | "\<tau> = (Var (dsnd x) :. C)" | "\<tau> |\<in>| \<Gamma>" by auto
          then show "satL \<theta>' \<tau>"
          proof cases
            case 1
            show ?thesis unfolding 1 satL_pair evfst using val_tau_iff[OF vV] iV by blast
          next
            case 2
            show ?thesis unfolding 2 satL_pair evsnd using val_tau_iff[OF vW] iW by blast
          next
            case 3
            then show ?thesis using satl satL_cong[OF evG'[OF 3]] by blast
          qed
        qed
        have cls': "closes \<theta>' (((Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma>) |\<union>| ((N :. A) ; \<Delta>))"
        proof -
          have "FVars (eval \<theta>' (Var (dfst x))) = {}" using evfst clV by simp
          moreover have "FVars (eval \<theta>' (Var (dsnd x))) = {}" using evsnd clW by simp
          moreover have "FVars (eval \<theta>' N) = {}"
            unfolding evN using clN clV clW dfst_neq_dsnd[of x] dset_alt[of x]
            by (auto simp: FVars_usubst split: if_splits)
          moreover have "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
            using evG' cls by (auto simp: closes_def)
          moreover have "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
            using evD' cls by (auto simp: closes_def)
          ultimately show ?thesis by (auto simp: closes_def)
        qed
        from semantic_judgementD[OF sLetR.IH(2) cvs' cls' satl']
        obtain \<tau> where t: "\<tau> |\<in>| ((N :. A) ; \<Delta>)" "satR \<theta>' \<tau>" by blast
        show ?thesis
        proof (cases "\<tau> |\<in>| \<Delta>")
          case True
          then have "satR \<theta> \<tau>" using t(2) satR_cong[OF evD'[OF True]] by simp
          then show ?thesis using False True by blast
        next
          case False
          then have "\<tau> = (N :. A)" using t(1) by auto
          then show ?thesis using t(2) evN by simp
        qed
      qed
      have SL: "term.Let x (eval \<theta>R M) (eval \<theta>R N) \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        by (rule sem_Let[OF Mmem clM]) (rule body)
      have eqL: "term.Let x (eval \<theta>R M) (eval \<theta>R N) = eval \<theta> (term.Let x M N)"
        by (metis evL pushL)
      have "satR \<theta> (term.Let x M N :. A)"
        unfolding satR_pair eqL[symmetric] by (rule SL)
      then show ?thesis by (rule exR_head)
    qed
  qed
next
  case (sIfzR \<Gamma> M \<Delta> P A N)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((If M N P :. A) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    show "\<exists>\<tau>. \<tau> |\<in>| ((If M N P :. A) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis using exR_tail by blast
    next
      case False
      have clsM: "closes \<theta> (\<Gamma> |\<union>| ((M :. Nat) ; \<Delta>))" using cls by auto
      have clsN: "closes \<theta> (\<Gamma> |\<union>| ((N :. A) ; \<Delta>))" using cls by auto
      have clsP: "closes \<theta> (\<Gamma> |\<union>| ((P :. A) ; \<Delta>))" using cls by auto
      have M: "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sIfzR.IH(1) cvs clsM satl]] False by blast
      have P: "eval \<theta> P \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sIfzR.IH(2) cvs clsP satl]] False by blast
      have N: "eval \<theta> N \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
        using satR_casesD[OF semantic_judgementD[OF sIfzR.IH(3) cvs clsN satl]] False by blast
      have "satR \<theta> (If M N P :. A)" using sem_If[OF M N P] by simp
      then show ?thesis by (rule exR_head)
    qed
  qed
next
  case (sDis A B \<Gamma> M \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((M :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((M :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have satlG: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have MA: "eval \<theta> M \<in> \<T>\<lblot>A\<rblot>" using satl by auto
    have clsP: "closes \<theta> (\<Gamma> |\<union>| ((M :. B) ; \<Delta>))" using cls by auto
    from satR_casesD[OF semantic_judgementD[OF sDis.IH cvs clsP satlG]]
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
    proof (elim disjE)
      assume MB: "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>"
      obtain V where V: "eval \<theta> M \<rightarrow>* V" "val V" "V \<in> \<lblot>A\<rblot>" using MA by (rule tau_dest)
      have "\<not> (eval \<theta> M) \<Up>"
        using V(1,2) vals_are_normal diverge_xor_normalizes normalizes_def by blast
      then have "eval \<theta> M \<in> \<T>\<lblot>B\<rblot>" using MB by auto
      then have "V \<in> \<lblot>B\<rblot>" using tau_unique V(1,2) by blast
      then have False using disjoint_sem[OF sDis.hyps(1) V(3)] by blast
      then show ?thesis ..
    qed blast
  qed
next
  case (sPairL1 M A \<Gamma> \<Delta> N B)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Pair M N :. Prod A B) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Pair M N :. Prod A B) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (term.Pair M N) \<in> \<T>\<lblot>Prod A B\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>A\<rblot>" unfolding eval_Pair using ext_Pair by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. A) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sPairL1.IH cvs clsP satlP] .
  qed
next
  case (sPairL2 N B \<Gamma> \<Delta> M A)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Pair M N :. Prod A B) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Pair M N :. Prod A B) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (term.Pair M N) \<in> \<T>\<lblot>Prod A B\<rblot>" using satl by auto
    then have "eval \<theta> N \<in> \<T>\<lblot>B\<rblot>" unfolding eval_Pair using ext_Pair by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((N :. B) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((N :. B) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sPairL2.IH cvs clsP satlP] .
  qed
next
  case (sAppL \<Gamma> M B A \<Delta> N)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((App M N :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((App M N :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have satlG: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have head: "eval \<theta> (App M N) \<in> \<T>\<lblot>A\<rblot>" using satl by auto
    have clsM: "closes \<theta> (\<Gamma> |\<union>| ((M :. OnlyTo B A) ; \<Delta>))" using cls by auto
    from satR_casesD[OF semantic_judgementD[OF sAppL.IH(1) cvs clsM satlG]]
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
    proof (elim disjE)
      assume Mm: "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo B A\<rblot>"
      have clN: "FVars (eval \<theta> N) = {}" using cls by auto
      have "eval \<theta> N \<in> \<T>\<lblot>B\<rblot>"
        using ext_AppL[OF _ Mm clN] head by simp
      then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((N :. B) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satlG by auto
      have clsP: "closes \<theta> (((N :. B) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
      show ?thesis using semantic_judgementD[OF sAppL.IH(2) cvs clsP satlP] .
    qed blast
  qed
next
  case (sSuccL M \<Gamma> \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Succ M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Succ M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (Succ M) \<in> \<T>\<lblot>Nat\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>Nat\<rblot>" unfolding eval_Succ using ext_Succ by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sSuccL.IH cvs clsP satlP] .
  qed
next
  case (sPredL M \<Gamma> \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Pred M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Pred M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (Pred M) \<in> \<T>\<lblot>Nat\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>Nat\<rblot>" unfolding eval_Pred using ext_Pred by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sPredL.IH cvs clsP satlP] .
  qed
next
  case (sIfzL1 M \<Gamma> \<Delta> N P A)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((If M N P :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((If M N P :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (If M N P) \<in> \<T>\<lblot>A\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>Nat\<rblot>" unfolding eval_If using ext_If1 by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sIfzL1.IH cvs clsP satlP] .
  qed
next
  case (sIfzL2 N A \<Gamma> \<Delta> P M)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((If M N P :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((If M N P :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (If M N P) \<in> \<T>\<lblot>A\<rblot>" using satl by auto
    then have "eval \<theta> N \<in> \<T>\<lblot>A\<rblot> \<or> eval \<theta> P \<in> \<T>\<lblot>A\<rblot>" unfolding eval_If using ext_If2 by blast
    then show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
    proof (elim disjE)
      assume "eval \<theta> N \<in> \<T>\<lblot>A\<rblot>"
      then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((N :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
      have clsP: "closes \<theta> (((N :. A) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
      show ?thesis using semantic_judgementD[OF sIfzL2.IH(1) cvs clsP satlP] .
    next
      assume "eval \<theta> P \<in> \<T>\<lblot>A\<rblot>"
      then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((P :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
      have clsP: "closes \<theta> (((P :. A) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
      show ?thesis using semantic_judgementD[OF sIfzL2.IH(2) cvs clsP satlP] .
    qed
  qed
next
  case (sLetL1 N A \<Gamma> \<Delta> x M)
  note freshGD = sLetL1.hyps(2)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((term.Let x M N :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((term.Let x M N :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    define S where "S = FVars (term.Let x M N) \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>"
    define \<theta>R where "\<theta>R = filter (\<lambda>p. fst p \<in> S) \<theta>"
    have cvsR: "closed_val_subst \<theta>R" unfolding \<theta>R_def by (rule cvs_filter[OF cvs])
    have domR: "fst ` set \<theta>R \<subseteq> S" unfolding \<theta>R_def by auto
    have dS: "dset x \<inter> S = {}" using freshGD unfolding S_def by auto
    have evG: "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evD: "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evL: "eval \<theta>R (term.Let x M N) = eval \<theta> (term.Let x M N)"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have pushL: "eval \<theta>R (term.Let x M N) = term.Let x (eval \<theta>R M) (eval \<theta>R N)"
      by (rule eval_Let[OF cvsR]) (use domR dS in auto)
    have clLet: "FVars (eval \<theta>R (term.Let x M N)) = {}" using cls evL by auto
    have clM: "FVars (eval \<theta>R M) = {}" using clLet pushL by auto
    have clN: "FVars (eval \<theta>R N) \<subseteq> dset x" using clLet pushL by auto
    have head: "eval \<theta>R (term.Let x M N) \<in> \<T>\<lblot>A\<rblot>" using satl evL by auto
    then have headP: "term.Let x (eval \<theta>R M) (eval \<theta>R N) \<in> \<T>\<lblot>A\<rblot>" using pushL by simp
    obtain V W where VW: "eval \<theta>R M \<rightarrow>* term.Pair V W" "val V" "val W"
      "FVars V = {}" "FVars W = {}"
      "(eval \<theta>R N)[V <- dfst x][W <- dsnd x] \<in> \<T>\<lblot>A\<rblot>"
      using ext_Let[OF headP clM] by blast
    define \<theta>' where "\<theta>' = (dfst x, V) # (dsnd x, W) # \<theta>R"
    have cvs': "closed_val_subst \<theta>'"
      unfolding \<theta>'_def using cvsR VW(2,3,4,5) by (auto simp: cvs_Cons)
    have dfstR: "dfst x \<notin> fst ` set \<theta>R" and dsndR: "dsnd x \<notin> fst ` set \<theta>R"
      using domR dS dsel_dset[of x] by blast+
    have evN: "eval \<theta>' N = (eval \<theta>R N)[V <- dfst x][W <- dsnd x]"
      unfolding \<theta>'_def
      by (rule eval_Cons2_subst[OF cvsR dfstR dsndR dfst_neq_dsnd VW(4,5)])
    have evG': "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
    proof -
      fix \<tau> assume m: "\<tau> |\<in>| \<Gamma>"
      have "dfst x \<notin> FVars (fst \<tau>)" "dsnd x \<notin> FVars (fst \<tau>)"
        using FVarsC_member'[OF m] freshGD dsel_dset[of x] by blast+
      then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
        unfolding \<theta>'_def by (simp add: eval_Cons_idle)
      then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evG[OF m] by simp
    qed
    have evD': "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
    proof -
      fix \<tau> assume m: "\<tau> |\<in>| \<Delta>"
      have "dfst x \<notin> FVars (fst \<tau>)" "dsnd x \<notin> FVars (fst \<tau>)"
        using FVarsC_member'[OF m] freshGD dsel_dset[of x] by blast+
      then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
        unfolding \<theta>'_def by (simp add: eval_Cons_idle)
      then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evD[OF m] by simp
    qed
    have satl': "\<forall>\<tau>. \<tau> |\<in>| ((N :. A) ; \<Gamma>) \<longrightarrow> satL \<theta>' \<tau>"
    proof (intro allI impI)
      fix \<tau> assume "\<tau> |\<in>| ((N :. A) ; \<Gamma>)"
      then consider "\<tau> = (N :. A)" | "\<tau> |\<in>| \<Gamma>" by auto
      then show "satL \<theta>' \<tau>"
      proof cases
        case 1
        show ?thesis unfolding 1 satL_pair evN by (rule VW(6))
      next
        case 2
        then show ?thesis using satl satL_cong[OF evG'[OF 2]] by blast
      qed
    qed
    have cls': "closes \<theta>' (((N :. A) ; \<Gamma>) |\<union>| \<Delta>)"
    proof -
      have "FVars (eval \<theta>' N) = {}"
        unfolding evN using clN VW(4,5) dfst_neq_dsnd[of x] dset_alt[of x]
        by (auto simp: FVars_usubst split: if_splits)
      moreover have "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
        using evG' cls by (auto simp: closes_def)
      moreover have "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
        using evD' cls by (auto simp: closes_def)
      ultimately show ?thesis by (auto simp: closes_def)
    qed
    from semantic_judgementD[OF sLetL1.IH cvs' cls' satl']
    obtain \<tau> where t: "\<tau> |\<in>| \<Delta>" "satR \<theta>' \<tau>" by blast
    then have "satR \<theta> \<tau>" using satR_cong[OF evD'[OF t(1)]] by simp
    then show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>" using t(1) by blast
  qed
next
  case (sLetL2 M B1 B2 \<Gamma> \<Delta> N A x)
  note freshGD = sLetL2.hyps(4)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((term.Let x M N :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((term.Let x M N :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    define S where "S = FVars (term.Let x M N) \<union> FVarsC \<Gamma> \<union> FVarsC \<Delta>"
    define \<theta>R where "\<theta>R = filter (\<lambda>p. fst p \<in> S) \<theta>"
    have cvsR: "closed_val_subst \<theta>R" unfolding \<theta>R_def by (rule cvs_filter[OF cvs])
    have domR: "fst ` set \<theta>R \<subseteq> S" unfolding \<theta>R_def by auto
    have dS: "dset x \<inter> S = {}" using freshGD unfolding S_def by auto
    have evG: "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evD: "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>R (fst \<tau>) = eval \<theta> (fst \<tau>)"
      unfolding \<theta>R_def
      by (rule eval_filter[OF cvs]) (use FVarsC_member' in \<open>fastforce simp: S_def\<close>)
    have evL: "eval \<theta>R (term.Let x M N) = eval \<theta> (term.Let x M N)"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have evMag: "eval \<theta>R M = eval \<theta> M"
      unfolding \<theta>R_def by (rule eval_filter[OF cvs]) (auto simp: S_def)
    have pushL: "eval \<theta>R (term.Let x M N) = term.Let x (eval \<theta>R M) (eval \<theta>R N)"
      by (rule eval_Let[OF cvsR]) (use domR dS in auto)
    have clLet: "FVars (eval \<theta>R (term.Let x M N)) = {}" using cls evL by auto
    have clM: "FVars (eval \<theta>R M) = {}" using clLet pushL by auto
    have clN: "FVars (eval \<theta>R N) \<subseteq> dset x" using clLet pushL by auto
    have head: "eval \<theta>R (term.Let x M N) \<in> \<T>\<lblot>A\<rblot>" using satl evL by auto
    then have headP: "term.Let x (eval \<theta>R M) (eval \<theta>R N) \<in> \<T>\<lblot>A\<rblot>" using pushL by simp
    obtain V W where VW: "eval \<theta>R M \<rightarrow>* term.Pair V W" "val V" "val W"
      "FVars V = {}" "FVars W = {}"
      "(eval \<theta>R N)[V <- dfst x][W <- dsnd x] \<in> \<T>\<lblot>A\<rblot>"
      using ext_Let[OF headP clM] by blast
    define \<theta>' where "\<theta>' = (dfst x, V) # (dsnd x, W) # \<theta>R"
    have cvs': "closed_val_subst \<theta>'"
      unfolding \<theta>'_def using cvsR VW(2,3,4,5) by (auto simp: cvs_Cons)
    have evfst: "eval \<theta>' (Var (dfst x)) = V"
      unfolding \<theta>'_def by (rule eval_Cons_Var_same[OF VW(4)])
    have evsnd: "eval \<theta>' (Var (dsnd x)) = W"
      unfolding \<theta>'_def using dfst_neq_dsnd[of x] VW(5)
      by (simp add: eval_Cons eval_Cons_Var_same eval_closed)
    have dfstR: "dfst x \<notin> fst ` set \<theta>R" and dsndR: "dsnd x \<notin> fst ` set \<theta>R"
      using domR dS dsel_dset[of x] by blast+
    have evN: "eval \<theta>' N = (eval \<theta>R N)[V <- dfst x][W <- dsnd x]"
      unfolding \<theta>'_def
      by (rule eval_Cons2_subst[OF cvsR dfstR dsndR dfst_neq_dsnd VW(4,5)])
    have evG': "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
    proof -
      fix \<tau> assume m: "\<tau> |\<in>| \<Gamma>"
      have "dfst x \<notin> FVars (fst \<tau>)" "dsnd x \<notin> FVars (fst \<tau>)"
        using FVarsC_member'[OF m] freshGD dsel_dset[of x] by blast+
      then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
        unfolding \<theta>'_def by (simp add: eval_Cons_idle)
      then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evG[OF m] by simp
    qed
    have evD': "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)"
    proof -
      fix \<tau> assume m: "\<tau> |\<in>| \<Delta>"
      have "dfst x \<notin> FVars (fst \<tau>)" "dsnd x \<notin> FVars (fst \<tau>)"
        using FVarsC_member'[OF m] freshGD dsel_dset[of x] by blast+
      then have "eval \<theta>' (fst \<tau>) = eval \<theta>R (fst \<tau>)"
        unfolding \<theta>'_def by (simp add: eval_Cons_idle)
      then show "eval \<theta>' (fst \<tau>) = eval \<theta> (fst \<tau>)" using evD[OF m] by simp
    qed
    have satlN: "\<forall>\<tau>. \<tau> |\<in>| ((N :. A) ; \<Gamma>) \<longrightarrow> satL \<theta>' \<tau>"
    proof (intro allI impI)
      fix \<tau> assume "\<tau> |\<in>| ((N :. A) ; \<Gamma>)"
      then consider "\<tau> = (N :. A)" | "\<tau> |\<in>| \<Gamma>" by auto
      then show "satL \<theta>' \<tau>"
      proof cases
        case 1
        show ?thesis unfolding 1 satL_pair evN by (rule VW(6))
      next
        case 2
        then show ?thesis using satl satL_cong[OF evG'[OF 2]] by blast
      qed
    qed
    have clsN2: "\<And>Bi v. v \<in> dset x \<Longrightarrow> FVars (eval \<theta>' (Var v)) = {} \<Longrightarrow>
      closes \<theta>' (((N :. A) ; \<Gamma>) |\<union>| ((Var v :. Bi) ; \<Delta>))"
    proof -
      fix Bi :: type and v assume "v \<in> dset x" and clv: "FVars (eval \<theta>' (Var v)) = {}"
      have "FVars (eval \<theta>' N) = {}"
        unfolding evN using clN VW(4,5) dfst_neq_dsnd[of x] dset_alt[of x]
        by (auto simp: FVars_usubst split: if_splits)
      moreover have "\<And>\<tau>. \<tau> |\<in>| \<Gamma> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
        using evG' cls by (auto simp: closes_def)
      moreover have "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> FVars (eval \<theta>' (fst \<tau>)) = {}"
        using evD' cls by (auto simp: closes_def)
      ultimately show "closes \<theta>' (((N :. A) ; \<Gamma>) |\<union>| ((Var v :. Bi) ; \<Delta>))"
        using clv by (auto simp: closes_def)
    qed
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
    proof (cases "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>")
      case True
      then show ?thesis .
    next
      case False
      have noD': "\<And>\<tau>. \<tau> |\<in>| \<Delta> \<Longrightarrow> \<not> satR \<theta>' \<tau>"
        using False satR_cong evD' by blast
      have cls1: "closes \<theta>' (((N :. A) ; \<Gamma>) |\<union>| ((Var (dfst x) :. B1) ; \<Delta>))"
        by (rule clsN2) (use dsel_dset evfst VW(4) in auto)
      from semantic_judgementD[OF sLetL2.IH(2) cvs' cls1 satlN]
      obtain \<tau>1 where t1: "\<tau>1 |\<in>| ((Var (dfst x) :. B1) ; \<Delta>)" "satR \<theta>' \<tau>1" by blast
      have V1: "V \<in> \<lblot>B1\<rblot>"
      proof -
        have "\<tau>1 = (Var (dfst x) :. B1)" using t1(1) noD' t1(2) by blast
        then have "V \<in> \<T>\<^sub>\<bottom>\<lblot>B1\<rblot>" using t1(2) evfst by simp
        then show ?thesis using val_taubot_iff[OF VW(2)] by simp
      qed
      have cls2: "closes \<theta>' (((N :. A) ; \<Gamma>) |\<union>| ((Var (dsnd x) :. B2) ; \<Delta>))"
        by (rule clsN2) (use dsel_dset evsnd VW(5) in auto)
      from semantic_judgementD[OF sLetL2.IH(3) cvs' cls2 satlN]
      obtain \<tau>2 where t2: "\<tau>2 |\<in>| ((Var (dsnd x) :. B2) ; \<Delta>)" "satR \<theta>' \<tau>2" by blast
      have V2: "W \<in> \<lblot>B2\<rblot>"
      proof -
        have "\<tau>2 = (Var (dsnd x) :. B2)" using t2(1) noD' t2(2) by blast
        then have "W \<in> \<T>\<^sub>\<bottom>\<lblot>B2\<rblot>" using t2(2) evsnd by simp
        then show ?thesis using val_taubot_iff[OF VW(3)] by simp
      qed
      have "term.Pair V W \<in> \<lblot>Prod B1 B2\<rblot>" using V1 V2 by auto
      then have "eval \<theta>R M \<in> \<T>\<lblot>Prod B1 B2\<rblot>"
        using VW(1) val.intros(3)[OF VW(2,3)] by (blast intro: tau_intro)
      then have satlM: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Prod B1 B2) ; \<Gamma>) \<longrightarrow> satL \<theta>R \<tau>"
        using satl satL_cong evG by auto
      have clsM: "closes \<theta>R (((M :. Prod B1 B2) ; \<Gamma>) |\<union>| \<Delta>)"
        using cls evG evD evMag clM by (auto simp: closes_def)
      from semantic_judgementD[OF sLetL2.IH(1) cvsR clsM satlM]
      obtain \<tau> where t: "\<tau> |\<in>| \<Delta>" "satR \<theta>R \<tau>" by blast
      then have "satR \<theta> \<tau>" using satR_cong[OF evD[OF t(1)]] by simp
      then show ?thesis using t(1) by blast
    qed
  qed
next
  case (sOkVarR \<Gamma> x \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((Var x :. Ok) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    have clx: "FVars (eval \<theta> (Var x)) = {}" using cls by auto
    have vx: "val (eval \<theta> (Var x))"
      using eval_Var[OF cvs, of x] clx by auto
    have "eval \<theta> (Var x) \<in> \<T>\<^sub>\<bottom>\<lblot>Ok\<rblot>"
      by (rule val_in_taubot[OF vx]) (simp add: Vals0_def vx)
    then have "satR \<theta> (Var x :. Ok)" by simp
    then show "\<exists>\<tau>. \<tau> |\<in>| ((Var x :. Ok) ; \<Delta>) \<and> satR \<theta> \<tau>" by (rule exR_head)
  qed
next
  case (sOkL M \<Gamma> \<Delta> A)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((M :. A) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((M :. A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> M \<in> \<T>\<lblot>A\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>Ok\<rblot>" by (rule tau_Ok)
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. Ok) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkL.IH cvs clsP satlP] .
  qed
next
  case (sOkR \<Gamma> M A \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (\<Gamma> |\<union>| ((M :. Ok) ; \<Delta>))"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| \<Gamma> \<longrightarrow> satL \<theta> \<tau>"
    have clsP: "closes \<theta> (\<Gamma> |\<union>| ((M :. A) ; \<Delta>))" using cls by auto
    from satR_casesD[OF semantic_judgementD[OF sOkR.IH cvs clsP satl]]
    show "\<exists>\<tau>. \<tau> |\<in>| ((M :. Ok) ; \<Delta>) \<and> satR \<theta> \<tau>"
    proof (elim disjE)
      assume "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
      then have "satR \<theta> (M :. Ok)" using taubot_Ok by simp
      then show ?thesis by (rule exR_head)
    qed (blast intro: exR_tail)
  qed
next
  case (sOkApL1 M A \<Gamma> \<Delta> N)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((App M N :. Ok) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((App M N :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (App M N) \<in> \<T>\<lblot>Ok\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>OnlyTo Ok A\<rblot>" unfolding eval_App using ext_App_fix by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. OnlyTo Ok A) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. OnlyTo Ok A) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkApL1.IH cvs clsP satlP] .
  qed
next
  case (sOkApL2 N \<Gamma> \<Delta> M)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((App M N :. Ok) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((App M N :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (App M N) \<in> \<T>\<lblot>Ok\<rblot>" using satl by auto
    then have "eval \<theta> N \<in> \<T>\<lblot>Ok\<rblot>" unfolding eval_App using ext_App2_Ok by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((N :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((N :. Ok) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkApL2.IH cvs clsP satlP] .
  qed
next
  case (sOkSL M \<Gamma> \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Succ M :. Ok) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Succ M :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (Succ M) \<in> \<T>\<lblot>Ok\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>Nat\<rblot>" unfolding eval_Succ using ext_Succ by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkSL.IH cvs clsP satlP] .
  qed
next
  case (sOkPL M \<Gamma> \<Delta>)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Pred M :. Ok) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Pred M :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (Pred M) \<in> \<T>\<lblot>Ok\<rblot>" using satl by auto
    then have "eval \<theta> M \<in> \<T>\<lblot>Nat\<rblot>" unfolding eval_Pred using ext_Pred by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Nat) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M :. Nat) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkPL.IH cvs clsP satlP] .
  qed
next
  case (sOkPrL_1 M1 \<Gamma> \<Delta> M2)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Pair M1 M2 :. Ok) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Pair M1 M2 :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (term.Pair M1 M2) \<in> \<T>\<lblot>Ok\<rblot>" using satl by auto
    then have "eval \<theta> M1 \<in> \<T>\<lblot>Ok\<rblot>" unfolding eval_Pair using ext_Pair_Ok by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M1 :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M1 :. Ok) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkPrL_1.IH cvs clsP satlP] .
  qed
next
  case (sOkPrL_2 M2 \<Gamma> \<Delta> M1)
  show ?case
  proof (rule semantic_judgementI)
    fix \<theta> :: "'a valuation"
    assume cvs: "closed_val_subst \<theta>"
      and cls: "closes \<theta> (((Pair M1 M2 :. Ok) ; \<Gamma>) |\<union>| \<Delta>)"
      and satl: "\<forall>\<tau>. \<tau> |\<in>| ((Pair M1 M2 :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>"
    have "eval \<theta> (term.Pair M1 M2) \<in> \<T>\<lblot>Ok\<rblot>" using satl by auto
    then have "eval \<theta> M2 \<in> \<T>\<lblot>Ok\<rblot>" unfolding eval_Pair using ext_Pair_Ok by blast
    then have satlP: "\<forall>\<tau>. \<tau> |\<in>| ((M2 :. Ok) ; \<Gamma>) \<longrightarrow> satL \<theta> \<tau>" using satl by auto
    have clsP: "closes \<theta> (((M2 :. Ok) ; \<Gamma>) |\<union>| \<Delta>)" using cls by auto
    show "\<exists>\<tau>. \<tau> |\<in>| \<Delta> \<and> satR \<theta> \<tau>"
      using semantic_judgementD[OF sOkPrL_2.IH cvs clsP satlP] .
  qed
qed


section \<open>Corollary 4.9\<close>

text \<open>For closed terms, in the safety fragment: well-typed programs do not go wrong, and
  ill-typed programs do not evaluate.\<close>

corollary well_typed_not_stuck: \<comment> \<open>Corollary 4.9, first part\<close>
  fixes M :: "'a::var term"
  assumes cl: "FVars M = {}" and ty: "{||} \<turnstile>\<^sub>s (M :. Ok) ; {||}"
  shows "\<not> getStuck M"
proof
  assume gs: "getStuck M"
  obtain S where S: "M \<rightarrow>* S" "stuck S" using gs getStuck_def by blast
  have sem: "{||} \<Turnstile> ((M :. Ok) ; {||})" by (rule semantic_soundness[OF ty])
  have cls0: "closes [] ({||} |\<union>| ((M :. Ok) ; {||}))"
    using cl by (auto simp: closes_def)
  have satl0: "\<forall>\<tau>. \<tau> |\<in>| ({||} :: 'a typing fset) \<longrightarrow> satL [] \<tau>" by auto
  obtain \<tau> where t: "\<tau> |\<in>| ((M :. Ok) ; {||})" "satR [] \<tau>"
    using semantic_judgementD[OF sem cvs_Nil cls0 satl0] by blast
  then have MOk: "M \<in> \<T>\<^sub>\<bottom>\<lblot>Ok\<rblot>" by auto
  then consider (v) V where "M \<rightarrow>* V" "val V" | (d) "M \<Up>" by auto
  then show False
  proof cases
    case (v V)
    have "V = S"
      using beta_star_normal_unique v S(1) vals_are_normal[OF v(2)] stucks_are_normal[OF S(2)]
      unfolding beta_star_def by blast
    then show False using v(2) S(2) stuck_not_val by blast
  next
    case d
    then show False
      using S(1) stucks_are_normal[OF S(2)] diverge_xor_normalizes normalizes_def by blast
  qed
qed

corollary ill_typed_not_evaluate: \<comment> \<open>Corollary 4.9, second part\<close>
  fixes M :: "'a::var term"
  assumes cl: "FVars M = {}" and ty: "(M :. Ok) ; {||} \<turnstile>\<^sub>s {||}"
  shows "\<not> (\<exists>V. M \<rightarrow>* V \<and> val V)"
proof
  assume "\<exists>V. M \<rightarrow>* V \<and> val V"
  then have "satL [] (M :. Ok)" by (auto simp: Vals0_def)
  then have satl0: "\<forall>\<tau>. \<tau> |\<in>| ((M :. Ok) ; {||}) \<longrightarrow> satL [] \<tau>" by auto
  have cls0: "closes [] (((M :. Ok) ; {||}) |\<union>| {||})"
    using cl by (auto simp: closes_def)
  show False
    using semantic_judgementD[OF semantic_soundness[OF ty] cvs_Nil cls0 satl0] by auto
qed


section \<open>Theorem 4.5: the necessity arrow is not a safety property\<close>

text \<open>The type \<open>Nat \<tratail> Nat \<rightarrow> Nat\<close> violates (S1): the context \<open>C = \<lambda>x y. [\<cdot>] x\<close> filled with
  \<open>N = \<lambda>w. pred w\<close> inhabits \<open>\<T>\<^sub>\<bottom>\<lblot>OnlyTo Nat (To Nat Nat)\<rblot>\<close> (if the argument is not a numeral,
  the returned function gets stuck on any input), but filled with \<open>div \<lesssim> N\<close> it does not
  (\<open>\<lambda>y. div V\<close> diverges on any input, hence is in \<open>Nat \<rightarrow> Nat\<close>, even for non-numeral \<open>V\<close>).
  This is the first half of the paper's Theorem 4.5; since a single failing conjunct suffices,
  it already establishes that not every type defines a safety property.\<close>

theorem necessity_not_safety: \<comment> \<open>Theorem 4.5\<close>
  "\<not> safety_property (tt :: 'a::var itself) (OnlyTo Nat (To Nat Nat))"
proof -
  obtain z :: 'a where "z \<notin> {}" using fresh_finite[of "{}"] by auto
  obtain a :: 'a where a: "a \<notin> {z}" using fresh_finite[of "{z}"] by auto
  obtain b :: 'a where b: "b \<notin> {z, a}" using fresh_finite[of "{z, a}"] by auto
  define N :: "'a term" where "N = Lam z (Pred (Var z))"
  define C :: "'a term" where "C = Lam a (Lam b (App (Var z) (Var a)))"
  have az: "a \<noteq> z" and bz: "b \<noteq> z" and ba: "b \<noteq> a" using a b by auto
  have clN: "FVars N = {}" unfolding N_def by auto
  have vN: "val N" unfolding N_def by simp
  have NW: "App N W \<rightarrow> Pred W" if "val W" for W :: "'a term"
    using Lam_beta[OF that, of z "Pred (Var z)"] unfolding N_def by simp
  \<comment> \<open>the two fillings of the context\<close>
  have CN: "C[N <- z] = Lam a (Lam b (App N (Var a)))"
    unfolding C_def using az bz clN by (simp add: Lam_usubst)
  have CP: "C[divt <- z] = Lam a (Lam b (App divt (Var a)))"
    unfolding C_def using az bz by (simp add: Lam_usubst)
  have clCN: "FVars (C[N <- z]) = {}" unfolding CN using clN by auto
  have PleN: "divt \<lesssim> N"
    unfolding less_defined_def using divt_not_normalizes by blast
  \<comment> \<open>filled with @{term N}, the context inhabits the type\<close>
  have CNmem: "C[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo Nat (To Nat Nat)\<rblot>"
  proof -
    obtain g where g: "g \<notin> {a, b} \<union> FVars (N :: 'a term)"
      using fresh_finite[of "{a, b} \<union> FVars N"] by auto
    have Le: "Lam a (Lam b (App N (Var a))) = Fix g a (Lam b (App N (Var a)))"
      by (rule Lam_eq) (use g clN in auto)
    have bodyprop: "\<forall>W\<in>Vals0. FVars W = {} \<longrightarrow>
      (Lam b (App N (Var a)))[W <- a][Fix g a (Lam b (App N (Var a))) <- g] \<in> \<T>\<lblot>To Nat Nat\<rblot> \<longrightarrow>
      W \<in> \<lblot>Nat\<rblot>"
    proof (intro ballI impI)
      fix W :: "'a term"
      assume "W \<in> Vals0" and clW: "FVars W = {}"
        and mem: "(Lam b (App N (Var a)))[W <- a][Fix g a (Lam b (App N (Var a))) <- g]
          \<in> \<T>\<lblot>To Nat Nat\<rblot>"
      have vW: "val W" using \<open>W \<in> Vals0\<close> by (simp add: Vals0_def)
      have push1: "(Lam b (App N (Var a)))[W <- a] = Lam b (App N W)"
        using ba clW clN az bz by (simp add: Lam_usubst subst_idle)
      have push2: "(Lam b (App N W))[Fix g a (Lam b (App N (Var a))) <- g] = Lam b (App N W)"
        by (rule subst_idle) (use g clN clW in auto)
      have memTo: "Lam b (App N W) \<in> \<T>\<lblot>To Nat Nat\<rblot>" using mem unfolding push1 push2 .
      have memTo': "Lam b (App N W) \<in> \<lblot>To Nat Nat\<rblot>"
        using val_tau_iff[OF val_Lam] memTo by blast
      obtain h where h: "h \<notin> {b} \<union> FVars (App N W)"
        using fresh_finite[of "{b} \<union> FVars (App N W)"] by auto
      have Lh: "Lam b (App N W) = Fix h b (App N W)"
        by (rule Lam_eq) (use h in auto)
      have iZ: "(Zero :: 'a term) \<in> \<lblot>Nat\<rblot>" by (simp add: num.intros(1))
      have unf: "(App N W)[Zero <- b][Lam b (App N W) <- h] \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
        by (rule To_unfold[OF memTo' _ _ iZ Lh]) (auto intro: val.intros num.intros)
      have clNW: "b \<notin> FVars (App N W)" and hNW: "h \<notin> FVars (App N W)"
        using clN clW h by auto
      have ANW: "App N W \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
        using unf unfolding subst_idle[OF clNW] subst_idle[OF hNW] .
      show "W \<in> \<lblot>Nat\<rblot>"
      proof (rule ccontr)
        assume "W \<notin> \<lblot>Nat\<rblot>"
        then have nW: "\<not> num W" by simp
        have "stuckEx (Pred W)" by (rule stuckEx.intros(5)[OF vW nW])
        then have sPW: "stuck (Pred W)" by (rule stuckEx_imp_stuck)
        have steps: "App N W \<rightarrow>[Suc 0] Pred W"
          using betas.step[OF NW[OF vW] betas.refl] .
        have "App N W \<notin> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
          by (rule notin_taubot_of_normal_reach[OF steps stucks_are_normal[OF sPW]])
            (use sPW stuck_not_val in blast)
        then show False using ANW by blast
      qed
    qed
    have "Lam a (Lam b (App N (Var a))) \<in> \<lblot>OnlyTo Nat (To Nat Nat)\<rblot>"
      unfolding Le type_semantics.simps(5) using bodyprop by blast
    then show ?thesis
      unfolding CN using val_taubot_iff[OF val_Lam] by blast
  qed
  \<comment> \<open>filled with @{term divt}, it does not\<close>
  have CPnot: "C[divt <- z] \<notin> \<T>\<^sub>\<bottom>\<lblot>OnlyTo Nat (To Nat Nat)\<rblot>"
  proof
    assume "C[divt <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo Nat (To Nat Nat)\<rblot>"
    then have memO: "Lam a (Lam b (App divt (Var a))) \<in> \<lblot>OnlyTo Nat (To Nat Nat)\<rblot>"
      unfolding CP using val_taubot_iff[OF val_Lam] by blast
    define VV :: "'a term" where "VV = Lam z (Var z)"
    have vVV: "val VV" unfolding VV_def by simp
    have clVV: "FVars VV = {}" unfolding VV_def by auto
    obtain g where g: "g \<notin> {a, b}" using fresh_finite[of "{a, b}"] by auto
    have Le: "Lam a (Lam b (App divt (Var a))) = Fix g a (Lam b (App divt (Var a)))"
      by (rule Lam_eq) (use g in auto)
    have push1: "(Lam b (App divt (Var a)))[VV <- a] = Lam b (App divt VV)"
      using ba clVV az bz by (simp add: Lam_usubst subst_idle)
    have push2: "(Lam b (App divt VV))[Lam a (Lam b (App divt (Var a))) <- g]
        = Lam b (App divt VV)"
      by (rule subst_idle) (use g clVV in auto)
    have memTo: "Lam b (App divt VV) \<in> \<lblot>To Nat Nat\<rblot>"
    proof -
      obtain h where h: "h \<notin> {b} \<union> FVars (App divt VV)"
        using fresh_finite[of "{b} \<union> FVars (App divt VV)"] by auto
      have Lh: "Lam b (App divt VV) = Fix h b (App divt VV)"
        by (rule Lam_eq) (use h in auto)
      have dv: "App divt VV \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
        using div_App1[OF divt_diverge] by auto
      have bodyprop: "\<forall>U\<in>Vals0. FVars U = {} \<longrightarrow> U \<in> \<lblot>Nat\<rblot> \<longrightarrow>
        (App divt VV)[U <- b][Fix h b (App divt VV) <- h] \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
      proof (intro ballI impI)
        fix U :: "'a term"
        assume "FVars U = {}"
        have c1: "b \<notin> FVars (App divt VV)" and c2: "h \<notin> FVars (App divt VV)"
          using clVV h by auto
        show "(App divt VV)[U <- b][Fix h b (App divt VV) <- h] \<in> \<T>\<^sub>\<bottom>\<lblot>Nat\<rblot>"
          unfolding subst_idle[OF c1] subst_idle[OF c2] by (rule dv)
      qed
      show ?thesis unfolding Lh type_semantics.simps(4) using bodyprop by blast
    qed
    have memTo': "(Lam b (App divt (Var a)))[VV <- a]
        [Lam a (Lam b (App divt (Var a))) <- g] \<in> \<T>\<lblot>To Nat Nat\<rblot>"
      unfolding push1 push2 using val_tau_iff[OF val_Lam] memTo by blast
    have "VV \<in> \<lblot>Nat\<rblot>"
      by (rule OnlyTo_unfold[OF memO vVV clVV Le memTo'])
    then have "num VV" by simp
    then show False unfolding VV_def using not_num_Lam by blast
  qed
  have "\<not> (\<forall>(C::'a term) N P z. FVars (C[N <- z]) = {} \<longrightarrow> P \<lesssim> N \<longrightarrow>
      C[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo Nat (To Nat Nat)\<rblot> \<longrightarrow>
      C[P <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>OnlyTo Nat (To Nat Nat)\<rblot>)"
    using clCN PleN CNmem CPnot by blast
  then show ?thesis unfolding safety_property_def by blast
qed

end
