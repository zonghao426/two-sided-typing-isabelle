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
| "\<lblot>To A B\<rblot> = {Fix f x M | f x M. \<forall>V \<in> Vals0. V \<in> \<lblot>A\<rblot> \<longrightarrow> M[V <- x][Fix f x M <- f] \<in> \<T>\<^sub>\<bottom>\<lblot>B\<rblot>}"
| "\<lblot>OnlyTo A B\<rblot> = {Fix f x M | f x M. \<forall>V \<in> Vals0. M[V <- x][Fix f x M <- f] \<in> \<T>\<lblot>B\<rblot> \<longrightarrow> V \<in> \<lblot>A\<rblot>}"
| "\<T>\<lblot>A\<rblot> = {M. \<exists>V \<in> \<lblot>A\<rblot>. M \<rightarrow>* V \<and> val V}"
| "\<T>\<^sub>\<bottom>\<lblot>A\<rblot> = {M. M \<in> \<T>\<lblot>A\<rblot> \<or> (M \<Up>)}"

type_synonym 'var valuation = "('var \<times> 'var term) list"

fun eval :: "'var::var valuation \<Rightarrow> 'var term \<Rightarrow> 'var term" where
  "eval Nil M = M"
| "eval ((x,t) # ps) M = eval ps (M[t <- x])"

inductive typing_semanticsL :: "'var::var valuation \<Rightarrow> 'var typing \<Rightarrow> bool" where
  "eval \<theta> M \<in> \<T>\<lblot>A\<rblot> \<Longrightarrow> typing_semanticsL \<theta> (M :. A)"

inductive typing_semanticsR :: "'var::var valuation \<Rightarrow> 'var typing \<Rightarrow> bool" where
  "eval \<theta> M \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow> typing_semanticsR \<theta> (M :. A)"

inductive semantic_judgement :: "'var::var typing fset \<Rightarrow> 'var typing fset \<Rightarrow> bool" (infix "\<Turnstile>" 10) where
  "\<forall>\<theta>. (\<forall>\<tau>. \<tau> |\<in>| L \<longrightarrow> typing_semanticsL \<theta> \<tau>) \<longrightarrow> (\<forall>\<tau>. \<tau> |\<in>| R \<longrightarrow> typing_semanticsR \<theta> \<tau>) \<Longrightarrow> L \<Turnstile> R"

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
  then obtain U where U1: "Pair V1 V2 = U[N <- z]" and U2: "M[P <- z] \<rightarrow>* U[P <- z]"
    using b4[of M N z _ "Pair V1 V2" P] beta_star_def val.intros(3) vals_are_normal
    by metis
  then show ?case
  proof (cases "U = Var z")
    case True
    then show ?thesis 
      using b5_helper[of M N z "Pair V1 V2" P U] 3 val.intros(3) U1 U2 by blast
  next
    case False
    then obtain M1 M2 where m1m2: "U = Pair M1 M2" and m1: "M1[N <- z] = V1" and m2: "M2[N <- z] = V2"
      using subst_Pair_inversion[of U N z V1 V2] False U1
      by metis
    then have "val M1" and "val M2"
      using subst_val_inversion 3(1, 2) (*what if M1 or M2 = Suc z, N = Zero*) sorry (*why do we need you?*)
    have "\<not> (M1[P <- z] \<Up>)" 
      using m1m2 U2 beta_star_diverge_back[of "M[P <- z]" "U[P <- z]"]
      using "3.prems"(4) Pair_div[of "M1[P <- z]" "M2[P <- z]"] 
      by auto
    then have "\<not> (M2[P <- z] \<Up>)" sorry (*what if M2 diverge and M1 stuck*)
    show ?thesis
    proof(cases "haveFix (Pair V1 V2)")
      case True
      then have b5VU: "b5_prop (Pair V1 V2) U[P <- z] P N z" unfolding b5_prop_def
        using m1m2 m1 m2 term.distinct(55) term.inject(7)
        by auto
      have "val M1[P <- z]" and "val M2[P <- z]" 
        using \<open>val M1\<close> \<open>val M2\<close> sorry (*is right?*)
      then have "val U[P <- z]" using m1m2 val.intros by auto
      then have "val U[P <- z] \<and> M[P <- z] \<rightarrow>* U[P <- z] \<and> b5_prop (term.Pair V1 V2) U[P <- z] P N z"
        using b5VU U2 by auto
      then show ?thesis by auto
    next
      case False
      obtain W1 where "val W1" and "M1[P <- z] \<rightarrow>* W1" and "b5_prop V1 W1 P N z"
        using 3(3)[of M1] m1 beta_star_def betas.refl
        using \<open>P \<lesssim> N\<close> \<open>z \<notin> FVars N\<close> \<open>\<not> (M1[P <- z] \<Up>)\<close> \<open>z \<notin> FVars (Pair V1 V2)\<close>
        by (metis Un_iff term.set(8))
      moreover obtain W2 where "val W2" and "M2[P <- z] \<rightarrow>* W2" and "b5_prop V2 W2 P N z"
        using 3(4)[of M2] m2 beta_star_def betas.refl
        using \<open>P \<lesssim> N\<close> \<open>z \<notin> FVars N\<close> \<open>\<not> (M2[P <- z] \<Up>)\<close> \<open>z \<notin> FVars (Pair V1 V2)\<close>
        by (metis Un_iff term.set(8))
      ultimately have *: "val (Pair W1 W2)" and **: "M[P <- z] \<rightarrow>* (Pair W1 W2)"
        using val.intros(3) U2 m1m2 beta_star_sums[of "M[P <- z]" "U[P <- z]" "Pair W1 W2"] Pair_beta_star
         apply auto
        by blast
      have "\<not> haveFix V1" and "\<not> haveFix V2"
        using False haveFix_Pair by auto
      then have "V1 = W1 \<and> V2 = W2" 
        using \<open>b5_prop V1 W1 P N z\<close> \<open>b5_prop V2 W2 P N z\<close> unfolding b5_prop_def by blast
      then have "val (Pair V1 V2) \<and> M[P <- z] \<rightarrow>* (Pair V1 V2) \<and> b5_prop (Pair V1 V2) (Pair V1 V2) P N z"
        using * ** b5_prop_reflexive 3(1, 2, 9) by blast
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

lemma eval_ctx_beta_inverse: 
  assumes "eval_ctx hole E" and "E[M <- hole] \<rightarrow> E[N <- hole]"
  shows "M \<rightarrow> N"
  using assms
  sorry

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

lemma b6:
  assumes gsM: "getStuck M[N <- z]" and ls: "P \<lesssim> N" and znN: "z \<notin> FVars N"
  shows "diverge M[P <- z] \<or> getStuck M[P <- z]"
proof -
  obtain M' where "M[N <- z] \<rightarrow>* M'" and "stuck M'" using gsM getStuck_def by auto
  then obtain R where *: "diverge M[P <- z] \<or> (M[P <- z] \<rightarrow>* R[P <- z] \<and> M' = R[N <- z])" 
    unfolding beta_star_def
    using ls znN stucks_are_normal[of M'] b4[of M N z _ M' P] by blast
  then consider (A) "M[P <- z] \<rightarrow>* R[P <- z] \<and> M' = R[N <- z]" | (B) "diverge M[P <- z]" by auto
  then show ?thesis
  proof cases
    case A
    then obtain E hole Q where "eval_ctx hole E" and "R[N <- z] = E[Q <- hole]" and "stuckEx Q"
      using \<open>stuck M'\<close> unfolding stuck_def by metis
    then obtain F Q' where "eval_ctx hole F" and "F[N <- z] = E" and "R = F[Q' <- hole]" and "Q'[N <- z] = Q" 
      using b2[of hole E R N z Q] (*need \<not> blocked z R, need hole freshness*) sorry
    show ?thesis
    proof(cases "Q' = Var z")
      case True
      then have "blocked z R" using \<open>eval_ctx hole F\<close> \<open>R = F[Q' <- hole]\<close> unfolding blocked_def by auto
      thm blocked_fresh_hole[of "FVars P" z R]
      then obtain F' hole' where 
        "\<forall>N. hole' \<notin> FVars N \<longrightarrow> eval_ctx hole' F'[N <- z]" and
        new_ctx: "R = F'[Var z <- hole']" and
        fresh_hole: "hole' \<notin> insert z (FVars P)"
        using finite_FVars blocked_fresh_hole[of "FVars P" z R] by auto
      then have FP: "eval_ctx hole' F'[P <- z]" by simp
      from True have "Q = N" using \<open>Q'[N <- z] = Q\<close> by simp
      then have "diverge R[P <- z] \<or> getStuck R[P <- z]"
      proof (cases "diverge P")
        case True
        have "R[P <- z] = F'[P <- z][P <- hole']" 
          using new_ctx fresh_hole usubst_usubst[of hole' z P F' "Var z"] by simp
        then have "diverge R[P <- z]" using FP True div_ctx[of hole' "F'[P <- z]" P] by simp
        then show ?thesis using exI by blast
      next
        case False
        then obtain N' where "N \<rightarrow>* N'" and "P \<rightarrow>* N'" and "normal N'"
          using \<open>P \<lesssim> N\<close> unfolding less_defined_def
          using diverge_or_normalizes[of P] by auto
        then have "F'[Q' <- hole'][P <- z] = F'[P <- z][P <- hole']"
          using fresh_hole usubst_usubst[of hole' z P F' Q'] \<open>Q' = Var z\<close>
          by auto
        then have t1: "R[P <- z] \<rightarrow>* F'[P <- z][N' <- hole']"
          using True new_ctx insertI2
          using \<open>P \<rightarrow>* N'\<close> FP eval_ctx_beta_star[of hole' "F'[P <- z]" P N']
          by auto
        have "stuckEx N'" 
          using \<open>N \<rightarrow>* N'\<close> \<open>Q = N\<close> \<open>stuckEx Q\<close> betas.cases[of N _ N'] unfolding beta_star_def
          using eval_ctx.intros(1) usubst_simps(5) stucks_are_normal[of N] unfolding normal_def stuck_def 
          by metis
        then have "stuck F'[P <- z][N' <- hole']" unfolding stuck_def using FP by auto
        then have "getStuck R[P <- z]" unfolding getStuck_def using t1 by auto
        then show ?thesis by auto
      qed
      then show ?thesis unfolding getStuck_def
        using A beta_star_diverge_back beta_star_sums by blast
    next                              
      case False
      have "stuckEx Q'[N <- z]" using \<open>Q'[N <- z] = Q\<close> \<open>stuckEx Q\<close> by simp
      then have "diverge Q'[P <- z] \<or> getStuck Q'[P <- z]"
      proof(cases "Q'[N <- z]" rule:stuckEx.cases)
        case (1 V)
        then obtain V' where "Q' = Succ V'" and "V = V'[N <- z]"
          using False subst_Succ_inversion[of Q' N z V] by auto
        then consider (A) "V'[P <- z] \<Up>" | (B) "\<exists>W. val W \<and> V'[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
          using 1(2) znN ls betas.refl b5[of V z N V' P] unfolding beta_star_def by auto
        then show ?thesis
        proof(cases)
          case A
          obtain thole :: 'a where "eval_ctx thole (Succ (Var thole))" using eval_ctx.intros by blast
          moreover have "Q'[P <- z] = (Succ (Var thole)) [V'[P <- z] <- thole]" using \<open>Q' = Succ V'\<close> by auto
          ultimately show ?thesis using div_ctx A by metis
        next
          case B
          then obtain W where "val W" and "V'[P <- z] \<rightarrow>* W" and "b5_prop V W P N z" by auto
          then have "\<not> num W" using 1 b5_prop_not_num[of V] by blast
          then have "stuckEx (Succ W)" using \<open>val W\<close> stuckEx.intros by auto
          then have "stuck (Succ W)"
            using eval_ctx.intros(1) stuck_def by force
          then have "getStuck (Succ V'[P <- z])" unfolding getStuck_def
            using Succ_beta_star \<open>V'[P <- z] \<rightarrow>* W\<close> beta_star_def by blast
          then show ?thesis using \<open>Q' = Succ V'\<close> by auto
        qed
      next
        case (2 V P1 P2)
        then obtain V' P1' P2' where "Q' = If V' P1' P2'" and 
          "V'[N <- z] = V" and "P1'[N <- z] = P1" and "P2'[N <- z] = P2" 
          using False subst_If_inversion[of Q' N z V P1 P2] by auto
        then consider (A) "V'[P <- z] \<Up>" | (B) "\<exists>W. val W \<and> V'[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
          using 2(2) znN ls betas.refl b5[of V z N V' P] unfolding beta_star_def by auto
        then show ?thesis
        proof(cases)
          case A
          obtain thole where "eval_ctx thole (If (Var thole) P1'[P <- z] P2'[P <- z])" and *: "thole \<notin> FVars P1'[P <- z]" and **: "thole \<notin> FVars P2'[P <- z]"
            using eval_ctx.intros(1, 9) 
            using ex_new_if_finite finite_FVars infinite_UNIV
            by (metis Un_iff term.set(4))
          moreover have "Q'[P <- z] = (If (Var thole) P1'[P <- z] P2'[P <- z]) [V'[P <- z] <- thole]" 
            using \<open>Q' = If V' P1' P2'\<close> * ** by auto
          ultimately show ?thesis using div_ctx A by metis
        next
          case B
          then obtain W where "val W" and "V'[P <- z] \<rightarrow>* W" and "b5_prop V W P N z" by auto
          then have "\<not> num W" using 2 b5_prop_not_num[of V] by blast
          then have "stuckEx (If W P1'[P <- z] P2'[P <- z])" using \<open>val W\<close> stuckEx.intros by auto
          then have "stuck (If W P1'[P <- z] P2'[P <- z])"
            using eval_ctx.intros(1) stuck_def by force
          then have "getStuck (If V'[P <- z] P1'[P <- z] P2'[P <- z])" unfolding getStuck_def
            using If_beta_star \<open>V'[P <- z] \<rightarrow>* W\<close> beta_star_def by blast
          then show ?thesis using \<open>Q' = If V' P1' P2'\<close> by auto
        qed
      next
        case (3 V M)
        then obtain R1 R2 where "Q' = App R1 R2" and "R1[N <- z] = V" and "R2[N <- z] = M"
          using False subst_App_inversion[of Q' N z V M] by blast
        then consider (A) "R1[P <- z] \<Up>" | (B) "\<exists>W. val W \<and> R1[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
          using 3(2) znN ls betas.refl b5[of V z N R1 P] unfolding beta_star_def by auto
        then show ?thesis
        proof(cases)
          case A
          obtain thole where *: "eval_ctx thole (App (Var thole) R2[P <- z])" and "thole \<notin> FVars R2[P <- z]"
            using eval_ctx.intros(1, 3)
            by (metis ex_new_if_finite finite_FVars infinite_UNIV)
          then have "Q'[P <- z] = (App (Var thole) R2[P <- z])[R1[P <- z] <- thole]" 
            using \<open>Q' = App R1 R2\<close> usubst_simps(6) by simp
          then show ?thesis using A * div_ctx by metis
        next
          case B
          then obtain W where "val W" and *: "R1[P <- z] \<rightarrow>* W" and "b5_prop V W P N z" by auto
          then have "\<nexists>f x Q. W = Fix f x Q" using 3(2, 3) b5_prop_not_fix by (metis is_Fix_def)
          then have "stuckEx (App W R2[P <- z])" using \<open>val W\<close> stuckEx.intros(3)[of W] by (auto simp: is_Fix_def)
          moreover obtain thole :: 'a where "eval_ctx thole (Var thole)" using eval_ctx.intros by auto
          ultimately have "stuck (App W R2[P <- z])" unfolding stuck_def
            by (meson eval_ctx.intros(1) usubst_simps(5))
          then have "getStuck (App R1[P <- z] R2[P <- z])" unfolding getStuck_def
            using App_beta_star * by auto
          then show ?thesis using \<open>Q' = App R1 R2\<close> by simp
        qed    
        next
          case (4 V xy M)
          have av1: "z \<notin> dset xy" and av2: "FVars N \<inter> dset xy = {}" and av3: "FVars P \<inter> dset xy = {}" sorry
          then obtain V' M' where q': "Q' = Let xy V' M'" and "V'[N <- z] = V" and "M'[N <- z] = M"
            using False 4 subst_Let_inversion[of Q' N z xy V M] by blast
          then consider (A) "V'[P <- z] \<Up>" | (B) "\<exists>W. val W \<and> V'[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
            using 4(2) znN ls betas.refl b5[of V z N V' P] unfolding beta_star_def by auto
          then show ?thesis
          proof(cases)
            case A
            obtain thole where "eval_ctx thole (Let xy (Var thole) M'[P <- z])" and *: "thole \<notin> FVars M'[P <- z]" and **: "thole \<notin> dset xy"
              using eval_ctx.intros(1, 8)
              using ex_new_if_finite finite_FVars infinite_UNIV
              sorry
            moreover have "Q'[P <- z] = (Let xy (Var thole) M'[P <- z]) [V'[P <- z] <- thole]" 
              using q' * ** av1 av2 av3 usubst_simps(9)[of z xy P V' M'] sorry  (*xy avoids V'*)
            ultimately show ?thesis using div_ctx A by metis
          next
            case B
            then obtain W where "val W" and "V'[P <- z] \<rightarrow>* W" and "b5_prop V W P N z" by auto
            then have "\<nexists>W1 W2. W = Pair W1 W2" using 4 b5_prop_not_pair[of V] by (metis is_Pair_def)
            then have "stuckEx (Let xy W M'[P <- z])" using \<open>val W\<close> stuckEx.intros by (auto simp: is_Pair_def)
            then have "stuck (Let xy W M'[P <- z])"
              using eval_ctx.intros(1) stuck_def by force
            then have "getStuck (Let xy V'[P <- z] M'[P <- z])" unfolding getStuck_def
              using Let_beta_star[of "V'[P <- z]" W xy "M'[P <- z]"] \<open>V'[P <- z] \<rightarrow>* W\<close> 
              unfolding beta_star_def by auto
            then show ?thesis using \<open>Q' = Let xy V' M'\<close> av1 av2 av3 sorry (*xy avoids V'*)
          qed
      next
        case (5 V)
        then obtain V' where "Q' = Pred V'" and "V = V'[N <- z]"
          using False subst_Pred_inversion[of Q' N z V] by auto
        then consider (A) "V'[P <- z] \<Up>" | (B) "\<exists>W. val W \<and> V'[P <- z] \<rightarrow>* W \<and> b5_prop V W P N z"
          using 5(2) znN ls betas.refl b5[of V z N V' P] unfolding beta_star_def by auto
        then show ?thesis
        proof(cases)
          case A
          obtain thole :: 'a where "eval_ctx thole (Pred (Var thole))" using eval_ctx.intros by blast
          moreover have "Q'[P <- z] = (Pred (Var thole)) [V'[P <- z] <- thole]" using \<open>Q' = Pred V'\<close> by auto
          ultimately show ?thesis using div_ctx A by metis
        next
          case B
          then obtain W where "val W" and "V'[P <- z] \<rightarrow>* W" and "b5_prop V W P N z" by auto
          then have "\<not> num W" using 5 b5_prop_not_num[of V] by blast
          then have "stuckEx (Pred W)" using \<open>val W\<close> stuckEx.intros by blast
          then have "stuck (Pred W)"
            using eval_ctx.intros(1) stuck_def by force
          then have "getStuck (Pred V'[P <- z])" unfolding getStuck_def
            using Pred_beta_star \<open>V'[P <- z] \<rightarrow>* W\<close> beta_star_def by blast
          then show ?thesis using \<open>Q' = Pred V'\<close> by auto
        qed
      qed
      then show ?thesis sorry
      (*how would be obtain stuck R[P <- z] from stuckEx Q'[P <- z], knowing that I may have F[P <- z] not an eval_ctx*)
    qed
  qed(auto)
qed

section \<open>Thm 4.7\<close>

lemma stuck_not_val: "stuck M \<Longrightarrow> \<not> val M"
  unfolding stuck_def using val_ctx_plug stuckEx_not_val by metis

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
| "safe A \<Longrightarrow> finitely_verifiable F \<Longrightarrow> safe (OnlyTop A F)"

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

lemma less_defined_diverge_subst: "Q \<lesssim> N \<Longrightarrow> diverge M[N <- z] \<Longrightarrow> diverge M[Q <- z]"
proof(cases "blocked z M")
  case True
  assume ls: "Q \<lesssim> N" and Md: "diverge M[N <- z]"
  obtain E hole where "M = E[Var z <- hole]" and "hole \<noteq> z" and niN: "hole \<notin> FVars N" and niQ: "hole \<notin> FVars Q" 
    and ctx_subst: "\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- z]"
    using blocked_fresh_hole[of "FVars N \<union> FVars Q"] finite_FVars True by auto
  then have "M[N <- z] = E[N <- z][N <- hole]" and "M[Q <- z] = E[Q <- z][Q <- hole]"
    using usubst_usubst[of hole z N] usubst_usubst[of hole z Q]
    by auto
  also have "eval_ctx hole E[N <- z]" and "eval_ctx hole E[Q <- z]"
    using niN niQ ctx_subst by auto
  ultimately have "diverge M[Q <- z]"
    using ls Md less_defined_diverge[of Q N] div_ctx sorry
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed

theorem b7_induction:
  assumes cl: "FVars M[N <- z] = {}" and ls: "Q \<lesssim> N" and nzN: "z \<notin> FVars N"
  shows "M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<Longrightarrow> M[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>"
    and "M[N <- z] \<notin> \<T>\<lblot>A\<rblot> \<Longrightarrow> M[Q <- z] \<notin> \<T>\<lblot>A\<rblot>"
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
        using less_defined_diverge_subst ls by blast
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
          using ls less_defined_diverge_subst by auto
        then show ?thesis unfolding tau_semantics.simps 
          using diverge_xor_normalizes vals_are_normal normalizes_def
          by auto
      qed
  }
next
  case (Prod A1 A2)
  {
    case 1
    then consider (A) "diverge M[N <- z]" | (B) "\<exists>V1 V2. M[N <- z] \<rightarrow>* (Pair V1 V2) \<and> V1 \<in> \<lblot>A1\<rblot> \<and> V2 \<in> \<lblot>A2\<rblot> \<and> val (Pair V1 V2)"
      unfolding bottom_semantics.simps tau_semantics.simps type_semantics.simps
      by auto
    then show ?case
    proof cases
      case A
      then have "diverge M[Q <- z]" 
        using ls less_defined_diverge_subst by auto                 
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
          using Prod.IH(1)[of W1] Prod.IH(3)[of W2] by auto
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
    then have notT: "M[N <- z] \<notin> \<T>\<lblot>Prod A1 A2\<rblot>" by simp
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
      then have "diverge M[Q <- z]" using ls less_defined_diverge_subst by auto
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
            then have "W1[Q <- z] \<notin> \<T>\<lblot>A1\<rblot>" using Prod.IH(2)[of W1] by auto
            then have "W1[Q <- z] \<notin> \<lblot>A1\<rblot>" using vW1 val_tau_iff by auto
            then show ?thesis by simp
          next
            assume "V2 \<notin> \<lblot>A2\<rblot>"
            then have "W2[N <- z] \<notin> \<T>\<lblot>A2\<rblot>" using w2 vV2 val_tau_iff by auto
            then have "W2[Q <- z] \<notin> \<T>\<lblot>A2\<rblot>" using Prod.IH(4)[of W2] by auto
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
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (OnlyTo A1 A2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
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
      then have "diverge M[Q <- z]" using ls less_defined_diverge_subst by auto
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
      then have "diverge M[Q <- z]" using ls less_defined_diverge_subst by auto
      then show ?thesis unfolding tau_semantics.simps type_semantics.simps
        using diverge_xor_normalizes vals_are_normal normalizes_def by (auto simp: Vals0_def)
    qed
  }
qed

theorem b7: 
  assumes cl: "FVars M[N <- z] = {}" and ls: "Q \<lesssim> N"
  shows "(M[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot> \<longrightarrow> M[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A\<rblot>) \<and> (M[N <- z] \<notin> \<T>\<lblot>A\<rblot> \<longrightarrow> M[Q <- z] \<notin> \<T>\<lblot>A\<rblot>)"
proof(cases "z \<in> FVars M")
  case True
  then have "z \<notin> FVars N" using cl FVars_usubst[of M N z] by auto
  then show ?thesis using cl ls b7_induction[of M N z Q A] by blast
next
  case False
  then show ?thesis using subst_idle[of z M] by auto
qed

end
