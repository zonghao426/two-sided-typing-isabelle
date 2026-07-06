theory MrBNF_ver
  imports Binders.MRBNF_Recursor "Case_Studies.FixedCountableVars"
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
| Let : "val V \<Longrightarrow> val W \<Longrightarrow> Let xy (Pair V W) M \<rightarrow> M[V <- dfst xy][W <- dsnd xy]"
| PredZ: "Pred Zero \<rightarrow> Zero"
| PredS: "num n \<Longrightarrow> Pred (Succ n) \<rightarrow> n"
| FixBeta: "val V \<Longrightarrow> App (Fix f x M) V \<rightarrow> M[V <- x][Fix f x M <- f]"

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
  by (induct rule: num.induct) (auto simp: term.permute intro: num.intros)

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

binder_inductive (no_auto_equiv) beta
  sorry (*TODO: Dmitriy*)

binder_inductive (no_auto_equiv) stuckEx
  sorry

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
(*
lemma premute_term_subst: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a ::var set| \<Longrightarrow> |SSupp Var f :: 'a set| <o |UNIV :: 'a set| \<Longrightarrow> id_on (FVars M - SSupp Var f) \<sigma> \<Longrightarrow>
  subst f (permute_term \<sigma> M) = subst (f o \<sigma>) M"
  apply (binder_induction M avoiding: M "IImsupp Var FVars f" "imsupp \<sigma>" rule: term_strong_induct)
            apply (metis SSupp_Inj_bound term.IImsupp_Sb_bound term.Sb_comp_Inj)
  using imsupp_supp_bound infinite_UNIV apply blast
          apply (auto simp: Un_Diff id_on_Un bij_implies_inject)
   apply (subst (1 2) term.subst)
  apply blast
  sorry
  apply (simp add: id_on_def)
*)
(*
  apply (smt (verit, best) Diff_iff Diff_insert2 Diff_insert_absorb bij_id_imsupp
      id_on_def in_imsupp not_in_imsupp_same not_in_supp_alt usubst_simps(7))
  apply (smt (verit, del_insts) Diff_iff Diff_insert2 Diff_triv Int_Un_emptyI1 Int_commute
      Int_emptyD Int_image_imsupp One_nat_def Sup_UNIV Sup_UNIV bij_imsupp_supp_ne
      disjoint_iff_not_equal dmap_def dmap_def dpair.map_id0 dpair.rel_Grp dpair.set_map
      dset_def fun.rel_eq fun.rel_eq id_on_def in_imsupp not_in_imsupp_same
      not_in_supp_alt set_diff_eq term.FVars_permute term.inject(8) term.map(9)
      term.permute(9) term.vvsubst_permute usubst_simps(9))
  done
*)

lemma premute_term_usubst: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a ::var set| \<Longrightarrow> id_on (FVars M - {x::'a}) \<sigma> \<Longrightarrow>
  (permute_term \<sigma> M)[V <- \<sigma> x] = M[V <- x]"
(*
  unfolding usubst_def
  apply (subst premute_term_subst)
      apply (auto simp: bij_implies_inject id_on_def SSupp_def intro!: term.Sb_cong)
  subgoal for y
    apply (cases "x = y")
     apply auto
    sledgehammer

  sorry
*)

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

lemma Let_fresh_inject:
  assumes "|A| <o |UNIV :: 'a set|"
  shows "(term.Let xy M N = term.Let xy' M' N') =
   (\<exists>f. bij f \<and> |supp f :: 'a :: var set| <o |UNIV :: 'a set| \<and> id_on (FVars N \<union> A - dset xy) f \<and> dmap f xy = xy' \<and> M = M' \<and> permute_term f N = N')"
  sorry

lemma dfst_dmap[simp]: "bij f \<Longrightarrow> dfst (dmap f xy) = f (dfst xy)"
  by transfer auto
lemma dsnd_dmap[simp]: "bij f \<Longrightarrow> dsnd (dmap f xy) = f (dsnd xy)"
  by transfer auto
lemma dset_alt: "dset xy = {dfst xy, dsnd xy}"
  by transfer auto

lemma beta_deterministic: "M \<rightarrow> N \<Longrightarrow> M \<rightarrow> N' \<Longrightarrow> N = N'"
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
  subgoal premises prems for V W xy M N' using prems(6)
    apply - 
    apply(erule beta.cases)
                 apply(auto simp add: prems(1-5) dset_alt simp del: term.inject elim:beta.cases)
    apply (auto) []
    using normal_def prems(4,5) val.intros(3) vals_are_normal apply blast
    apply (subst (asm) Let_fresh_inject[of "FVars V \<union> FVars W"])
    apply auto
    apply (rule premute_term_usubst2[symmetric]; simp?)
    apply (auto simp add: Un_Diff dset_alt id_on_def prems(1))
     apply (metis Int_Un_empty dset_alt insert_disjoint(2) prems(1) term.set(8,9))
    apply (metis Int_Un_empty Int_emptyD bij_not_eq_twice dsel_dset(1,2) prems(1) term.set(8,9))
    done
  subgoal for N'
    apply (erule beta.cases)
    apply (auto elim:beta.cases)
    done
  subgoal for n N'
    apply (erule beta.cases)
                 apply (auto elim:beta.cases)
    using normal_def num.intros(2) nums_are_normal apply blast
    done
  subgoal premises prems for V f x M N' using prems(5)
    apply -
    apply (erule beta.cases)
                 apply(auto simp add: prems(1-4) dset_alt simp del: term.inject elim:beta.cases)
    apply (metis normal_def prems(4) term.inject(5) vals_are_normal)
    apply (metis normal_def term.inject(5) val.intros(4) vals_are_normal)
    apply auto
    sorry
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
  done

lemma FVars_beta: "M \<rightarrow> N \<Longrightarrow> FVars N \<subseteq> FVars M"
  apply(binder_induction M N avoiding: "App M N" rule:beta.strong_induct)
               apply(auto)
  subgoal premises prems for V f x M z
  proof -
    have "FVars M[V <- x][Fix f x M <- f] \<subseteq> FVars M \<union> FVars V"
      using FVars_usubst fresh_usubst by fastforce
    then have "z \<in> FVars M" using prems(2, 3) by auto
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

binder_inductive eval_ctx
  sorry

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

lemma blocked_fresh_hole:
  assumes "finite A" 
  shows "blocked z M = (\<exists> hole E. (\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- z]) \<and> (M = E[Var z <- hole]) \<and> (hole \<notin> insert z A))"
proof (rule iffI)
  obtain hole where "hole \<notin> insert z (A \<union> FVars M)"
    by (metis arb_element assms finite_FVars finite_Un finite_insert)
  assume "blocked z M"
  then obtain hole0 E0 where "eval_ctx hole0 E0" "M = E0[Var z <- hole0]" unfolding blocked_def by blast
  then show "\<exists> hole E. (\<forall>N. hole \<notin> FVars N \<longrightarrow> eval_ctx hole E[N <- z]) \<and> (M = E[Var z <- hole]) \<and> hole \<notin> insert z A"
    apply (binder_induction hole0 E0 arbitrary: M avoiding: M rule: eval_ctx_strong_induct)
            apply auto
    apply (metis finite_insert usubst_simps(5) assms eval_ctx.intros(1) arb_element insert_iff)
    sorry
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

lemma subst_comp:
  assumes "|SSupp Var f| <o |UNIV :: 'var set|" "|SSupp Var g| <o |UNIV :: 'var set|"
  shows "subst f (subst g t) = subst (subst f o g) (t :: 'var :: var term)"
  unfolding term.Sb_comp[OF assms(2,1), symmetric] o_apply ..

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
  ultimately have "eval_ctx hole' E'" using eval_subst[of hole E hole'] eval_ctx.intros
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

lemma val_stuck_step: "val M \<or> stuck M \<or> (\<exists>N. M \<rightarrow> N)"
  \<comment> \<open>Progress lemma. The original proof used \<open>stuck.intros\<close>, which does not exist
      (\<open>stuck\<close> is a definition, not an inductive), so it never compiled and left the
      theory in a bad state. Discharging this properly needs \<open>stuck\<close>-propagation through
      evaluation contexts (analogous to \<^theory_text>\<open>blocked_inductive\<close>) plus \<open>stuckEx_imp_stuck\<close>.\<close>
  sorry


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

notation Set.insert (infixr ";" 50)

inductive judgement :: "'var::var typing set \<Rightarrow> 'var::var typing set \<Rightarrow> bool" (infix "\<turnstile>" 10) where
  Id : "(Var x :. A) ; \<Gamma> \<turnstile> (Var x :. A) ; \<Delta>"
| ZeroR : "\<Gamma> \<turnstile> (Zero :. Nat) ; \<Delta>"
| SuccR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Succ M :. Nat) ; \<Delta>"
| PredR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Pred M :. Nat) ; \<Delta>"
| FixsR: "(Var f :. To A B) ; (Var x :. A) ; \<Gamma> \<turnstile> (M :. B) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Fix f x M :. To A B) ; \<Delta>"
| FixnR: "(Var f :. OnlyTo A B) ; (M :. B) ; \<Gamma> \<turnstile> (Var x :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Fix f x M :. OnlyTo A B) ; \<Delta>"
| AppR: "(M :. To B A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. B) ; \<Delta> \<Longrightarrow>  \<Gamma>  \<turnstile> (App M N :. A) ; \<Delta>"
| PairR: "\<Gamma> \<turnstile> (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. B) ; \<Delta> \<Longrightarrow>  \<Gamma>  \<turnstile> (Pair M N :. Prod A B) ; \<Delta>"
| LetR: "(M :. Prod B C) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Var (dfst x) :. B) ; (Var (dsnd x) :. C) ; \<Gamma> \<turnstile> (N :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (Let x M N :. A) ; \<Delta>"
| IfzR: "\<Gamma> \<turnstile> (M :. Nat) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (P :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (N :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (If M N P :. A) ; \<Delta>"
| Dis: "A || B \<Longrightarrow> \<Gamma> \<turnstile> (M :. B) ; \<Delta> \<Longrightarrow> (M :. A); \<Gamma> \<turnstile> \<Delta>"
| PairL1: "(M :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M N :. Prod A B) ; \<Gamma> \<turnstile> \<Delta>"
| AppL: "(M :. OnlyTo B A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. B) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| SuccL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Succ M :. Nat) ; \<Gamma> \<turnstile> \<Delta>"
| PredL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pred M :. Nat) ; \<Gamma> \<turnstile> \<Delta>"
| IfzL1: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile> \<Delta>"
| IfzL2: "(N :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (P :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (If M N P :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL1: "(N :. A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL2_1: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. A) ; \<Gamma> \<turnstile> (Var (dfst x) :. B1) ; \<Delta> \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| LetL2_2: "(M :. Prod B1 B2) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (N :. A) ; \<Gamma> \<turnstile> (Var (dsnd x) :. B1) ; \<Delta> \<Longrightarrow> (Let x M N :. A) ; \<Gamma> \<turnstile> \<Delta>"
| OkVarR: "\<Gamma> \<turnstile> (Var x :. Ok) ; \<Delta>"
| OkL: "(M :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile> \<Delta>"
| OkR: "\<Gamma> \<turnstile> (M :. A) ; \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> (M :. Ok) ; \<Delta>"
| OkApL1: "(M :. OnlyTo Ok A) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkApL2: "(N :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (App M N :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkSL: "(M :. Nat); \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Succ M :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPL: "(M :. Nat) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pred M :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPrL_1: "(M1 :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta>"
| OkPrL_2: "(M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (Pair M1 M2 :. Ok) ; \<Gamma> \<turnstile> \<Delta>"

binder_inductive (no_auto_equiv) judgement
  sorry

thm judgement.strong_induct

lemma weakenL: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> (M :. A) ; \<Gamma> \<turnstile> \<Delta>"
  apply (induction \<Gamma> \<Delta> rule:judgement.induct)
  apply (auto intro: judgement.intros simp add: insert_commute[of "M :. A" _])
  done

lemma weakenR: "\<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma>  \<turnstile> (M :. A) ; \<Delta>"
  apply (induction \<Gamma> \<Delta> rule:judgement.induct)
  apply (auto intro: judgement.intros simp add: insert_commute[of "M :. A" _])
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

inductive semantic_judgement :: "'var::var typing set \<Rightarrow> 'var typing set \<Rightarrow> bool" (infix "\<Turnstile>" 10) where
  "\<forall>\<theta>. (\<forall>\<tau>\<in>L. typing_semanticsL \<theta> \<tau>) \<longrightarrow> (\<forall>\<tau>\<in>R. typing_semanticsR \<theta> \<tau>) \<Longrightarrow> L \<Turnstile> R"

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
  assumes "M[t <- x] = Fix f z Q" and "\<not> M = Var x"
  assumes "f \<noteq> x" and "f \<notin> FVars t" and "x \<noteq> z" and "z \<notin> FVars t"
  obtains Q' where "M = Fix f z Q'" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
          apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  subgoal for f' z' Q' \<sigma>
    sorry

  thm avoiding_bij
  done

lemma subst_Let_inversion:
  assumes "M[t <- x] = Let xy P Q" and "\<not> M = Var x"
  assumes "x \<notin> dset xy" and "FVars t \<inter> dset xy = {}"
  obtains P' Q' where "M = Let xy P' Q'" and "P'[t <- x] = P" and "Q'[t <- x] = Q"
  using assms
  apply(atomize_elim)
  apply(binder_induction M avoiding: M t x rule:term.strong_induct)
  apply(auto simp add:blocked_inductive Int_Un_distrib split:if_splits)
  sorry

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
    using blocked_inductive \<open>\<not> blocked z V'\<close> by metis
  then have "val V1'" using \<open>V1'[N <- z] = V1\<close> "3.IH"(1)[of V1'] by auto
  then have "\<not> blocked z V2'"
    using blocked_inductive \<open>\<not> blocked z V'\<close> \<open>V' = term.Pair V1' V2'\<close> by metis
  then have "val V2'" using \<open>V2'[N <- z] = V2\<close> "3.IH"(2)[of V2'] by auto
  show ?case using \<open>val V1'\<close> \<open>val V2'\<close> \<open>V' = Pair V1' V2'\<close> val.intros by auto
next
  case (4 f x M V')
  then obtain M' where "V' = Fix f x M'" and "M'[N <- z] = M"
    using subst_Fix_inversion[of V' N z f x M] blocked_inductive(1)
    by (metis Un_empty_right Un_insert_right insertCI insert_disjoint(2) term.set(5,6))
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
    using blocked_inductive \<open>M = Pair Q1 Q2\<close> by metis
  ultimately obtain E' P' where "E'[N <- z] = E" and "P'[N <- z] = P" and "Q1 = E'[P' <- x]" and "eval_ctx x E'"
    using 6(2)[where M = Q] 6 by fastforce
   moreover have "x \<notin> FVars Q2"
    using 6 \<open>x \<notin> FVars M \<union> FVars P \<union> FVars N\<close> \<open>M = Pair Q1 Q2\<close>
    by simp
  ultimately have "M = (Pair E' Q2)[P' <- x] \<and> Pair E Q = (Pair E' Q2)[N <- z] \<and> P = P'[N <- z]"
    by (simp add: \<open>M = term.Pair Q1 Q2\<close> \<open>Q = Q2[N <- z]\<close>)
  also have "eval_ctx x (Pair E' Q2)" using \<open>eval_ctx x E'\<close> \<open>x \<notin> FVars Q2\<close> eval_ctx.intros by metis
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
  also have "eval_ctx x (Pair V' E')" using \<open>eval_ctx x E'\<close> \<open>x \<notin> FVars V'\<close> \<open>val V'\<close> eval_ctx.intros by metis
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
  also have "eval_ctx hole (Let x E' Q')" using \<open>eval_ctx hole E'\<close> \<open>hole \<notin> FVars Q'\<close> eval_ctx.intros(8)[of hole E'] sorry
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
  also have "eval_ctx x (If E' Q1' Q2')" using q1 q2 ctxxE eval_ctx.intros by metis
  ultimately show ?case by blast
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
then show ?case sorry
next
  case (1 hole p' M)
  have "p' = (z, N, M, Var hole, hole, P1, P2) \<Longrightarrow>
       M[N <- z] = (Var hole)[P1 <- hole] \<Longrightarrow>
       \<not> blocked z M \<Longrightarrow>
       \<exists>M'. M \<rightarrow> M' \<and>  M'[N <- z] = (Var hole)[P2 <- hole]"
    using 1(3)
proof (binder_induction P1 P2 avoiding: z N M rule:beta.strong_induct[unfolded Un_insert_right Un_empty_right, consumes 1])
    case (2 N N' f x Q)
    then show ?case sorry
  next
    case (3 Q Q' N)
    then show ?case sorry
  next
    case (4 Q Q')
    then show ?case sorry
  next
    case (5 Q Q')
    then show ?case sorry
  next
    case (6 Q Q' N)
    then show ?case sorry
  next
    case (7 V N N')
    then show ?case sorry
  next
    case (8 Q Q' xy N)
    then show ?case sorry
  next
    case (9 Q Q' N P)
    then show ?case sorry
  next
    case (10 P2 Q)
    then have "M[N <- z] = If Zero P2 Q" by simp
    then obtain Q0 Q1 Q2
      where "M = If Q0 Q1 Q2" and "Q0[N <- z] = Zero" and "Q1[N <- z] = P2" and "Q2[N <- z] = Q"  and "\<not> blocked z Q0"
      using  \<open>\<not> blocked z M\<close> subst_If_inversion[of M N z Zero P2 Q] blocked_inductive by metis
    then have "Q0 = Zero"
      using subst_Zero_inversion blocked_inductive(1) by blast
    then show ?case
      using \<open>M = term.If Q0 Q1 Q2\<close> \<open>Q1[N <- z] = P2\<close> beta.Ifz by auto
  next
    case (11 Q Q1 P2)
    then have "M[N <- z] = term.If (Succ Q) Q1 P2" by simp
    then obtain Q0' Q1' Q2'
      where "M = If Q0' Q1' Q2'" and "Q0'[N <- z] = (Succ Q)" and "Q1'[N <- z] = Q1" and "Q2'[N <- z] = P2"  and "\<not> blocked z Q0'"
      using  \<open>\<not> blocked z M\<close> subst_If_inversion[of M N z "Succ Q" Q1 P2] blocked_inductive by metis
    then have "Q0' = Succ Q"
       using 11(1) num.intros(2) subst_num_inversion by blast
     then show ?case
      using \<open>M = term.If Q0' Q1' Q2'\<close> \<open>Q2'[N <- z] = P2\<close> beta.Ifs 11(1) by auto
  next
    case (12 V W xy Q)
    then have "M[N <- z] = Let xy (Pair V W) Q" by simp
    then obtain P' Q' where "M = Let xy P' Q'" and "P'[N <- z] = Pair V W" and "Q'[N <- z] = Q"
      using subst_Let_inversion[of M N z xy "Pair V W" Q] \<open>\<not> blocked z M\<close> 12(1) 12(2) blocked_inductive(1)
      by blast
    moreover have "\<not> blocked z P'" using blocked_inductive(8)[of z P'] \<open>M = Let xy P' Q'\<close> 1(4) 12(1,3)
      by auto
    ultimately obtain V' W' where "P' = Pair V' W'" and "V'[N <- z] = V" and "W' [N <- z] = W" and "\<not> blocked z V'"
      using subst_Pair_inversion blocked_inductive(1, 6) by metis
    then have "val V'"
      using subst_val_inversion \<open>val V\<close> \<open>val W\<close> by auto
    then have "\<not> blocked z W'" using \<open>P' = Pair V' W'\<close> \<open>\<not> blocked z P'\<close> blocked_inductive(7) by auto
    then have "val W'" using subst_val_inversion \<open>W'[N <- z] = W\<close> \<open>val W\<close> by auto
    have "(Q'[V' <- dfst xy][W' <- dsnd xy])[N <- z] = Q[V <- dfst xy][W <- dsnd xy]"
      using usubst_usubst[of "dsnd xy" z N "Q'[V' <- dfst xy]" W'] usubst_usubst[of "dfst xy" z N Q' V']
      using 12(1) 12(2) \<open>Q'[N <- z] = Q\<close> \<open>V'[N <- z] = V\<close> \<open>W'[N <- z] = W\<close>
      by (metis Int_emptyD  dsel_dset(1,2))
    then show ?case
      using \<open>M = term.Let xy P' Q'\<close> \<open>P' = term.Pair V' W'\<close> beta.Let usubst_simps(5)
      using \<open>val V'\<close> \<open>val W'\<close>
      by metis
  next
    case 13
    then have "M[N <- z] = Pred Zero" by simp
    then obtain Q where "M = Pred Q" and "\<not> blocked z Q" and "Q[N <- z] = Zero" using subst_Pred_inversion
      by (metis "1"(4) blocked_inductive(1,5))
    then have "Q = Zero" using \<open>Q[N <- z] = Zero\<close> \<open>\<not> blocked z Q\<close> subst_Zero_inversion blocked_inductive(1) by auto
    have "(Zero)[N <- z] = Zero" by simp
    then show ?case
      using \<open>M = Pred Q\<close> \<open>Q = Zero\<close> assms(3) PredZ by auto
  next
    case (14 P2)
    then have "M[N <- z] = Pred (Succ P2)" by simp
    then obtain Q where "M = Pred Q" and "\<not> blocked z Q" and "Q[N <- z] = Succ P2" using subst_Pred_inversion
      by (metis "1"(4) blocked_inductive(1,5))
    then obtain Q' where "Q = Succ Q'" and "\<not> blocked z Q'" and "Q'[N <- z] = P2"
      using subst_Succ_inversion blocked_inductive(1, 4) by metis
    moreover have "num Q'" using subst_num_inversion \<open>Q'[N <- z] = P2\<close> \<open>\<not> blocked z Q'\<close> \<open>num P2\<close>
      by metis
    ultimately show ?case
      using \<open>M = Pred Q\<close> PredS by force
  next
    case (15 V f x Q)
    then have "M[N <- z] = App (Fix f x Q) V" by simp
    then obtain Q' V' where "M = App (Fix f x Q') V'" and "Q'[N <- z] = Q" and "V'[N <- z] = V"
      using  \<open>\<not> blocked z M\<close> subst_Fix_inversion subst_App_inversion blocked_inductive(1,3) 15(1,2)
      by (metis insert_disjoint(2) insert_iff)
    moreover have "(Fix f x Q')[N <- z] = Fix f x Q"
      using 15(1) 15(2) \<open>Q'[N <- z] = Q\<close> by auto 
    ultimately have *: "Q'[V' <- x][Fix f x Q' <- f][N <- z] = Q[V <- x][Fix f x Q <- f]"
      using usubst_usubst[of f z N "Q'[V' <- x]" "Fix f x Q'"] usubst_usubst[of x z N "Q'" "V'"]
      using 15(1) 15(2)
      by (metis insert_disjoint(2) insert_iff)
    have "\<not> blocked z V'" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = App (Fix f x Q') V'\<close> by blast
    then have "val V'" using subst_val_inversion \<open>val V\<close> \<open>V'[N <- z] = V\<close> by auto
    then show ?case
      using \<open>M = App (Fix f x Q') V'\<close> beta.FixBeta usubst_simps(5) * by metis
  qed
  then show ?case using 1 by auto
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
  then have "\<not> blocked z Q" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = Pair V' Q\<close> by metis
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
  then have "\<not> blocked z Q0'" using blocked_inductive \<open>\<not> blocked z M\<close> \<open>M = If Q0' Q1' Q2'\<close> by metis
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
  sorry (* this will work once binder_induction works*)

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

lemma val_subst: "val V \<Longrightarrow> V \<noteq> Var x \<Longrightarrow> val V[Q <- x]"
  apply(binder_induction V avoiding: "App Q (Var x)" rule: val.strong_induct)
     apply(auto intro:val.intros)
  oops

lemma eval_ctx_subst: "eval_ctx x E \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> FVars Q \<Longrightarrow> eval_ctx x E[Q <- y]"
  apply(induction rule:eval_ctx.induct)
  apply(auto intro:eval_ctx.intros simp add:)
  sorry (*Questionably True*)

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
  have "\<not> blocked z V" using \<open>\<not> blocked z (Pair V Na)\<close> blocked_inductive by metis
  then have "val V[Q <- z]" using \<open>val V\<close> sorry
  then show ?case using OrdPair2 beta.intros(6) \<open>\<not> blocked z Na\<close> by auto
next
  case (OrdLet Ma M' xy Na)
  then show ?case sorry
next
  case (Let xy V W Ma)
  then show ?case sorry
next
  case (FixBeta f xa Ma V)
  then show ?case sorry
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

definition b5_prop :: "'var::var term \<Rightarrow> 'var term \<Rightarrow> 'var term \<Rightarrow> 'var term \<Rightarrow> 'var \<Rightarrow>  bool" where
  "b5_prop V W P N z \<equiv> (\<not> haveFix V \<longrightarrow> W = V) \<and> 
    (\<forall>V1 V2. V = Pair V1 V2 \<longrightarrow> (\<exists>W1 W2. W = Pair W1[P <- z] W2[P <- z] \<and> W1[N <- z] = V1 \<and> W2[N <- z] = V2)) \<and>
    (\<forall>f x R. V = Fix f x R \<longrightarrow> z \<noteq> f \<longrightarrow> z \<noteq> x \<longrightarrow> (\<exists>Q. W = Fix f x Q[P <- z] \<and> Q[N <- z] = R))"

lemma Succ_beta_star: "n \<rightarrow>* m \<Longrightarrow> Succ n \<rightarrow>* Succ m"
proof -
  assume "n \<rightarrow>* m"
  obtain x :: 'a where "eval_ctx x (Succ (Var x))"
    using eval_ctx.intros by blast
  then show ?thesis 
    using eval_ctx_beta_star[of x "Succ (Var x)" n m] \<open>n \<rightarrow>* m\<close>
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
    using diverge.cases beta.intros by metis
  then show ?case by auto
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
    assume fxR': "f' \<noteq> z" "x' \<noteq> z" "Fix f x R = Fix f' x' R'"
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
        using \<open>M[P <- z] \<rightarrow>* U[P <- z]\<close> \<open>U = Succ W'\<close> eval_ctx.intros(1,4)
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
    have "f \<noteq> z" and "f \<notin> FVars N" and "x \<noteq> z" and "x \<notin> FVars N" and "f \<notin> FVars P" and "x \<notin> FVars P" sorry
    then obtain Q where q1: "U = Fix f x Q" and q2: "Q[N <- z] = R"
      using subst_Fix_inversion[of U N z f x R] \<open>U \<noteq> Var z\<close> U1
      by auto
    then have "b5_prop (Fix f x R) U[P <- z] P N z" unfolding b5_prop_def
      using \<open>f \<noteq> z\<close> \<open>x \<noteq> z\<close> \<open>f \<notin> FVars P\<close> \<open>x \<notin> FVars P\<close> haveFix.intros(1)
(*
      by (metis term.distinct(63) usubst_simps(7))
*)
      sorry
    moreover have "val U[P <- z]" using q1 val.intros(4)
      by (simp add: \<open>f \<noteq> z\<close> \<open>f \<notin> FVars P\<close> \<open>x \<noteq> z\<close> \<open>x \<notin> FVars P\<close>)
    ultimately show ?thesis using U2 by auto
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
    case (3 V M)
    then show ?thesis
      using 3 vals_are_normal[of V] steps beta.cases[of M M'] unfolding normal_def
(*
      by (smt (verit) beta.cases term.distinct(42,43,44,62,70) term.inject(5))
*)
      sorry
  next
    case (4 V xy M)
    then show ?thesis sorry
  qed
qed

lemma stucks_are_normal: "stuck M \<Longrightarrow> normal M"
proof(rule ccontr)
  assume "stuck M"
  then obtain hole E N where ctx: "eval_ctx hole E" and "M = E[N <- hole]" and "stuckEx N"
    unfolding stuck_def by auto
  assume "\<not> normal M"
  then obtain M' where "M \<rightarrow> M'" unfolding normal_def by auto
  then show False sorry 
qed

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
    using eval_ctx.intros
    by (metis UnCI arb_element finite_FVars term.set(8))
  then show ?thesis 
    using eval_ctx_beta_star[of x "App (Var x) M" V V'] \<open>V \<rightarrow>* V'\<close>
    by auto
qed

lemma Let_beta_star: "V \<rightarrow>* V' \<Longrightarrow> Let xy V M \<rightarrow>* Let xy V' M"
proof -
  assume "V \<rightarrow>* V'"
  obtain x :: 'a where "eval_ctx x (Let xy (Var x) M)" and "x \<notin> FVars M" and "x \<notin> dset xy"
    using eval_ctx.intros(1, 9) dset_finite
    using UnCI arb_element finite_FVars sorry
  then show ?thesis 
    using eval_ctx_beta_star[of x "Let xy (Var x) M" V V'] \<open>V \<rightarrow>* V'\<close>
    sorry
  thm usubst_simps(9)[of x xy V "Var x" M]
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
proof (binder_induction V avoiding: "Var z" rule:val.strong_induct)
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
  case (4 f x)
  then show ?thesis using b5 unfolding b5_prop_def
    by (metis Un_Int_eq(1,2) empty_not_insert haveFix.intros(1) num_not_haveFix term.set(5))
qed

lemma b5_prop_not_pair: 
assumes "val V" and nNum: "\<nexists>V1 V2. V = Pair V1 V2" and b5: "b5_prop V W P N z"
  shows "\<nexists>W1 W2. W = Pair W1 W2"
  using assms
proof (binder_induction V avoiding: "Var z" rule:val.strong_induct)
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
  case (4 f x)
  then show ?thesis using b5 unfolding b5_prop_def
    by (metis Un_Int_eq(1,2) empty_not_insert term.Vrs_Inj term.distinct(63))
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
        fresh_hole: "hole' \<notin> (z ; FVars P)"
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
        qed
      then show ?thesis sorry 
      (*how would be obtain stuck R[P <- z] from stuckEx Q'[P <- z], knowing that I may have F[P <- z] not an eval_ctx*)
    qed
  qed(auto)
qed

section \<open>Thm 4.7\<close>

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
      using val_stuck_step diverge_or_normalizes sorry
    then show ?case
      proof cases
        case A
        then obtain V where "M[N <- z] \<rightarrow>* V" and "val V" and "V \<notin> \<lblot>Nat\<rblot>"
          using 2 unfolding tau_semantics.simps by blast
        then obtain W where "diverge M[Q <- z] \<or> M[Q <- z] \<rightarrow>* W" (*W same type of value as V*)
          using b5[of V z N M Q] b5_prop_def[of V] sorry
        then show ?thesis sorry
      next
        case B
        then have "diverge M[Q <- z] \<or> getStuck M[Q <- z]"
          using ls nzN b6[of M N z Q] by auto
        then show ?thesis unfolding tau_semantics.simps sorry (*need val xor stuck*)
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
        then obtain W where M2W: "M[Q <- z] \<rightarrow>* W" and "b5_prop (term.Pair V1 V2) W Q N z" by auto
        then obtain W1 W2 where "W = Pair W1[Q <- z] W2[Q <- z]" and "W1[N <- z] = V1" and "W2[N <- z] = V2"
          unfolding b5_prop_def
          sorry
        then have "W1[N <- z] \<in> \<lblot>A1\<rblot>" and "W2[N <- z] \<in> \<lblot>A2\<rblot>"
          using \<open>V1 \<in> \<lblot>A1\<rblot>\<close> \<open>V2 \<in> \<lblot>A2\<rblot>\<close> by auto
        then have "W1[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>" and "W2[N <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" 
          unfolding bottom_semantics.simps tau_semantics.simps 
          using beta_star_def betas.refl sorry
        then have "W1[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A1\<rblot>" and "W2[Q <- z] \<in> \<T>\<^sub>\<bottom>\<lblot>A2\<rblot>" 
          using Prod.IH(1)[of W1] Prod.IH(3)[of W2] by auto
        then consider (a) "diverge W1[Q <- z] \<or> diverge W2[Q <- z]" | (b) "W1[Q <- z] \<in> \<T>\<lblot>A1\<rblot> \<and> W2[Q <- z] \<in> \<T>\<lblot>A2\<rblot>"
          unfolding bottom_semantics.simps by auto
        then show ?thesis
        proof cases
          case a
          then have "diverge W"
            using \<open>W = Pair W1[Q <- z] W2[Q <- z]\<close> sorry
          then show ?thesis using beta_star_diverge_back M2W by auto
        next
          case b
          then have "W \<in> \<T>\<lblot>Prod A1 A2\<rblot>" unfolding tau_semantics.simps type_semantics.simps
            sorry
          then have "M[Q <- z] \<in> \<T>\<lblot>Prod A1 A2\<rblot>" unfolding tau_semantics.simps
            using M2W beta_star_sums by blast
          then show ?thesis unfolding bottom_semantics.simps by auto
        qed
      qed(auto)
    qed
  next
    case 2
    then show ?case sorry
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
    then show ?case sorry
  next
    case 2
    then show ?case sorry
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
