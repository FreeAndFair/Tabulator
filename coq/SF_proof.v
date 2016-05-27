Require SF_imp.
Require SF_spec.
Require Import SF_lemma.
Require Import SF_properties.
Require Import SF_opt.
Require Import RelDec.
Require Import List.
Require Import Sorted.
Require Import Permutation.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import SF_tactic.
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Omega.

Import ListNotations.


Section cand.

Variable candidate : Set.
Variable reldec_candidate : RelDec (@Logic.eq candidate).
Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.

Local Open Scope N_scope.

Ltac solve_rcv := SF_tactic.solve_rcv reldec_correct_candidate.
Ltac intuition_nosplit := SF_tactic.intuition_nosplit reldec_correct_candidate.

Lemma no_viable_candidates_correct :
forall rec bal,
SF_imp.no_viable_candidates candidate _ rec bal = true ->
SF_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
solve_rcv.
specialize (H _ H0). solve_rcv.
apply H in H1.
Unset Ltac Debug.
solve_rcv.
Qed.



Lemma eliminated_correct :
forall rec can,
SF_imp.eliminated candidate _ rec can = true <->
in_record rec can.
Proof.
split; solve_rcv.
 exists x. solve_rcv. intuition.
 exists can.  solve_rcv.
Qed.


Ltac force_specialize P :=
repeat
match goal with
| [ H : _ |- _] => extend (P H)
end.

Ltac force_specialize_all :=
repeat
match goal with
| [ H : (forall x, _) |- _ ] => progress (force_specialize H)
end.



Lemma next_ranking_not_overvote :
forall rec bal cd bal' a,
SF_imp.next_ranking candidate _ rec (a :: bal) = Some (cd, bal') ->
~SF_spec.overvote candidate a.
Proof.
intros. intro.
simpl in *.
destruct a; solve_rcv;
force_specialize_all;
simpl in *; intuition; subst; solve_rcv.
Qed.

Lemma next_ranking_selects : forall a bal cd bal' rec,
    SF_imp.next_ranking candidate reldec_candidate rec (a :: bal) =
    Some (cd, bal') ->
    SF_spec.does_not_select candidate (in_record rec) a ->
    SF_imp.next_ranking candidate reldec_candidate rec (bal) = Some (cd, bal').
Proof.
intros.
destruct a; simpl in *; solve_rcv.
destruct H0; solve_rcv.
assert (x=cd).
simpl in H0; intuition; force_specialize_all; solve_rcv.
subst. clear H0.
force_specialize_all; solve_rcv.
force_specialize_all; solve_rcv.
Qed.

Hint Resolve next_ranking_not_overvote : rcv.

Lemma next_ranking_correct :
forall rec bal cd bal' ,
SF_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
exists h t,(SF_spec.next_ranking candidate (in_record rec) bal (h::t) /\ Forall (Logic.eq cd) (h::t)).
Proof.
intros.
induction bal.
- solve_rcv.
- solve_rcv.
  destruct (SF_spec.ranking_cases _  (in_record rec) a); [ | destruct H0].
  + apply next_ranking_not_overvote in H. intuition.
  + solve_rcv. destruct a; simpl in *; solve_rcv.
    * { destruct H1.
        - exfalso. apply H2.
          subst. exists x2. auto.
        - exists x0; exists (x1); solve_rcv.
          + constructor; solve_rcv.
            * exists x2. split; auto.
              destruct H7. subst; auto.
              force_specialize_all; solve_rcv.
            * force_specialize_all; solve_rcv.
      }
    * { destruct H1.
        - subst. exists x. exists a. solve_rcv.
          eapply SF_spec.next_ranking_valid; solve_rcv.
        - exists cd.  exists a.
          solve_rcv. eapply SF_spec.next_ranking_valid; solve_rcv.
          simpl in H1. intuition.
          force_specialize_all; solve_rcv.
      }
  + apply next_ranking_selects in H; auto.
    solve_rcv.
    exists x; solve_rcv. exists x0.
    destruct H0; solve_rcv. constructor; solve_rcv.
    constructor; solve_rcv. force_specialize_all; solve_rcv.
    force_specialize_all; solve_rcv.
Qed.



Lemma next_ranking_viable :
forall bal rec cd bal',
SF_imp.next_ranking candidate reldec_candidate rec bal =
      Some (cd, bal') ->
~SF_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
induction bal; intros.
- simpl in *. congruence.
- simpl in *. destruct a.
  + intro. apply no_viable_candidates_cons in H0. destruct H0.
    eapply IHbal in H1; eauto.
  + destruct (forallb (eq_dec c) a).
    * { destruct (SF_imp.eliminated candidate reldec_candidate rec c) eqn:?.
        - apply eliminated_correct in Heqb.
          intro. apply no_viable_candidates_cons in H0.
          destruct H0.
          eapply IHbal in H1; eauto.
        - inv H. intro. apply no_viable_candidates_cons in H. destruct H.
          unfold SF_spec.no_viable_candidates in H.
          specialize (H (cd :: a)). simpl in H. intuition. clear H2.
          specialize (H cd). intuition. clear H2.
          rewrite <- eliminated_correct in H. congruence.
      }
    * congruence.
Qed.


Lemma next_ranking_selected :
forall bal cd bal' rec,
SF_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
SF_spec.selected_candidate candidate (in_record rec) bal cd.
solve_rcv.
- destruct H0.
 + apply H0; clear H0.
   apply next_ranking_correct in H.
   solve_rcv.
 + destruct bal; solve_rcv.
   copy H.
   apply next_ranking_correct in H. solve_rcv.
   unique; subst.
   force_specialize_all; solve_rcv.
- apply next_ranking_correct in H; solve_rcv.
  exists (x :: x0); solve_rcv.  simpl in *.
  force_specialize_all; solve_rcv; intuition.
Qed.

Lemma next_ranking_eliminated :
forall bal rec,
SF_imp.next_ranking candidate _ rec bal = None ->
SF_spec.exhausted_ballot candidate (in_record rec) bal.
Proof.
intros.
induction bal.
- left. solve_rcv.
- simpl in *. destruct a; solve_rcv.
  + destruct IHbal; solve_rcv.
    * left. intro. apply H0. solve_rcv.
      exists x. inv H1; solve_rcv.
    * right. exists x. solve_rcv. constructor; solve_rcv.
  + destruct IHbal.
    * left. intro. apply H2; solve_rcv.
      { inv H3.
        - solve_rcv.
        - destruct H8; solve_rcv.
          + exfalso. simpl in *. repeat (intuition; subst); force_specialize_all; solve_rcv.
          + inv H6; solve_rcv.
            * exfalso. apply H3. clear H3. exists x; solve_rcv.
            * force_specialize_all. solve_rcv.
              exfalso. apply H3; solve_rcv.
      }
    * right. solve_rcv.
      exists x1; solve_rcv.
      constructor; solve_rcv. exists x; inv H6; force_specialize_all; solve_rcv.
      simpl in *. intuition; force_specialize_all; solve_rcv.
  + right. clear IHbal. exists (c::a). solve_rcv.
    eapply SF_spec.next_ranking_valid. simpl. auto.
    left. solve_rcv. exists x. exists c.
    simpl. auto.
    exists x. exists c. simpl. auto.
Qed.


Definition boolCmpToProp {A} (c : A -> A -> bool) :=
fun a b => match c a b with
           | true => True
           | false => False
end.

Lemma insert_sorted : forall {A} c sorted (a : A),
    (forall a b, c a b = false -> c b a = true) ->
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (SF_imp.insert c a sorted).
intros.
induction H0.
- simpl. auto.
- simpl.
  destruct (c a a0) eqn:?.
  constructor. auto. constructor. unfold boolCmpToProp. rewrite Heqb. auto.
  constructor. auto.
  clear IHSorted H0.
  induction l.
  + simpl in *.
    constructor. unfold boolCmpToProp. apply H in Heqb. rewrite Heqb.
    auto.
  + simpl in *. destruct (c a a1) eqn:?. constructor. apply H in Heqb.
    unfold boolCmpToProp. rewrite Heqb. auto.
    constructor; auto.
    unfold boolCmpToProp.
    apply H in Heqb. inv H1. unfold boolCmpToProp in H2.
    auto.
Qed.


Lemma insertion_sort_sorted' : forall {A} (l : list A) (sorted : list A) c,
    (forall a b, c a b = false -> c b a = true) ->
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (SF_imp.insertionsort' c l sorted).
Proof.
induction l.
+ intros. simpl. auto.
+ intros. simpl in *. apply IHl; auto.
  apply insert_sorted; auto.
Qed.

Lemma insertion_sort_sorted : forall {A} (l : list A) c,
    (forall a b, c a b = false -> c b a = true) ->
    Sorted (boolCmpToProp c) (SF_imp.insertionsort c l).
intros.
apply insertion_sort_sorted'; auto.
Qed.

Lemma insert_permutation :
  forall {A} l2 l1  (a : A) c,
    Permutation l1 l2 ->
    Permutation (a :: l1) (SF_imp.insert c a l2).
Proof.
induction l2; intros.
- apply Permutation_sym in H. apply Permutation_nil in H. subst. simpl in *. auto.
- simpl in *. destruct (c a0 a).
  constructor. auto.
  eapply Permutation_trans. instantiate (1:= (a0 :: a :: l2)).
  auto. rewrite perm_swap. constructor.
  apply IHl2. auto.
Qed.


Lemma insertion_sort_permutation' :
  forall {A} (le ls : list A) c sorted,
    Permutation ls sorted ->
    Permutation (ls ++ le) (SF_imp.insertionsort' c le sorted).
Proof.
induction le; intros.
- simpl in *. rewrite app_nil_r. auto.
- simpl. rewrite <- Permutation_middle.
  rewrite app_comm_cons.
  apply IHle. apply insert_permutation. auto.
Qed.

Lemma insertion_sort_permutation :
  forall {A} (l : list A) c,
    Permutation l (SF_imp.insertionsort c l).
intros. rewrite <- app_nil_l at 1.
unfold SF_imp.insertionsort.
apply insertion_sort_permutation'. auto.
Qed.


Definition tb_func_to_Prop {c : Set} (f : list c -> option c) :=
fun l cd => match f l with
         | Some x => x = cd
         | None => False
end.


Lemma in_split : forall A B (f : A) (l : list (A * B)),
              In f (fst (split l)) ->
              exists n : B, In (f, n) l.
Proof.
induction l; intros.
- simpl in *. inv H.
- simpl in *. destruct a. simpl in *.
  destruct (split l) eqn:?.
  simpl in *. destruct H.
  + subst. eauto.
  + intuition. destruct H0. eauto.
Qed.



Lemma rel_dec_refl : forall c, rel_dec c c = true.
Proof.
intros. apply rel_dec_correct. auto.
Qed.

Lemma increment_spec : forall (m : list (candidate *  N)) cd cds (ct : N),
cds = (fst (split m)) ->
NoDup (cds) ->
(In (cd, ct) m -> In (cd, (ct + 1)%N) (SF_imp.increment candidate _ m cd)) /\
(~In cd cds -> In (cd, 1%N) (SF_imp.increment candidate _ m cd)).
Proof.
induction m; intros.
- simpl in *. intuition.
- simpl in *. destruct a.
  destruct (split m) eqn:?.
  simpl in *.
  destruct (in_dec rel_dec_p cd cds).
  + subst.
    split.
    * { intros. simpl in *.
        unfold eq_dec.
        intuition.
        - inv H2.  rewrite rel_dec_refl.
          simpl. auto.
        - subst. clear -Heqp H2 H0.
          inv H0. assert (In cd l). apply in_split_l in H2.
          simpl in H2. rewrite Heqp in *. auto.
          intuition.
        - inv H2. inv H0. intuition.
        - assert (c <> cd).
          intro. subst. inv H0. intuition.
          eapply rel_dec_neq_false in H.
          rewrite H. simpl. right.
          edestruct IHm. reflexivity.
          inv H0; auto.
          clear H4. auto. apply reldec_correct_candidate.
      }
    * intuition.
  + subst. simpl in *. inv H0. unfold eq_dec.
    split.
      * { intuition.
        - inv H0. intuition.
        - eapply rel_dec_neq_false in H. rewrite H.
          edestruct IHm; eauto. simpl in *. auto.
          apply reldec_correct_candidate.
        }
      * intuition. eapply rel_dec_neq_false in H4. rewrite H4.
        simpl.
        edestruct IHm; eauto.
        eapply reldec_correct_candidate.
Grab Existential Variables. exact 0.
Qed.


Lemma increment_not_0 : forall running cd,
NoDup (fst (split running)) ->
~In (cd, 0) (SF_imp.increment candidate reldec_candidate running cd).
Proof.
induction running; intros; intro.
- unfold SF_imp.increment in *. simpl in *; intuition. congruence.
- simpl in *. destruct a. destruct (eq_dec c cd) eqn:?.
  + clear IHrunning. apply reldec_correct_candidate in Heqb. subst.
    simpl in *. destruct (split running) eqn:?. simpl in *.
    inv H. intuition. inv H. rewrite N.add_comm in H1. rewrite N.eq_add_0 in H1.
    intuition. congruence.  apply in_split_l in H.
    simpl in H. rewrite Heqp in H. simpl. intuition.
  + simpl in *. destruct (split running) eqn:?. simpl in *.
    apply neg_rel_dec_correct in Heqb. destruct H0.
    * inv H0. auto.
    * inv H. intuition. eapply IHrunning; eauto.
Qed.

Lemma increment_nodup' : forall running cd c,
~In c (fst (split running)) ->
c <> cd ->
~In c (fst (split (SF_imp.increment candidate reldec_candidate running cd))).
Proof.
induction running; intros.
- simpl in *. intuition.
- simpl in *.
  destruct a.
  destruct (split running) eqn:?. simpl in H. intuition.
  destruct (eq_dec c0 cd) eqn:?.
  + simpl in *. rewrite Heqp in *. simpl in *. intuition.
  + simpl in *. destruct (split
                   (SF_imp.increment candidate reldec_candidate running cd)) eqn:?.
    simpl in *. intuition. eapply IHrunning; eauto.
    rewrite Heqp0. simpl. auto.
Qed.

Lemma increment_nodup : forall running cd,
NoDup (fst (split running)) ->
NoDup (fst (split (SF_imp.increment candidate reldec_candidate running cd))).
induction running; intros.
- simpl in *. constructor; auto.
- simpl in *. destruct a. destruct (eq_dec c cd) eqn:?.
  + apply reldec_correct_candidate in Heqb. subst.
    simpl in *.
    destruct (split running) eqn:?. simpl in *. auto.
  + simpl in *. destruct ( split (SF_imp.increment candidate reldec_candidate running cd)) eqn:?.
    simpl.
    destruct (split running) eqn:?. simpl in *. inv H.
    eapply IHrunning in H3. instantiate (1:=cd) in H3. rewrite Heqp in H3.
    simpl in H3. constructor; auto. intro. apply neg_rel_dec_correct in Heqb.
    eapply increment_nodup'; eauto. instantiate (1:=running).
    rewrite Heqp0. simpl. auto.
    rewrite Heqp. auto.
Qed.

Lemma increment_neq : forall running c cd v,
In (c, v) running ->
c <> cd ->
In (c, v) (SF_imp.increment candidate reldec_candidate running cd).
Proof.
induction running; intros.
- inv H.
- destruct a.
  simpl in *.
  destruct (eq_dec c0 cd) eqn:?.
  + simpl in *. intuition.
    apply reldec_correct_candidate in Heqb. inv H1. subst. intuition.
  + simpl in *. intuition.
Qed.


Lemma increment_neq' : forall running cd ct  c,
In (cd, ct) (SF_imp.increment candidate reldec_candidate running c) ->
c <> cd ->
In (cd, ct) running.
Proof.
induction running; intros.
- simpl in H. intuition. congruence.
- simpl in *. destruct a.
  + destruct (eq_dec c0 c) eqn:?.
    apply rel_dec_correct in Heqb. subst.
    simpl in *. intuition. inv H1. intuition.
    simpl in *. intuition.
    right. eapply IHrunning; eauto.
Qed.

Lemma tabulate''_not_0 : forall l cd v running,
NoDup (fst (split running)) ->
In (cd, v) running ->
v <> 0 ->
~In (cd, 0)
   (SF_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *. intuition. apply H1.
  clear H1. induction running.
  + inv H0.
  + simpl in *. destruct a. destruct (split running) eqn:?. simpl in *.
    intuition.
    * inv H1. inv H0. auto.
    * inv H1. inv H. intuition. apply in_split_l in H0. simpl in *.
      rewrite Heqp in *. simpl in *. intuition.
    * inv H. inv H0. apply in_split_l in H1. rewrite Heqp in *. simpl in *.
      intuition.
    * inv H. intuition.
- simpl in *. destruct a. intro. intuition.
  destruct (rel_dec_p c cd).
  + subst.
    eapply IHl in H2; auto.
    * apply increment_nodup. auto.
    * instantiate (1:=v + 1). edestruct increment_spec. reflexivity.
      apply H. apply H3. auto.
    * intuition.  rewrite N.eq_add_0 in H3. destruct H3. congruence.
  + eapply IHl in H2; auto.
    * apply increment_nodup; auto.
    * instantiate (1:=v). edestruct increment_spec. reflexivity.
      apply H. apply increment_neq; auto.
    * auto.
  + eapply IHl in H0; auto.
Grab Existential Variables. apply 0. apply c. (*ugh*)
Qed.

Lemma tabulate''_not_0_also : forall l cd running,
NoDup (fst (split running)) ->
(forall v,
   In (cd, v) running ->
   v <> 0) ->
~In (cd, 0)
   (SF_imp.tabulate'' candidate reldec_candidate l running).
Proof.
  induction l; simpl; repeat intro.
  * apply H0 in H1. apply H1; auto.
  * destruct a.
    revert H1. apply IHl.
    apply increment_nodup; auto.
    intros.
    intro. subst v.
    case_eq (eq_dec cd c); intros.
    apply reldec_correct_candidate in H2. subst c.
    eapply increment_not_0. 2: apply H1. auto.
    apply increment_neq' in H1.
    apply H0 in H1. elim H1; auto.
    intro.
    subst c.
    assert (eq_dec cd cd = true).
    apply reldec_correct_candidate. auto.
    rewrite H2 in H3. discriminate.
    eapply IHl; eauto.
Qed.

Lemma tabulate_not_0 : forall l cd r ,
~In (cd, 0)
   (fst (SF_imp.tabulate candidate reldec_candidate r l)).
Proof.
  intros.
  unfold SF_imp.tabulate.
  destruct (SF_imp.option_split
               (map (SF_imp.next_ranking candidate reldec_candidate r) l)).
  simpl.
  intro.
  generalize (insertion_sort_permutation
                (SF_imp.tabulate' _ reldec_candidate l0) (SF_imp.cnle candidate)).
  intros.
  assert (In (cd, 0) (SF_imp.tabulate' _ reldec_candidate l0)).
  eapply Permutation_in. 2: apply H.
  apply Permutation_sym. auto.
  unfold SF_imp.tabulate' in H1.
  eapply (tabulate''_not_0_also l0 cd); eauto.
  simpl. constructor.
  simpl; intuition.
Qed.

Lemma opt_eq_dec : forall A,
(forall (a b : A), {a = b} + {a <> b}) ->
forall (a b : option A), {a = b} + {a <> b}.
Proof.
intros.
destruct a, b; auto.
specialize (X a a0). destruct X. subst. auto. right.
intro. inv H. auto.
right. intro. congruence.
right. congruence.
Qed.

Lemma opt_eq_dec_cand :
forall (a b : option candidate), {a = b} + {a <> b}.
Proof.
apply opt_eq_dec. apply rel_dec_p.
Qed.

Lemma NoDup_In_fst :
forall A B l (a :A) (b :B) c,
NoDup (fst (split l)) ->
In (a, b) l ->
In (a, c) l ->
b = c.
Proof.
induction l; intros.
- inv H0.
- simpl in *.
  destruct (split l) eqn:?.
  destruct a. intuition; try congruence.
  + simpl in *. inv H2. inv H. apply in_split_l in H0. simpl in H0.
    rewrite Heqp in *. intuition.
  + simpl in *. inv H. inv H0.
    apply in_split_l in H2. simpl in*. rewrite Heqp in *.
    intuition.
  + eapply IHl; eauto. simpl. simpl in H. inv H. auto.
Qed.

Lemma tab_inc_s : forall cd ct l running running' cr,
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
In (cd, ct + 1)
   (SF_imp.tabulate'' candidate reldec_candidate l running') ->
In (cd, cr) running ->
In (cd, (cr + 1)) running' ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *.
  assert (cr = ct).
  eapply NoDup_In_fst in H3. instantiate (1:= ct + 1) in H3.
  apply N.add_cancel_r in H3. auto.
  auto. auto. subst. auto.
- simpl in *.
  destruct a.
  + destruct (rel_dec_p cd c).
    * subst. eapply IHl.
      apply increment_nodup. auto.
      apply increment_nodup. apply H0.
      eauto.
      eapply increment_spec in H2; eauto.
      eapply increment_spec in H3; eauto.
    * eapply increment_neq in H2; eauto.
      eapply increment_neq in H3; eauto.
      eapply IHl.
      apply increment_nodup. auto.
      apply increment_nodup. apply H0.
      apply H1.
      eauto.
      eauto.
  + eapply IHl; eauto.
Qed.



Lemma tabulate''_same : forall cd l running running' cr ct,
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
In (cd, cr) running ->
In (cd, cr) running' ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running) ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running').
Proof.
induction l; intros.
- simpl in *.
  assert (cr = ct).
  eapply NoDup_In_fst. apply H.
  apply H1. apply H3. subst.
  auto.
- simpl in *.
  destruct a.
  + destruct (rel_dec_p cd c).
    * eapply IHl.
      apply increment_nodup. apply H.
      apply increment_nodup. auto.
      subst.
      eapply increment_spec in H1. apply H1.
      auto. auto.
      subst. eapply increment_spec in H2; eauto.
      eauto.
    * eapply IHl.
      apply increment_nodup. apply H.
      apply increment_nodup. auto.
      eapply increment_neq in n. apply n. eauto.
      eapply increment_neq in n.
      eauto. auto.
      eauto.
  + eapply IHl; eauto.
Qed.

Lemma tabulate''_same_notin : forall cd ct l running running',
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
~In cd (fst (split running)) ->
~In cd (fst (split running')) ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running) ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running').
Proof.
induction l; intros.
- simpl in *. intuition.
  apply in_split_l in H3. simpl in H3. intuition.
- simpl in *.
  destruct a; try solve [eapply IHl; eauto].
  destruct (rel_dec_p cd c).
  + subst. eapply increment_spec in H1; eauto.
    eapply increment_spec in H2; eauto.
    eapply (tabulate''_same _ _ _ _ _ _ _ _ _ H2).
    eauto.
  + eapply IHl. apply H.
    apply increment_nodup. auto. auto. apply increment_nodup'; eauto.
    eapply IHl in H3. eauto.
    apply increment_nodup. auto. auto. apply increment_nodup'; eauto.
    auto. Grab Existential Variables. auto.
    apply increment_nodup. auto. apply increment_nodup. auto.
Qed.

Lemma tab_inc_s_l :
forall l cd ct running,
In (cd, ct + 1) (SF_imp.tabulate'' candidate reldec_candidate l
               (SF_imp.increment candidate reldec_candidate running cd)) ->
~ In cd (fst (split running)) ->
NoDup (fst (split running)) ->
In (Some cd) l ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- inv H2.
- simpl in *. destruct a.
  destruct (rel_dec_p cd c).
  + subst. clear H2.
    simpl in *. eapply increment_spec in H0; auto.
    copy H0.
    eapply increment_spec in H0; auto.
    eapply tab_inc_s. apply increment_nodup. auto. apply increment_nodup.
    apply increment_nodup. eauto. eauto. eauto. eauto.
    apply increment_nodup. auto.
  + destruct H2. congruence.
    eapply tabulate''_same_notin.
    eauto. apply increment_nodup. auto.
    auto.
    apply increment_nodup'; auto.
    eapply IHl; eauto.
    eapply (tabulate''_same) in H.
    apply H. apply increment_nodup. apply increment_nodup.
    auto. apply increment_nodup. auto.
    apply increment_neq; auto. eapply increment_spec in H0; eauto.
    eapply increment_spec in H0; eauto.
  + intuition. congruence.
Qed.

Lemma tabulate_not_in_l :
forall l cd ct running,
NoDup (fst (split running)) ->
In (cd, ct) running ->
~In (Some cd) l ->
In (cd, ct) (SF_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl. auto.
- simpl in *.
  destruct a; intuition; try congruence.
  eapply IHl; eauto. apply increment_nodup. auto.
  apply increment_neq; auto. intuition. subst. auto.
Qed.

Lemma tabulate_nodup :
forall l running,
NoDup (fst (split running)) ->
NoDup (fst (split (SF_imp.tabulate'' candidate reldec_candidate l running))).
Proof.
induction l; intros.
- simpl.  auto.
- simpl in *.
  destruct a.
  + apply IHl. apply increment_nodup; auto.
  + apply IHl. auto.
Qed.


Lemma selected_not_in :
forall  ef l cd r l0,
~(In (Some cd ) l) ->
SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate r) ef) =
         (l, l0) ->
SF_spec.first_choices candidate (in_record r) cd ef 0.
Proof.
induction ef; intros.
- simpl in *. inv H0. constructor.
- simpl in *.
  destruct (SF_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. destruct (SF_imp.option_split
                            (map (SF_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl in *. inv H0. simpl in *.
    intuition.
    apply next_ranking_selected in Heqo.
    constructor.
    intro. eapply SF_spec.selected_candidate_unique in Heqo; eauto.
    subst; auto.
    eapply IHef; eauto.
  + destruct (SF_imp.option_split
              (map (SF_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    inv H0.
    simpl in *.
    apply SF_spec.first_choices_not_selected.
    intro. intuition. unfold SF_spec.selected_candidate in H0.
    destruct H0. apply next_ranking_eliminated in Heqo.
    unfold SF_spec.continuing_ballot in H. intuition.
    eapply IHef; eauto.
Qed.

Lemma increment_same_s :
forall c running,
NoDup (fst (split running)) ->
exists n, In (c, n + 1) (SF_imp.increment candidate _ running c).
intros.
destruct (in_dec rel_dec_p c (fst (split running))).
apply in_split in i. destruct i.
exists x. eapply increment_spec in H; eauto.
destruct H. apply H. auto.
exists 0. eapply increment_spec in n; eauto. apply 0.
Qed.


Lemma tabulate''_first_choices : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))),
In (cd, ct) (SF_imp.tabulate'' candidate _
                (fst (SF_imp.option_split
                  (map (SF_imp.next_ranking candidate reldec_candidate r)
                       ef))) running) ->
(forall cnd, ~In cnd (fst (split running)) ->
             SF_spec.first_choices candidate (in_record r) cnd es 0) ->
Forall (fun x => let (cnd, n) := (x: candidate * N)
                 in SF_spec.first_choices candidate (in_record r) cnd es (N.to_nat n)) running ->
SF_spec.first_choices candidate (in_record r) cd (es ++ ef) (N.to_nat ct).
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in *. specialize (H1 _ H). simpl in H1.
  rewrite app_nil_r.  auto.
- simpl in H.
  assert (Permutation (a :: (es ++ ef)) (es ++ a :: ef)).
  apply Permutation_middle.
  eapply first_choices_perm; eauto. clear H2.
  destruct (SF_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  +  destruct p. destruct (SF_imp.option_split
                     (map (SF_imp.next_ranking candidate reldec_candidate r)
                          ef)) eqn:?. simpl in *.
     apply next_ranking_selected in Heqo.
     destruct (rel_dec_p c cd).
     * subst.
       { destruct ct.
         - clear - H NODUP.
           assert (X := increment_same_s cd running NODUP).
           destruct X.
           exfalso. eapply tabulate''_not_0; [ | | | apply H]; eauto.
           apply increment_nodup. auto. intro. rewrite N.eq_add_0 in H1. intuition; congruence.
         - assert (exists p', N.to_nat (N.pos p) = S p').
           rewrite Znat.positive_N_nat.
           apply Pnat.Pos2Nat.is_succ. destruct H2. rewrite H2 in *.
           apply SF_spec.first_choices_selected; auto.
           destruct (in_dec rel_dec_p cd (fst (split running))).
           + rewrite <- (Nnat.Nat2N.id x). eapply IHef; eauto.
             edestruct in_split. apply i.
             eapply tab_inc_s; auto.
             apply increment_nodup. eauto.
             rewrite Heqp. simpl.
             assert (N.of_nat x+1 = N.pos p).
             assert (1 = (N.of_nat 1)). auto. rewrite H4.
             rewrite <- Nnat.Nat2N.inj_add.
             rewrite Plus.plus_comm. simpl (1 + x)%nat.
             rewrite <- H2. rewrite Nnat.N2Nat.id. auto.
             rewrite H4.
             eauto.
             apply H3. eapply increment_spec in H3; eauto.
           + destruct (in_dec opt_eq_dec_cand (Some cd) l).
             * rewrite <- (Nnat.Nat2N.id x).
               eapply IHef; eauto.
               rewrite Heqp. simpl.
               apply tab_inc_s_l; auto.
               assert (N.of_nat x+1 = N.pos p).
               assert (1 = (N.of_nat 1)). auto. rewrite H3.
               rewrite <- Nnat.Nat2N.inj_add.
               rewrite Plus.plus_comm. simpl (1 + x)%nat.
               rewrite <- H2. rewrite Nnat.N2Nat.id. auto.
               rewrite H3.
               eauto.
             * copy n. eapply increment_spec in n; eauto.
               eapply tabulate_not_in_l in n; eauto.
               assert (1 = (Npos p)). eapply NoDup_In_fst; [ | eauto | eauto ].
               apply tabulate_nodup. apply increment_nodup. auto.
               assert (1%nat = (S x)). rewrite <- H2.
               rewrite <- H4. simpl. auto.
               rewrite <- H4 in *. inv H5.
               change 0%nat with (0 + 0)%nat.
               { apply first_choices_app.
                 - apply H0. auto.
                 - eapply selected_not_in; eauto.
               }
               apply increment_nodup; auto. constructor.
       }
     * apply SF_spec.first_choices_not_selected. intro.
       apply n. eapply SF_spec.selected_candidate_unique; eauto.
       { destruct (in_dec rel_dec_p cd (fst (split running))).
         - copy i. apply in_split in H2. destruct H2.
           eapply IHef; eauto.
           rewrite Heqp. simpl. eapply tabulate''_same in H; eauto.
           eauto.
           apply increment_nodup. auto.
           apply increment_neq; auto.
         - eapply IHef; eauto.
           rewrite Heqp. simpl.
           eapply tabulate''_same_notin in H.
           eauto. apply increment_nodup. auto.
           auto. intro.
           apply in_split in H2.
           destruct H2.
           apply n0.
           eapply increment_neq' in H2.
           apply in_split_l in H2. auto.
           auto. auto.
       }
  + destruct ( SF_imp.option_split
                 (map (SF_imp.next_ranking candidate reldec_candidate r)
                      ef)) eqn:?.
    simpl in *.
    apply next_ranking_eliminated in Heqo.
    apply SF_spec.first_choices_not_selected.
    intro. unfold SF_spec.selected_candidate in H2.
    intuition.
    eapply IHef; eauto. rewrite Heqp. simpl. auto.
Qed.

Lemma tabulate'_first_choices : forall l cd ct  r,
In (cd, ct) (SF_imp.tabulate' _ _ (fst (SF_imp.option_split
                                      (map (SF_imp.next_ranking candidate reldec_candidate r)
                                           l)))) ->
SF_spec.first_choices candidate (in_record r) cd (l) (N.to_nat ct).
Proof.
intros.
rewrite <- app_nil_l at 1.
eapply tabulate''_first_choices in H. eauto.
constructor.
intros. constructor.
constructor.
Qed.

Lemma tabulate_correct : forall rec election rs election',
SF_imp.tabulate candidate _ rec election = (rs, election') ->
Forall (fun (x: (candidate * N)) => let (cd, fc) := x in
                 SF_spec.first_choices candidate (in_record rec) cd election (N.to_nat fc)) rs.
Proof.
intros.
unfold SF_imp.tabulate in H. destruct (SF_imp.option_split
             (map (SF_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
assert (PRM := insertion_sort_permutation (SF_imp.tabulate' candidate reldec_candidate l)
                                          (SF_imp.cnle candidate)).
rewrite Forall_forall. intros. destruct x. destruct ((SF_imp.insertionsort (SF_imp.cnle candidate)
         (SF_imp.tabulate' candidate reldec_candidate l),
      SF_imp.drop_none l0)) eqn:?. inv H.
inv Heqp0.
apply Permutation_sym in PRM.
eapply Permutation_in in PRM; eauto.
assert (l = fst (SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate rec) election))).
rewrite Heqp. auto.  subst.
clear H0.
apply tabulate'_first_choices in PRM. auto.
Qed.

(*Lemma leb_false :
forall n0  n,
NPeano.leb n0 n = false ->
n <= n0.
Proof.
induction n0; intros.
- inv H.
- simpl in *.  destruct n.
  omega.
  apply IHn0 in H. omega.
Qed.*)


Lemma tabulate_sorted :
forall rec election rs election',
SF_imp.tabulate _ _ rec election = (rs, election') ->
Sorted (boolCmpToProp (SF_imp.cnle candidate)) rs.
Proof.
intros.
intros.
unfold SF_imp.tabulate in H. destruct (SF_imp.option_split
             (map (SF_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
inv H. apply insertion_sort_sorted.
intros. unfold SF_imp.cnle. destruct b.
destruct a. simpl in *. rewrite N.leb_le in *.
rewrite N.leb_gt in *. apply N.lt_le_incl in H. auto.
Qed.


Lemma increment_not_eliminated :
forall vs c rec,
~(in_record rec c) ->
Forall (fun cd =>  ~(in_record rec cd)) (fst (split vs)) ->
Forall (fun cd => ~(in_record rec cd)) (fst (split (SF_imp.increment candidate _ vs c))).
Proof.
induction vs; intros.
- simpl in *. auto.
- simpl in *. rewrite Forall_forall in *.
  intros. destruct a.
  destruct (eq_dec c0 c) eqn:?.
  + simpl in *. destruct (split vs) eqn:?.
    simpl in *. intuition. subst. apply reldec_correct_candidate in Heqb.
    subst. intuition.
    specialize (H0 x). intuition.
  + simpl in *. destruct (split (SF_imp.increment candidate reldec_candidate vs c)) eqn:?.
    simpl in *. intuition.
    * subst. specialize (H0 x).
      destruct (split vs) eqn:?. simpl in *. intuition.
    * eapply IHvs in H; eauto.
      rewrite Forall_forall in H.
      eapply H; eauto.
      rewrite Heqp. auto.
      rewrite Forall_forall. intros.
      specialize (H0 x0). destruct (split vs).
      simpl in *. intuition.
Qed.


Lemma tabulate''_continuing : forall ef cd ct  running r,
In (cd, ct) (SF_imp.tabulate'' candidate _
                               (fst (SF_imp.option_split
                                      (map (SF_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running) ->
Forall (fun x => ~(in_record r x)) (fst (split running)) ->
~(in_record r cd).
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in H0.
  specialize (H0 (cd)). intuition. apply H0; auto.
  apply in_split_l in H. simpl in H. auto.
- simpl in *. destruct ( SF_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. apply next_ranking_selected in Heqo.
    destruct (SF_imp.option_split
                (map (SF_imp.next_ranking candidate reldec_candidate r)
                     ef)) eqn:?. simpl in *.
    apply SF_spec.selected_candidate_not_eliminated in Heqo.
    eapply increment_not_eliminated in Heqo; eauto.
    eapply IHef. rewrite Heqp. simpl. eauto.
    auto.
  + destruct (SF_imp.option_split
                (map (SF_imp.next_ranking candidate reldec_candidate r)
                     ef)) eqn:?.
    simpl in *.
    eapply IHef. rewrite Heqp. simpl. eauto.
    eauto.
Qed.

Lemma split_fst (A B:Type) (l:list (A*B)):
  map (@fst A B) l = fst (split l).
Proof.
  induction l; simpl; auto.
  destruct a; simpl.
  destruct (split l); simpl in *.
  f_equal; auto.
Qed.

Lemma increment_same :
  forall running cnd cnt,
    NoDup (fst (split running)) ->
    In (cnd,cnt) (SF_imp.increment candidate reldec_candidate running cnd) ->
    (exists cnt', cnt = cnt' + 1 /\ In (cnd,cnt') running) \/
    (cnt = 1 /\ ~In cnd (fst (split running))).
Proof.
  induction running; simpl; intuition.
  * inv H1. eauto.
  * revert H0. case_eq (eq_dec a0 cnd); intros.
    + simpl in H1. destruct H1.
      - inv H1.
        left. exists b. split; auto.
      - case_eq (split running); intros.
        rewrite H2 in H. simpl in H.
        inv H.
        apply reldec_correct_candidate in H0.
        subst a0.
        assert (In cnd (map (@fst _ _ ) running)).
        rewrite in_map_iff.
        exists (cnd,cnt). simpl; auto.
        rewrite split_fst in H.
        rewrite H2 in H. simpl in H.
        contradiction.
    + simpl in H1. destruct H1.
      - inv H1.
        assert (eq_dec cnd cnd = true).
        apply reldec_correct_candidate. auto.
        rewrite H0 in H1. discriminate.
      - apply IHrunning in H1.
        destruct H1.
        destruct H1 as [cnt' [??]].
        left. exists cnt'. split; simpl; auto.
        destruct H1.
        right; split; auto.
        destruct (split running); simpl in *.
        intro. intuition.
        assert (eq_dec a0 cnd = true).
        apply reldec_correct_candidate. auto.
        rewrite H0 in H3. discriminate.
        destruct (split running). simpl in *.
        inv H; auto.
Qed.

Lemma tabulate''_first_choices_complete : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))),
(forall cnd cnt,
   (cnt <> 0 /\ SF_spec.first_choices candidate (in_record r) cnd es (N.to_nat cnt)) <->
   In (cnd, cnt) running) ->
ct <> 0 ->
SF_spec.first_choices candidate (in_record r) cd (es ++ ef) (N.to_nat ct) ->
In (cd, ct) (SF_imp.tabulate'' candidate _
                               (fst (SF_imp.option_split
                                      (map (SF_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running).
Proof.
induction ef; intros.
- simpl in *.
  rewrite app_nil_r in *. apply H; auto.
- simpl in *.
  destruct (SF_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. destruct (SF_imp.option_split
                  (map (SF_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    assert (l = fst ( SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate r) ef))) by (rewrite Heqp; auto).
    subst. simpl.
    assert (Permutation (es ++ a :: ef) (a :: (es ++ ef))).
    rewrite Permutation_middle. auto.
    eapply first_choices_perm in H1; eauto.
    clear H2.
    apply next_ranking_selected in Heqo; auto.
    apply (IHef cd ct (a::es) (SF_imp.increment candidate reldec_candidate running c) r); auto.
    { apply increment_nodup; auto. }
    { intros. split.
      * intros [??]. inv H3.
        + assert ( c = cnd ) by (eapply SF_spec.selected_candidate_unique; eauto).
          subst c.
          destruct (increment_spec running cnd (fst (split running)) (N.of_nat n')); auto.
          replace cnt with (N.of_nat n' + 1).
          assert (n' = 0 \/ n' <> 0)%nat by omega.
          destruct H5.
          subst n'.
          simpl in *.
          apply H4.
          { intro.
            rewrite <- split_fst in H5.
            rewrite in_map_iff in H5.
            destruct H5 as [[p q] [??]].
            simpl in *.
            subst p.
            apply H in H9. destruct H9.
            elim H5.
            apply Nnat.N2Nat.inj. simpl.
            eapply SF_spec.sf_first_choices_unique; eauto.
          }
          apply H3.
          rewrite <- H.
          split.
          intro.
          apply H5.
          destruct n'; auto.
          inv H9.
          rewrite Nnat.Nat2N.id. auto.
          apply Nnat.N2Nat.inj.
          rewrite <- H6.
          rewrite Nnat.N2Nat.inj_add.
          rewrite Nnat.Nat2N.id.
          rewrite Plus.plus_comm. simpl. auto.
        + apply increment_neq; auto.
          rewrite <- H. split; auto.
          intro. subst c. contradiction.
      * simpl; intros.
        destruct (classic (c = cnd)).
        subst c.
        split. intro. subst cnt.
        revert H2. apply increment_not_0; auto.
        apply increment_same in H2; auto.
        destruct H2.
        destruct H2 as [cnt' [??]].
        apply H in H3. destruct H3.
        replace (N.to_nat cnt) with (S (N.to_nat cnt')).
        apply SF_spec.first_choices_selected; auto.
        rewrite H2.
        rewrite N.add_comm.
        rewrite Nnat.N2Nat.inj_add. simpl. auto.
        destruct H2. subst cnt. unfold N.to_nat. unfold BinPos.Pos.to_nat. simpl.
        apply SF_spec.first_choices_selected; auto.
        destruct (SF_spec.sf_first_choices_total candidate (in_record r) es cnd).
        destruct x; auto.
        elim H3.
        rewrite <- split_fst.
        rewrite in_map_iff.
        exists (cnd, N.of_nat (S x)). split.
        simpl; auto.
        apply H.
        split. simpl. discriminate.
        rewrite Nnat.Nat2N.id. auto.

        apply increment_neq' in H2; auto.
        rewrite <- H in H2.
        destruct H2; split; auto.
        apply SF_spec.first_choices_not_selected; auto.
        intro. apply H3.
        eapply SF_spec.selected_candidate_unique; eauto.
    }

  + destruct (SF_imp.option_split
                  (map (SF_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl.
    assert (l = fst ( SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate r) ef))) by (rewrite Heqp; auto).
    subst. simpl.
    assert (Permutation (es ++ a :: ef) (a :: (es ++ ef))).
    rewrite Permutation_middle. auto.
    eapply first_choices_perm in H1. 2: apply H2.
    clear H2.
    inv H1.
    * apply next_ranking_eliminated in Heqo.
      destruct H5. elim H1; auto.
    * apply (IHef cd ct (a::es) running r); auto.
      { intros; split.
        intros [??].
        apply H. split; auto.
        inv H2; auto.
        apply next_ranking_eliminated in Heqo.
        destruct H8. contradiction.
        intros.
        apply H in H1.
        destruct H1; split; auto.
        apply SF_spec.first_choices_not_selected; auto.
        apply next_ranking_eliminated in Heqo.
        intro. destruct H3. contradiction.
      }
      { simpl. apply SF_spec.first_choices_not_selected; auto. }
Qed.


Lemma tabulate'_first_choices_complete : forall l cd ct r,
ct <> 0 ->
SF_spec.first_choices _ (in_record r) cd l (N.to_nat ct) ->
In (cd, ct) (SF_imp.tabulate' _ _
   (fst (SF_imp.option_split (map (SF_imp.next_ranking _ _ r) l)))).
Proof.
intros.
unfold SF_imp.tabulate'.
rewrite <- (app_nil_l l) in H0.
eapply tabulate''_first_choices_complete; eauto; try solve [constructor].
split; intros.
destruct H1. inv H2. assert (cnt = 0). rewrite <- Nnat.Nat2N.inj_iff in H3.
rewrite Nnat.N2Nat.id in H3. auto. subst. congruence.
inv H1.
Qed.

Lemma tabulate_first_choices_complete : forall l cd ct r,
ct <> 0 ->
SF_spec.first_choices _ (in_record r) cd l (N.to_nat ct) ->
In (cd, ct) (fst (SF_imp.tabulate _ _ r l)).
  intros.
  unfold SF_imp.tabulate.
  destruct (SF_imp.option_split
               (map (SF_imp.next_ranking candidate reldec_candidate r) l)) eqn:?.
  eapply Permutation_in.
  apply insertion_sort_permutation.
  assert (l0 = fst (SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate r) l))).
  rewrite Heqp. auto.
  subst.
  eapply tabulate'_first_choices_complete. auto.
  auto.
Qed.


Lemma cnlt_trans : Relations_1.Transitive (boolCmpToProp (SF_imp.cnle candidate)).
Proof.
intro. intros.
destruct x, y, z.
unfold boolCmpToProp in *. simpl in *.
destruct (n <=? n0) eqn:?, (n0 <=? n1) eqn:?, (n <=? n1) eqn:?; auto.
rewrite N.leb_le in *.
rewrite N.leb_gt in *.
eapply N.le_trans in Heqb0; eauto.
rewrite N.le_ngt in *. auto.
Qed.



Lemma tabulate''_participates : forall x election n rec,
In (x, n) (SF_imp.tabulate'' _ _ (fst (SF_imp.option_split
                                        (map (SF_imp.next_ranking candidate reldec_candidate rec)
                                             election))) nil) ->
SF_spec.participates candidate x election.
Proof.
induction election; intros.
- simpl in *. inv H.
- simpl in *.
  destruct (SF_imp.next_ranking candidate reldec_candidate rec a) eqn:?.
  + destruct p.
    destruct ( SF_imp.option_split
                 (map
                    (SF_imp.next_ranking candidate reldec_candidate rec)
                    election)) eqn:?.
    simpl in *.
    destruct (rel_dec_p c x).
    * subst.
      apply next_ranking_selected in Heqo.
      eapply selected_participates. eauto.
      simpl. auto.
    * apply participates_cons. right.
      eapply IHelection. instantiate (2 := n).
      assert (fst (SF_imp.option_split
                     (map (SF_imp.next_ranking candidate reldec_candidate rec) election)) = l).
      rewrite Heqp; auto. subst.
      eapply tabulate''_same_notin. instantiate (1 := [(c,1)]).
      repeat constructor. auto. constructor.
      intro. simpl in H0. intuition. auto.
      apply H.
  + destruct (SF_imp.option_split
                     (map
                        (SF_imp.next_ranking candidate reldec_candidate rec)
                        election)) eqn:?.
    simpl in H. assert (l = (fst (SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate rec) election)))).
    rewrite Heqp. auto.
    subst.
    apply participates_cons. right.
    eapply IHelection. eauto.
Qed.

Lemma tabulate_participates : forall x n election rec,
In (x, n) (fst (SF_imp.tabulate _ _ rec election)) ->
SF_spec.participates candidate x election.
intros. unfold SF_imp.tabulate in *.
destruct (SF_imp.option_split
                  (map (SF_imp.next_ranking candidate reldec_candidate rec)
                     election)) eqn:?.
simpl in *.
assert (l = fst (SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate rec) election))).
rewrite Heqp. auto.
subst. clear Heqp.
eapply Permutation_in in H.
eapply tabulate''_participates. apply H.
symmetry. apply insertion_sort_permutation.
Qed.

Lemma get_bottom_votes_is_loser :
forall election rec losers rs election'
 (ELIMO : forall c, SF_spec.participates _ c election ->
                    SF_spec.first_choices _ (in_record rec) c election 0 ->
                    (in_record rec c)),
  SF_imp.tabulate _ _ rec election = (rs, election') ->
  SF_imp.get_bottom_votes  _ rs = losers ->
  Forall (SF_spec.is_loser candidate (in_record rec) election) losers.
Proof.
intros.
destruct (SF_imp.tabulate _ _ rec election) eqn:?. inv H.
destruct rs.
- simpl in *. auto.
- simpl in *. destruct p. rewrite N.eqb_refl.
  simpl. rewrite Forall_forall.
  intros. simpl in *.
  destruct H.
  + subst. assert (SRTD := tabulate_sorted _ _ _ _ Heqp).
    apply Sorted_StronglySorted in SRTD.
    *    assert (CRCT := tabulate_correct _ _ _ _ Heqp).
         rewrite Forall_forall in CRCT.
         specialize (CRCT (x, n)). intuition.
         simpl in *. intuition. clear H0.
         inv SRTD.
         unfold SF_spec.is_loser.
         { repeat split.
           - unfold SF_imp.tabulate in Heqp. unfold
                                           SF_imp.tabulate' in Heqp.
             destruct (SF_imp.option_split
                         (map (SF_imp.next_ranking candidate reldec_candidate rec)
                              election)) eqn:?.
             inv Heqp.
             assert (PRM := insertion_sort_permutation ((SF_imp.tabulate'' candidate reldec_candidate l []))
                                                       (SF_imp.cnle candidate)).
             eapply Permutation_sym in PRM.
             eapply Permutation_in in PRM.
             instantiate (1 := (x, n)) in PRM.
             eapply tabulate''_continuing. instantiate (1 := nil). instantiate (1 := election).
             erewrite Heqp0. simpl. eauto.
             constructor.
             rewrite H0. constructor. auto.
           - eapply tabulate_participates; eauto. instantiate (1:=rec). rewrite Heqp.
             simpl. left. reflexivity.
           - intros.
             assert (N.to_nat n = n0); [ | subst n0 ].
             { eapply SF_spec.sf_first_choices_unique in H0; [ | apply H1]. auto. }
             rewrite Forall_forall in H3.
             destruct H.
             unfold SF_spec.participates in H5.
             destruct H5.
             destruct H5. destruct H6. destruct H6.
             destruct (NPeano.Nat.eq_dec (N.to_nat n) m).
             + omega.
             + cut (In (c', (N.of_nat m)) rs).
               * intros.
                 apply H3 in H8. unfold boolCmpToProp in H8.
                 simpl in *. destruct (n <=? N.of_nat m) eqn:?; try contradiction.
                 apply N.leb_le in Heqb.
                 edestruct (rel_dec_p c' x).
                 subst.
                 eapply SF_spec.sf_first_choices_unique in H4; [ | apply H1]. intuition.
                 rewrite <- (Nnat.Nat2N.id m) in H4.
                 apply tabulate_first_choices_complete in H4.
                 rewrite Heqp in H4. simpl in H4.
                 destruct H4. congruence.
                 destruct (n <=? N.of_nat m) eqn:?; auto.
                 rewrite N.leb_le in Heqb0.
                 rewrite N.lt_eq_cases in Heqb0.
                 destruct Heqb0. rewrite Znat.N2Z.inj_lt in H9.
                 rewrite (Znat.Nat2Z.inj_le (N.to_nat n) m). rewrite Znat.N_nat_Z in *.
                 rewrite Znat.nat_N_Z in *. rewrite BinInt.Z.lt_eq_cases. auto.
                 subst. rewrite (Nnat.Nat2N.id) in *. intuition.
                 rewrite N.leb_gt in Heqb0. clear - Heqb.
                 rewrite Znat.N2Z.inj_le in Heqb.
                 rewrite Znat.nat_N_Z in *.
                 rewrite Znat.Nat2Z.inj_le.
                 rewrite Znat.N_nat_Z. auto.
                 intro. rewrite H9 in *.
                 eapply ELIMO in H4. auto.
                 unfold SF_spec.participates.
                 exists x0.
                 eauto.
               * generalize (tabulate_first_choices_complete election c' (N.of_nat m) rec).
                 rewrite Heqp. simpl.
                 rewrite Nnat.Nat2N.id.
                 intros. destruct H8; auto.
                 intro.
                 elim H.
                 apply ELIMO; auto.
                 red. eauto.
                 destruct m; auto. discriminate.
                 auto.
                 inv H8.
                 elim n0.
                 rewrite Nnat.Nat2N.id. auto.
         }
    *  apply cnlt_trans.
  + assert (In (x, n) (filter
              (fun x0 : candidate * N =>
               let (_, v') := x0 in n =? v') rs)).
    rewrite filter_In. split.
    * rewrite in_map_iff in H. destruct H. destruct x0. simpl in H. intuition.
      subst. rewrite filter_In in H1. intuition.
      apply N.eqb_eq in H0. subst.
      auto.
    * symmetry. symmetry. apply N.eqb_refl .
    * clear H.
      rewrite filter_In in H0. destruct H0.
      assert (SRTD := tabulate_sorted _ _ _ _ Heqp).
      apply Sorted_StronglySorted in SRTD.
      assert (CRCT := tabulate_correct _ _ _ _ Heqp).
      rewrite Forall_forall in CRCT.
      inv SRTD.
      simpl in *. specialize (CRCT ((x, n))).
      intuition. clear H1.
      unfold SF_spec.is_loser.
      split.
      split.
      rewrite Forall_forall in *.
      { apply nonzero_first_choices_selected in H5.
        destruct H5 as [b [??]].
        apply SF_spec.selected_candidate_not_eliminated in H2. auto.
        assert ( n = 0 \/ n > 0 ). zify. omega.
        destruct H1. subst n.
        elim (tabulate_not_0 election c rec).
        rewrite Heqp. simpl. auto.
        zify. omega.
      }
      { apply tabulate_participates with n rec.
        rewrite Heqp. simpl. auto.
      }
      intros ? ? ? [??] ? ?.
      eapply SF_spec.sf_first_choices_unique in H5; eauto. subst.
      rewrite Forall_forall in H4.
      specialize (H4 (c', (N.of_nat m))).
      destruct (rel_dec_p c c').
      subst.
      assert (CRCT := tabulate_correct _ _ _ _ Heqp).
      rewrite Forall_forall in CRCT.
      specialize (CRCT (c', n)). simpl in CRCT. intuition.
      clear H8.
      eapply SF_spec.sf_first_choices_unique in H7; eauto.
      subst.
      auto.
      assert (In (c', N.of_nat m) rs).
      rewrite <- Nnat.Nat2N.id in H7.
      apply tabulate_first_choices_complete in H7.
      rewrite Heqp in *. simpl in H7. destruct H7.
      inv H5. intuition.
      auto.
      intro.
      rewrite H5 in *. clear H5.
      apply ELIMO in H7; auto.
      intuition.
      unfold boolCmpToProp in H8. simpl in H8.
      destruct (n <=? N.of_nat m) eqn:?; intuition.
      apply N.leb_le in Heqb. zify. omega.
      apply cnlt_trans.
Qed.


Lemma last_item_in :
forall l w n,
SF_imp.last_item candidate l = Some (w,n) ->
In (w,n) l.
Proof.
induction l; intros.
simpl in *. congruence.
simpl in *. destruct l. inv H. auto.
right. auto.
Qed.


Lemma N_nat_le_inj :
forall x1 n,
x1 <= n <-> (N.to_nat x1 <= N.to_nat n)%nat.
Proof.
intros. rewrite Znat.N2Z.inj_le. rewrite Znat.Nat2Z.inj_le.
repeat rewrite Znat.N_nat_Z. intuition.
Qed.

Lemma tabulate_total_selected : forall r election election' vs,
SF_imp.tabulate _ _ r election = (vs, election') ->
SF_spec.total_selected candidate (in_record r) election (length election').
Proof.
  intros. unfold SF_imp.tabulate in *.
  destruct (SF_imp.option_split
             (map (SF_imp.next_ranking candidate reldec_candidate r) election)) eqn:?.
  simpl in *. inv H.
  generalize dependent l0.
  revert r  election l.
  induction election; intros.
  -   simpl in *. inv Heqp. constructor.
  - simpl in *. destruct (SF_imp.next_ranking candidate reldec_candidate r a) eqn:?.
    + repeat dlp.
      inv Heqp. simpl in *. apply SF_spec.total_continuing.
      apply next_ranking_selected in Heqo.
      unfold SF_spec.selected_candidate in *. intuition.
      eapply IHelection. eauto.
    + dlp. inv Heqp. simpl in *.
      apply SF_spec.total_exhausted.
      eapply next_ranking_eliminated; eauto.
      eapply IHelection; eauto.
Qed.


Lemma last_item_cons :
forall h t l,
SF_imp.last_item candidate (h :: t) = Some l ->
(t = nil /\ h = l) \/ SF_imp.last_item candidate t = Some l.
induction t; intros.
- simpl in *. inv H. auto.
- simpl in *. right.
  auto.
Qed.


Lemma ss_last :
forall l c n,
StronglySorted (boolCmpToProp (SF_imp.cnle candidate)) l ->
SF_imp.last_item candidate l = Some (c, n) ->
Forall (fun (r : candidate * N) => let (_, y) := r in y <= n) l.
Proof.
induction l; intros.
- simpl in *. congruence.
- apply last_item_cons in H0.
  rewrite Forall_forall; intros.
  intuition. subst.
  inv H1. apply N.le_refl.
  inv H0.
  destruct H1.
  + subst. destruct x.  inv H.
    rewrite Forall_forall in *.
    specialize (H4 (c, n)).
    apply last_item_in in H2. intuition.
    unfold boolCmpToProp in H.
    simpl in *.
    destruct (n0 <=? n) eqn:?; try contradiction.
    rewrite N.leb_le in Heqb. auto.
  + eapply IHl in H2; eauto.
    rewrite Forall_forall in H2.
    apply H2.  auto. inv H. auto.
Qed.

Lemma lt_of_nat :
forall n nn,
N.of_nat n < nn <->
(n < N.to_nat nn)%nat.
Proof.
intros. repeat rewrite Znat.N2Z.inj_lt.
rewrite Znat.nat_N_Z.
rewrite Znat.Nat2Z.inj_lt. rewrite Znat.N_nat_Z.
split; auto.
Qed.

Lemma gt_of_nat :
forall n nn,
N.of_nat n > nn <->
(n > N.to_nat nn)%nat.
Proof.
intros. repeat rewrite Znat.N2Z.inj_gt.
rewrite Znat.nat_N_Z.
rewrite Znat.Nat2Z.inj_gt. rewrite Znat.N_nat_Z.
split; auto.
Qed.

Lemma gt_of_nat2 :
forall n nn,
 n > N.of_nat nn <->
(N.to_nat n >  nn)%nat.
Proof.
intros. repeat rewrite Znat.N2Z.inj_gt.
rewrite Znat.nat_N_Z.
rewrite Znat.Nat2Z.inj_gt. rewrite Znat.N_nat_Z.
split; auto.
Qed.

Lemma NNatex :
forall x0,
exists nx0, N.to_nat nx0 = x0.
intros. induction x0. exists 0. auto.
destruct IHx0. exists (N.succ x).
rewrite Nnat.N2Nat.inj_succ. auto.
Qed.


Lemma run_election'_correct :
  forall fuel election winner rec' rec tbreak res
         (TB : forall c x, tbreak c = Some x -> In x c)
         (N0 : forall c, SF_spec.participates _ c election ->
                           SF_spec.first_choices _ (in_record rec) c election 0 ->
                           in_record rec c),
    SF_imp.run_election' candidate _ tbreak election rec fuel = (Some winner, rec', res) ->
    SF_spec.winner candidate election (in_record rec) winner.
induction fuel; intros.
- simpl in *. congruence.
- simpl in *. destruct (SF_imp.tabulate candidate reldec_candidate rec election) eqn:?;
                       simpl in *; try congruence.
  destruct (SF_imp.last_item candidate l) eqn:?; try congruence.
  destruct p.
  destruct ( SF_imp.gtb_N (n * 2) (N.of_nat (length e))) eqn:?.
  + inv H.
    apply SF_spec.winner_now. unfold SF_spec.majority.
    intros. assert (winner_votes = (N.to_nat n)).
    { apply tabulate_correct in Heqp.
      rewrite Forall_forall in Heqp. specialize (Heqp (winner, n)).
      apply last_item_in in Heqo. intuition.
      eapply SF_spec.sf_first_choices_unique in H1; eauto. }
    subst.
    assert (total_votes = (length e)).
    { apply tabulate_total_selected in Heqp.
      eapply SF_spec.total_selected_unique; eauto. }
    subst.
    rewrite SF_imp.gtb_nat_gt in Heqb. rewrite gt_of_nat2 in Heqb.
    rewrite Nnat.N2Nat.inj_mul in Heqb. auto.
    apply _.
  + unfold SF_imp.find_eliminated_noopt in *.
    destruct (tbreak (SF_imp.get_bottom_votes candidate l)) eqn:?.
    * rename c0 into loser.
      rename Heqo0 into TBREAK.
      copy Heqp. rename H0 into ISLOSER.
      eapply get_bottom_votes_is_loser in ISLOSER; eauto.
      rewrite Forall_forall in ISLOSER.
      eapply TB in TBREAK.
      apply ISLOSER in TBREAK.
      { eapply SF_spec.winner_elimination.
        - unfold SF_spec.no_majority.
          intro. destruct H0.
          assert (~ SF_spec.majority _ (in_record rec) election c).
          { intro.
            unfold SF_spec.majority in *.
            specialize (H1 (length e) (N.to_nat n)).
            copy Heqp.
            apply tabulate_total_selected in H2. intuition.
            apply tabulate_correct in Heqp.
            rewrite Forall_forall in Heqp.
            specialize (Heqp (c, n)). simpl in *.
            apply last_item_in in Heqo. intuition.
            change 2%nat with (N.to_nat 2) in H4.
            rewrite <- Nnat.N2Nat.inj_mul in H4.
            rewrite <- gt_of_nat2 in H4.
            rewrite <- SF_imp.gtb_nat_gt in H4. congruence.
            apply _.
          }
          copy Heqp.
          apply tabulate_sorted in Heqp.
          clear - Heqp Heqo H0 H1 H2 N0.
          destruct (majority_not_0 _ _ _ _ H0). intuition.
          rename H4 into X0. rename H3 into FCX.
          apply Sorted_StronglySorted in Heqp; [ |  apply cnlt_trans].
          eapply ss_last in Heqp; eauto.
          rewrite Forall_forall in *.
          apply H1. clear H1. intro; intros.
          assert (winner_votes = (N.to_nat n)).
          { apply last_item_in in Heqo.
            apply tabulate_correct in H2.
            rewrite Forall_forall in H2. eapply H2 in Heqo; clear H2.
            eapply SF_spec.sf_first_choices_unique; eauto. }
          subst.
          unfold SF_spec.majority in H0.
          copy FCX.
          destruct (NNatex x0).
          rewrite <- H4 in H3.
          apply tabulate_first_choices_complete in H3; auto.
          rewrite H2 in *. simpl in *.
          specialize (Heqp (x, x1)).
          intuition.
          eapply H0 in FCX; eauto. subst. rewrite  N_nat_le_inj in H5. omega.
          subst. intro. subst. intuition.
        - eauto.
        - rewrite update_eliminated_in_rec_eq_noc.
          destruct (SF_imp.run_election' candidate reldec_candidate tbreak election
                                         ([loser] :: rec) fuel) eqn:REQN. destruct p.
          eapply IHfuel.
          + eauto.
          + intros. edestruct (rel_dec_p c0 loser).
            * subst. unfold in_record. exists [loser].
              intuition.
            * apply N0 in H0. unfold in_record in *.
              destruct H0.
              exists x. intuition.
              eapply first_choices_rec_0; eauto.
          + inv H. rewrite REQN.  auto.
      }
    * congruence.
Qed.

Lemma no_dup_map_allc :  forall allc,
NoDup allc ->
NoDup (fst (split (map (fun x : candidate => (x, 0)) allc))).
Proof.
induction allc; intros.
- simpl. auto.
- simpl. inv H.
  destruct ( split (map (fun x : candidate => (x, 0)) allc) ) eqn:?.
  assert (l = fst (split (map (fun x : candidate => (x, 0)) allc))).
  rewrite Heqp. auto. subst.
  simpl in *. constructor; auto. intuition.   clear - H2 H reldec_correct_candidate.
  apply H2. apply in_split in H. intuition_nosplit.
  apply in_map_iff in H. destruct H. intuition. inv H0. auto.
Qed.

Lemma nodup_not_in_filter :
forall allc c l,
NoDup allc ->
~ In c
         (map (@fst _ _)
            (filter
               (fun x : candidate * N =>
                let (_, ct) := x in  ct =? 0)
               (SF_imp.tabulate'' candidate reldec_candidate l
                  (SF_imp.increment candidate reldec_candidate
                     (map (fun x : candidate => (x, 0)) allc) c)))).
Proof.
intros. intro.
apply in_map_iff in H0. destruct H0. destruct H0. destruct x. simpl in *. subst.
apply filter_In in H1. destruct H1. rewrite N.eqb_eq in H1.
subst. edestruct increment_same_s. Focus 2.
 eapply tabulate''_not_0. Focus 2. eauto. apply increment_nodup.
instantiate (1:=map (fun x : candidate => (x, 0)) allc). apply no_dup_map_allc; auto.
rewrite N.add_1_r. apply N.succ_0_discr.
eauto. apply no_dup_map_allc. auto.
Qed.

Lemma tabulate_0_running :
forall (c: candidate) l running
(NODUP: NoDup (fst (split (running)))),
In (c, 0) (SF_imp.tabulate'' _ _ l running) ->
In (c, 0) running.
Proof.
induction l.
- intros. simpl in *. auto.
- intros. simpl in *. destruct a.
  destruct (rel_dec_p c c0).
  + subst. exfalso.
    edestruct (increment_same_s c0).
    eauto.
    eapply tabulate''_not_0.
    * apply increment_nodup. eauto.
    * apply H0.
    * rewrite N.add_1_r. apply N.succ_0_discr.
    * eauto.
  + apply IHl in H.
    eapply increment_neq' in H; auto.
    apply increment_nodup. auto.
  + apply IHl in H; auto.
Qed.

Lemma find_0s_correct :
forall allc election c
(PART: forall c, SF_spec.participates _ c election -> In c allc),
NoDup allc ->
In c (SF_imp.find_0s candidate reldec_candidate allc election) ->
SF_spec.first_choices _ (in_record nil) c election 0.
Proof.
intros.
induction election; intros.
- constructor.
- unfold SF_imp.find_0s in *. simpl in *.
  destruct (SF_imp.next_ranking candidate reldec_candidate [] a) eqn:?.
  + destruct p. destruct (SF_imp.option_split
                            (map (SF_imp.next_ranking candidate reldec_candidate [])
                                 election)) eqn:?.
    simpl in *. destruct (rel_dec_p c0 c).
    * subst.
      eapply nodup_not_in_filter in H. exfalso. apply H. apply H0.
    * apply SF_spec.first_choices_not_selected.
      intro. apply next_ranking_selected in Heqo.
      eapply SF_spec.selected_candidate_unique in Heqo; eauto.
      apply IHelection; eauto. intros. apply PART.
      apply participates_cons. auto.
      apply in_map_iff.
      apply in_map_iff in H0. intuition_nosplit.
      exists x. destruct x. simpl in H0. subst. intuition.
      apply filter_In in H1. apply filter_In. intuition.
      { destruct (classic (In (c, n0)
                            (SF_imp.tabulate'' candidate reldec_candidate l
                                               (map (fun x : candidate => (x, 0)) allc)))).
        - eapply tabulate''_same; [ | | | | exact H0]. apply increment_nodup.
          + apply no_dup_map_allc. auto.
          + apply no_dup_map_allc. auto.
          + apply increment_neq; eauto.
            specialize (PART c). apply in_map_iff. exists c. split.
            * reflexivity.
            * rewrite N.eqb_eq in H2. subst.
              apply tabulate_0_running in H1. apply in_map_iff in H1.
              destruct H1. destruct H1. inv H1. auto. apply no_dup_map_allc. auto.
          + rewrite N.eqb_eq in H2. subst.
            eapply tabulate_0_running. apply no_dup_map_allc; auto.
            eauto.
        - eapply tabulate''_same in H0.
          + exfalso. apply H1. apply H0.
          + apply increment_nodup; auto.
            apply no_dup_map_allc; auto.
          + apply no_dup_map_allc; auto.
          + eapply increment_neq; auto.
            apply in_map_iff. exists c.
            intuition. apply N.eqb_eq in H2. subst.
            apply tabulate_0_running in H0. eapply increment_neq' in H0; auto.
            apply in_map_iff in H0; intuition_nosplit; auto.
            apply increment_nodup. apply no_dup_map_allc. auto.
          + apply in_map_iff. exists c. intuition. apply N.eqb_eq in H2. subst.
            apply tabulate_0_running in H0. eapply increment_neq' in H0; auto.
            apply in_map_iff in H0; intuition_nosplit; auto.
            apply increment_nodup. apply no_dup_map_allc. auto.
      }
  + destruct (SF_imp.option_split
                    (map (SF_imp.next_ranking candidate reldec_candidate [])
                       election)) eqn:?.
    simpl in *.
    apply IHelection in H0; auto.
    * constructor. intro. unfold SF_spec.selected_candidate in H1.
      intuition_nosplit. apply next_ranking_eliminated in Heqo.
      unfold SF_spec.continuing_ballot in *. intuition.
      auto.
    * intros. apply PART. apply participates_cons; auto.
Qed.


Lemma selected_not_in' :
forall  ef l cd r l0,
SF_imp.option_split
           (map (SF_imp.next_ranking candidate reldec_candidate r) ef) =
         (l, l0) ->
SF_spec.first_choices candidate (in_record r) cd ef 0 ->
~(In (Some cd ) l).
Proof.
induction ef; intros.
- simpl in *. inv H0. inv H.
  simpl. auto.
- simpl in *.
  destruct (SF_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. destruct (SF_imp.option_split
                            (map (SF_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl in *. inv H.
    inv H0. simpl in *.
    intuition.
    inv H0.
    apply next_ranking_selected in Heqo.
    contradiction.
    subst; auto.
    eapply IHef; eauto.
  + destruct (SF_imp.option_split
              (map (SF_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    inv H.
    inv H0.
    simpl in *.
    intuition.
    discriminate.
    eapply IHef; eauto.
Qed.

Lemma find_0s_complete :
  forall election allc c
    (PART: forall c, SF_spec.participates _ c election -> In c allc)
    (NODUP:NoDup allc),
    SF_spec.first_choices candidate (in_record []) c election 0 ->
    True ->
    In c allc ->
    In c (SF_imp.find_0s candidate reldec_candidate allc election).
Proof.
  induction election; simpl; intros.
  inv H.
  { unfold SF_imp.find_0s in *; simpl.
    rewrite in_map_iff.
    exists (c,0).
    split; simpl; auto.
    rewrite filter_In. split. 2: rewrite N.eqb_eq; auto.
    apply in_map_iff. exists c. split; auto.
  }
  inv H.
  unfold SF_imp.find_0s in *.
  simpl in *.
  destruct (SF_imp.next_ranking candidate reldec_candidate [] a) eqn:?.
  + simpl.
    destruct p. destruct (SF_imp.option_split
                            (map (SF_imp.next_ranking candidate reldec_candidate [])
                                 election)) eqn:?.
    destruct (rel_dec_p c0 c).
    apply next_ranking_selected in Heqo.
    subst c0. contradiction.
    apply in_map_iff. exists (c, 0). split; simpl; auto.
    apply filter_In. split. 2: rewrite N.eqb_eq; auto.
    apply tabulate_not_in_l.
    apply increment_nodup.
    rewrite <- split_fst.
    rewrite map_map. simpl.
    rewrite map_id. auto.
    apply increment_neq; auto.
    apply in_map_iff.
    exists c. split; auto.
    intro.
    eapply selected_not_in'; eauto.

  + simpl in *.
    destruct (SF_imp.option_split
                    (map (SF_imp.next_ranking candidate reldec_candidate [])
                       election)) eqn:?.
    simpl.
    apply IHelection; auto.
    intros. apply PART. apply participates_cons; auto.
Qed.


Lemma find_0s_nodup :
  forall allc e,
    NoDup allc ->
    NoDup (SF_imp.find_0s candidate reldec_candidate allc e).
Proof.
  intros.
  unfold SF_imp.find_0s.
  case_eq (SF_imp.option_split
            (map (SF_imp.next_ranking candidate reldec_candidate []) e)).
  intros a b Hab.
  rewrite split_fst.
  assert (NoDup (fst (split (map (fun x : candidate => (x, 0)) allc)))).
  { replace (fst (split (map (fun x : candidate => (x, 0)) allc))) with allc; auto.
    clear. induction allc; simpl; auto.
    destruct (split (map (fun x => (x,0)) allc)); simpl in *.
    f_equal; auto.
  }
  generalize (tabulate_nodup a (map (fun x => (x,0)) allc) H0).
  generalize (SF_imp.tabulate'' candidate reldec_candidate a
              (map (fun x : candidate => (x, 0)) allc)).
  generalize (fun x : candidate * N => let (_, ct) := x in ct =? 0).
  intro f. induction l; simpl; intros; auto.
  destruct a0; simpl in *.
  case_eq (split l); intros.
  rewrite H2 in H1.
  rewrite H2 in IHl.
  simpl in *.
  inv H1.
  case_eq (f (c,n)); intros.
  simpl.
  case_eq (split (filter f l)); simpl; intros.
  constructor; auto.
  { intro. apply H5.
    clear -H3 H2 H4.
    revert l0 l1 l2 l3 H2 H3 H4.
    induction l; simpl; intros; auto.
    inv H2. inv H3. auto.
    destruct a; simpl in *.
    case_eq (split l); intros.
    rewrite H in H2.
    inv H2.
    case_eq (split (filter f l)); intros.
    generalize (IHl l4 l5 l0 l1 H H0); intros.
    destruct (f (c0,n)). simpl in *.
    rewrite H0 in H3.
    inv H3.
    simpl in H4; intuition.
    rewrite H3 in H0.
    inv H0.
    simpl; intuition.
  }
  rewrite H3 in IHl.
  simpl in IHl.
  apply IHl; auto.
  apply IHl; auto.
Qed.

Lemma find_0s_subset :
  forall allc l e,
    NoDup allc ->
    In l (SF_imp.find_0s candidate reldec_candidate allc e) ->
    In l allc.
Proof.
  intros.
  unfold SF_imp.find_0s in H0.
  cut (In (l,0) (map (fun x => (x,0)) allc)).
  { clear. induction allc; simpl; intuition.
    inv H0. auto.
  }
  destruct (SF_imp.option_split
                (map (SF_imp.next_ranking candidate reldec_candidate []) e)).
  eapply tabulate_0_running.
  { replace (fst (split (map (fun x : candidate => (x, 0)) allc))) with allc; auto.
    clear.
    rewrite <- split_fst.
    rewrite map_map.
    simpl.
    symmetry. apply map_id.
  }
  rewrite in_map_iff in H0.
  destruct H0 as [x [??]].
  destruct x. simpl in *.
  subst c.
  rewrite filter_In in H1. destruct H1.
  rewrite N.eqb_eq in H1. subst n.
  apply H0.
Qed.

Lemma count_votes_nonzero :
  forall P e n,
    (n > 0)%nat->
    Ranked_properties.count_votes candidate P e n ->
    exists b, In b e /\ P b.
Proof.
  induction e; intros.
  * inv H0. omega.
  * inv H0.
    exists a. split; simpl; auto.
    destruct (IHe n) as [b [??]]; auto.
    exists b; split; simpl; auto.
Qed.

Lemma count_votes_find_0s :
  forall allc election
  (NODUP : NoDup allc)
  (PART : forall c, SF_spec.participates _ c election -> In c allc) ,
   Ranked_properties.count_votes candidate
     (fun b : list (list candidate) =>
      exists c : candidate,
        SF_spec.selected_candidate candidate (in_record []) b c /\
        In c (SF_imp.find_0s candidate reldec_candidate allc election))
     election 0.
Proof.
  intros.
  destruct (count_votes_total _ (fun b : list (list candidate) =>
      exists c : candidate,
        SF_spec.selected_candidate candidate (in_record []) b c /\
        In c (SF_imp.find_0s candidate reldec_candidate allc election))
     election) as [n ?].
  destruct n; auto.
  elimtype False.
  assert (exists b, In b election /\
      exists c : candidate,
        SF_spec.selected_candidate candidate (in_record []) b c /\
        In c (SF_imp.find_0s candidate reldec_candidate allc election)).
  { apply count_votes_nonzero in H. auto. omega. }
  destruct H0 as [b [? [c [??]]]].
  assert (SF_spec.first_choices candidate (in_record []) c election 0).
  apply (find_0s_correct allc election c); auto.
  clear -H1 H0 H3.
  induction election.
  * elim H0.
  * apply first_choices_0_cons in H3. destruct H3.
    hnf in H0. destruct H0; auto.
    subst a.
    inv H.
    contradiction.
Qed.

Lemma winner_viable :
  forall elim election c,
    SF_spec.winner candidate election elim c ->
    SF_spec.viable_candidate candidate elim election c.
Proof.
  intros. induction H.
  destruct (majority_not_0 _ eliminated election winning_candidate) as [v [??]]; auto.
  destruct (nonzero_first_choices_selected _ eliminated winning_candidate election v) as [b [??]]; auto.
  omega.
  split.
  eapply SF_spec.selected_candidate_not_eliminated; eauto.
  eapply selected_participates; eauto.
  destruct IHwinner; split; auto.
  intro. apply H2.
  hnf. auto.
Qed.

Theorem run_election_correct : forall election winner tb rec allc res
  (TB : forall c x, tb c = Some x -> In x c)
  (PART : forall c, SF_spec.participates _ c election -> In c allc)
  (NODUP : NoDup allc),
    SF_imp.run_election candidate _ tb election allc = (Some winner, rec, res) ->
    SF_spec.winner _ election (in_record []) winner.
Proof.
intros. unfold SF_imp.run_election in H.
apply run_election'_correct in H; auto.
- rewrite -> sf_spec_optimization with
     (SF_imp.find_0s _ reldec_candidate allc election) 0%nat; auto. apply H.
  + apply count_votes_find_0s; auto.
  + exists winner.
    apply winner_viable in H.
    destruct H; split; auto.
    intro.
    apply H.
    hnf. eexists.
    split. simpl; auto. auto.
    split; auto.
    intros [q [??]]. elim H1.
  + intros. destruct count; auto with arith.
    elim H0. clear H0.
    apply find_0s_complete; auto.
    intros. apply PART; auto.
    destruct H1; auto.
  + unfold in_record. firstorder. subst x0. auto.
- intros.
  eexists. simpl. split. left. reflexivity.
  apply find_0s_complete; auto.
  destruct (SF_spec.sf_first_choices_total _ (in_record []) election c).
  destruct x; auto.
  cut (S x <= 0)%nat. omega.
  eapply first_choices_monotone.
  2: eauto. 2: eauto.
  intro.
  hnf in H3.
  destruct H3 as [q [??]].
  hnf in H3. destruct H3. 2: elim H3.
  subst q.
  assert (SF_spec.first_choices _ (in_record []) c election 0).
  apply (find_0s_correct allc election c); auto.
  assert( 0 = S x)%nat.
  eapply SF_spec.sf_first_choices_unique; eauto.
  inv H5.
  intros.
  hnf in H3.
  destruct H3 as [q[??]].
  elim H3.
Qed.

End cand.

Check run_election_correct.
Print Assumptions run_election_correct.
