Require Import Recdef. 
Require SF_spec.
Require Import SF_tactic.
Require Import RelDec.
Require Import List.
Require Import Sorted.
Require Import Permutation.
Require Import FunctionalExtensionality.
Require Import Classical.
Import ListNotations.

Section cand.

Variable candidate : Set.
Variable reldec_candidate : RelDec (@eq candidate).
Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.

Ltac solve_rcv := SF_tactic.solve_rcv reldec_correct_candidate.
Ltac intuition_nosplit := SF_tactic.intuition_nosplit reldec_correct_candidate.


Lemma next_ranking_cons_or :
forall b1 bal e x,
SF_spec.next_ranking candidate e (b1 :: bal) x ->
SF_spec.next_ranking candidate e [b1] x \/ 
SF_spec.next_ranking candidate e bal x.
intros. inv H; solve_rcv. left.
destruct H4; solve_rcv. eapply SF_spec.next_ranking_valid; solve_rcv.
left. eauto. eapply SF_spec.next_ranking_valid; solve_rcv.
Qed.

Lemma next_ranking_in :
forall e bal x,
  SF_spec.next_ranking candidate e bal x ->
  In x bal.
Proof.
induction bal; solve_rcv.
inv H; solve_rcv. 
Qed.

Lemma no_viable_candidates_cons :
forall a b e,
SF_spec.no_viable_candidates candidate (e) (a ::  b) <->
(SF_spec.no_viable_candidates candidate e [a] /\
SF_spec.no_viable_candidates candidate e b).
split.
intros.
unfold SF_spec.no_viable_candidates in *.
split.
intros. eapply H; eauto. inv H0; simpl in *; intuition.
intros. eapply H; eauto. simpl. intuition.
intros. intuition.
unfold SF_spec.no_viable_candidates in *. simpl in *.
intuition. eapply H0; eauto. 
eapply H1; eauto.
Qed.

Lemma first_choices_app : 
forall c l1 l2 x1 x2  r cnd, 
SF_spec.first_choices c r cnd l1 x1 ->
SF_spec.first_choices c r cnd l2 x2 ->
SF_spec.first_choices c r cnd (l1 ++ l2) (x1 + x2).
Proof.
induction l1; intros.
- simpl in *. inv H. simpl. auto.
- simpl in *. 
  inv H.
  + apply SF_spec.first_choices_selected. auto. fold plus.
    apply IHl1; auto.
  + apply SF_spec.first_choices_not_selected; auto.
Qed.

Lemma first_choices_app_gt :
forall c l1 l2 x1 x2 r cnd,
SF_spec.first_choices c r cnd l1 x1 ->
SF_spec.first_choices c r cnd (l1 ++ l2) (x2) ->
x2 >= x1.
Proof.
induction l1; intros.
- simpl in *. inv H. omega.
- simpl in *. inv H; inv H0; try congruence; try omega.
  eapply IHl1 in H5; eauto. omega.
  eapply IHl1; eauto.
Qed.

Lemma first_choices_perm : 
forall c l1 l2 x r cnd,
Permutation l1 l2 ->
SF_spec.first_choices c r cnd l1 x ->
SF_spec.first_choices c r cnd l2 x.
Proof.
induction l1; intros.
- apply Permutation_nil in H. subst. auto. 
- assert (exists l2s l23, l2 = l2s ++ (a :: l23)). 
  { eapply Permutation_in in H. instantiate (1 := a) in H.
    apply List.in_split in H. auto.
    constructor; auto. }
  destruct H1. destruct H1.
  subst.
  apply Permutation_cons_app_inv in H.
  inv H0.
  + eapply (IHl1 _ n' r cnd) in H; auto.
    clear - H H3.
    { generalize dependent x1. generalize dependent n'.
      induction x0; intros.
      - simpl in *. constructor; auto.
      - simpl in *. inv H. 
        + constructor; auto.
        + apply SF_spec.first_choices_not_selected; auto.
    }
  + eapply IHl1 in H; eauto.
    { clear - H H3.
      generalize dependent x1. generalize dependent x.
      induction x0; intros.
      - simpl in *. apply SF_spec.first_choices_not_selected; auto.
      - simpl in *. inv H.
        + constructor; auto.
        + apply SF_spec.first_choices_not_selected; auto.
    }
Qed.

Lemma selected_participates : forall election (c : candidate) bal  r,
SF_spec.selected_candidate _ r bal c ->
In bal election ->
SF_spec.participates _ c election.
Proof.
induction election; intros.
inv H0.
destruct H0. subst.
unfold SF_spec.participates.
unfold SF_spec.selected_candidate in H.
destruct H. destruct H0.
exists bal. split; eauto.
simpl. auto.
exists x. intuition.
apply next_ranking_in in H1. auto.
eapply IHelection in H0.
unfold SF_spec.participates in H0.
unfold SF_spec.participates.
simpl in *.
destruct H0.
exists x. split; auto. intuition.
destruct H0.
apply H1.
eauto.
Qed.

Lemma participates_cons : forall e a (c : candidate) ,
        SF_spec.participates _ c [a] \/ SF_spec.participates _ c e <->
        SF_spec.participates _ c (a :: e).
Proof.
split.
- intros.
  destruct H.
  + unfold SF_spec.participates in *.
    destruct H. destruct H. destruct H0. destruct H0.
    exists a. simpl in *. intuition.
    subst. exists x0. auto.
  + unfold SF_spec.participates in *. 
    destruct  H. intuition. destruct H1. exists x; intuition.
    exists x0; intuition.
- intros. destruct H.
  destruct H. destruct H0.
  destruct H.
  +  unfold SF_spec.participates.
     subst. left. exists x. intuition.
     exists x0; auto.
  +  right. unfold SF_spec.participates.
     exists x. intuition.
     exists x0; auto.
Qed.


Lemma majority_not_0 :
forall r e x ,
SF_spec.majority candidate r e x ->
exists v, SF_spec.first_choices _ r x e v /\ v <> 0.
Proof.
intros.
unfold SF_spec.majority in *.
edestruct (SF_spec.sf_first_choices_total _ r e x).
edestruct (SF_spec.total_selected_total _ r e).
exists x0. intuition.
subst.
eapply H in H0; eauto.
omega.
Qed.

Lemma update_eliminated_in_rec : forall rec loser c,
SF_spec.update_eliminated candidate (in_record rec) loser c <->
in_record ([loser] :: rec) c.
Proof.
split; intros.
{ induction rec.
  - unfold SF_spec.update_eliminated in H.
    intuition. inv H0. destruct H. inv H.
    subst. unfold in_record. exists [c]. intuition; auto.
  - unfold SF_spec.update_eliminated in  *. intuition.
    unfold in_record in H0. destruct H0. intuition.
    simpl in H2. destruct H2.
    + subst. unfold in_record. exists x. 
      intuition.
    + unfold in_record. exists x. intuition.
    + unfold in_record in H2. destruct H2.
      intuition. simpl in H2. destruct H2.
      * subst. unfold in_record. exists [c].
        intuition.
      * exists x. intuition. }
{ unfold in_record in H. destruct H. intuition. simpl in H0.
  destruct H0. subst. unfold SF_spec.update_eliminated.
  right. inv H1; auto. inv H.
  left. unfold in_record. eauto. }
Qed.

Axiom prop_ext : forall (P Q : Prop), 
  (P <-> Q) -> P = Q.


Lemma update_eliminated_in_rec_eq : forall rec loser c,
SF_spec.update_eliminated candidate (in_record rec) loser c =
in_record ([loser] :: rec) c.
Proof. intros.
apply prop_ext. apply update_eliminated_in_rec.
Qed.


Lemma update_eliminated_in_rec_eq_noc : forall rec loser,
SF_spec.update_eliminated candidate (in_record rec) loser =
in_record ([loser] :: rec).
intros. extensionality c. apply update_eliminated_in_rec_eq.
Qed.

Definition continuing2 b rec:=
exists r, SF_spec.next_ranking candidate rec b r /\ ~SF_spec.overvote candidate r.


Lemma continuing2_continuing : 
forall b rec,
continuing2 b rec <-> SF_spec.continuing_ballot candidate rec b.
Proof.
intros.
split.
intros.
unfold continuing2 in *.
solve_rcv.
destruct H1. apply H1. exists x. auto.
destruct H1. solve_rcv.
eapply SF_spec.next_ranking_unique in H; eauto. subst.
apply H0; eauto.
intros.
unfold continuing2.
solve_rcv.

apply Classical_Prop.not_or_and in H.
destruct H. apply Classical_Prop.NNPP in H.
destruct H. exists x.
split. auto.
intro. apply H0. exists x. auto.
Qed.

Lemma continuing_ballot_cons :
forall r h t,
SF_spec.continuing_ballot candidate r (h :: t) ->
SF_spec.continuing_ballot candidate r [h] \/ ((~SF_spec.overvote candidate h) /\ SF_spec.continuing_ballot candidate r t).
Proof.
intros. repeat rewrite <- continuing2_continuing in *.
induction t. 
- auto.
- unfold continuing2 in *.
  destruct H. destruct H.
  inv H.
  + right. intuition. exists x. auto.
  + destruct H5. 
    *  intuition. 
    * left. exists x.
      intuition. eapply SF_spec.next_ranking_valid.
      apply H3. auto.
Qed.

Lemma continuing_ballot_cons2 :
forall r a b,
SF_spec.continuing_ballot candidate r [a] ->
SF_spec.continuing_ballot candidate r (a :: b).
Proof.
intros. rewrite <- continuing2_continuing in *.
unfold continuing2 in *. destruct H.
exists x.
destruct H. intuition.
clear H0.
inv H. inv H5. eapply SF_spec.next_ranking_valid; eauto.
Qed.

Lemma continuing_ballot_cons3 :
forall t h r
(OV : ~SF_spec.overvote candidate h), 
SF_spec.continuing_ballot candidate r t ->
SF_spec.continuing_ballot candidate r (h :: t).
Proof.
intros. rewrite <- continuing2_continuing in *.
unfold continuing2 in *.
destruct H. destruct H.
destruct (classic (Forall r h)).
exists x. intuition. 
constructor; eauto.
destruct h. exfalso. solve_rcv. apply H1. solve_rcv.
exists (c::h). intuition.
eapply SF_spec.next_ranking_valid. simpl. eauto. 
right. solve_rcv. apply H1. intros. destruct H3. subst. auto.
destruct (rel_dec_p c x0).
subst. auto.
exfalso. apply OV. exists c. exists x0.
simpl. auto.
Qed.

Lemma continuing_ballot_rec_cons : 
forall l r b,
  SF_spec.continuing_ballot candidate (in_record ([l] :: r)) (b) ->
   SF_spec.continuing_ballot candidate (in_record r) (b).
Proof.
  intros. induction b.
  - unfold SF_spec.continuing_ballot in *.  
    intro. apply H. clear H.
    unfold SF_spec.exhausted_ballot. left. intro.
    inv H. inv H1.
  - apply continuing_ballot_cons in H.  
    destruct H.
    apply continuing_ballot_cons2. 
    rewrite <- continuing2_continuing in *.
    unfold continuing2. 
    unfold continuing2 in H.
    destruct H. exists x.
    destruct H. intuition.
    inv H. constructor; solve_rcv.
    destruct H5. intuition.
    eapply SF_spec.next_ranking_valid; eauto.
    right. intro. apply H; clear H.
    unfold in_record in *. solve_rcv.
    intuition.
    apply continuing_ballot_cons3; auto.
Qed.

Lemma next_ranking_cons_or2 :
forall b1 bal e x,
SF_spec.next_ranking candidate e (b1 :: bal) x ->
SF_spec.next_ranking candidate e [b1] x \/ 
(Forall e b1 /\ SF_spec.next_ranking candidate e bal x).
intros. inv H; solve_rcv. left.
destruct H4; solve_rcv. eapply SF_spec.next_ranking_valid; solve_rcv.
left. eauto. eapply SF_spec.next_ranking_valid; solve_rcv.
Qed.

Lemma continuing_ballot_cons4 : (*should be main lemma, don't want to rework proofs :( *)
forall r h t,
SF_spec.continuing_ballot candidate r (h :: t) ->
SF_spec.continuing_ballot candidate r [h] \/ ((~SF_spec.overvote candidate h) /\ SF_spec.continuing_ballot candidate r t /\ Forall r h).
Proof.
intros. repeat rewrite <- continuing2_continuing in *.
induction t. 
- auto.
- unfold continuing2 in *.
  destruct H. destruct H.
  inv H.
  + right. intuition. exists x. auto.
  + destruct H5. 
    *  intuition. 
    * left. exists x.
      intuition. eapply SF_spec.next_ranking_valid.
      apply H3. auto.
Qed.

Lemma selected_cons :
forall r a b c,
SF_spec.selected_candidate candidate  r (a :: b) c ->
SF_spec.selected_candidate candidate r [a] c \/
(Forall r a /\ ~SF_spec.overvote candidate a /\SF_spec.selected_candidate candidate r b c).
Proof.
intros.
unfold SF_spec.selected_candidate in H.
intuition_nosplit. apply continuing_ballot_cons4 in H.
apply next_ranking_cons_or2 in H0.
destruct H, H0.
left. unfold SF_spec.selected_candidate. intuition.
eauto.
rewrite <- continuing2_continuing in H.
unfold continuing2 in H. destruct H. destruct H.
inv H. inv H8. rewrite Forall_forall in H0. firstorder.
destruct H. destruct H2. inv H0. inv H9. rewrite Forall_forall in *.
firstorder.
right. unfold SF_spec.selected_candidate. intuition.
eauto.
Qed.

Lemma first_choices_0_cons :
forall r c h t,
SF_spec.first_choices candidate r c (h :: t) 0 <->
SF_spec.first_choices candidate r c [h] 0 /\
SF_spec.first_choices candidate r c t 0.
Proof.
split.
- intros.
  induction t. intuition. constructor.
  inv H. intuition.
  inv H4.
  apply IHt.
  constructor. auto. auto.
- intros. destruct H.
  inv H. constructor; auto.
Qed.

Lemma next_ranking_record_same :
forall b x c l r,
  In c x ->
  c <> l ->
  SF_spec.next_ranking candidate (in_record r) b x ->
  ~ SF_spec.overvote candidate x ->
  SF_spec.next_ranking candidate (in_record ([l] :: r)) b x.
Proof.
induction b; intros.
inv H1.
inv H1.
- constructor. solve_rcv. specialize (H5 x0); solve_rcv.
  auto.
  eapply IHb; eauto.
- intuition.
  eapply SF_spec.next_ranking_valid.
  apply H5. right. intro.
  apply H1. solve_rcv. simpl in H3. destruct H3; solve_rcv.
  assert (c0 = l). inv H4. subst; intuition. inv H3. subst. clear H4.
  exfalso. apply H2. exists c. exists l. eauto.
Qed.

Lemma ne_still_continuing :
forall b c l  x r,
SF_spec.next_ranking candidate (in_record r) b x ->
SF_spec.continuing_ballot candidate (in_record r) b ->
In c x ->
c <> l ->
SF_spec.continuing_ballot candidate (in_record ([l] :: r)) b.
Proof.
intros. repeat rewrite <- continuing2_continuing in *.
unfold continuing2 in *. intuition_nosplit.
exists x0. split; eauto. 
eapply SF_spec.next_ranking_unique in H; eauto. subst.
eapply next_ranking_record_same; eauto.
Qed.

Lemma selected_rec_cons :
forall r b c l,
c <> l ->
SF_spec.selected_candidate candidate (in_record r) b c ->
SF_spec.selected_candidate candidate (in_record ([l]::r)) b c.
intros.
induction b. solve_rcv.
apply selected_cons in H0. 
destruct H0. 
- clear IHb. 
  unfold SF_spec.selected_candidate in *.
  intuition_nosplit.
  split. 
  + apply continuing_ballot_cons2. 
  eapply ne_still_continuing; eauto.
  + inv H1. inv H8.
    destruct H7. exists x. intuition.
    eapply SF_spec.next_ranking_valid; eauto.
    exists x. intuition. eapply SF_spec.next_ranking_valid; eauto.
    right. intro. apply H1. rewrite <- continuing2_continuing in *. 
    unfold continuing2 in *. unfold in_record in *. intuition_nosplit. 
    simpl in *. destruct H3; subst; try solve [solve_rcv].
    inv H4; intuition_nosplit. inv H0. inv H10. intuition.
    exfalso. apply H6. solve_rcv.
- intuition. clear H3. 
  unfold SF_spec.selected_candidate in *.
  intuition_nosplit. split. 
  rewrite <- continuing2_continuing. unfold continuing2. exists x.
  intuition. constructor; auto. rewrite Forall_forall in *.
  intro. specialize (H1 x0). intro. intuition. 
  solve_rcv.  rewrite <-  continuing2_continuing in *.
  unfold continuing2 in *. intuition_nosplit.
  eapply SF_spec.next_ranking_unique in H2; eauto. subst.
  auto.
  exists x. intuition.
  constructor; auto.
  rewrite Forall_forall in *. intros. specialize (H1 x0). 
  solve_rcv.
Qed.

Lemma first_choices_rec_0 :
forall c l r e,
  SF_spec.first_choices candidate (in_record ([l] :: r)) c e 0 ->
  c <> l ->
  SF_spec.first_choices candidate (in_record r) c e 0.
Proof.
intros.
induction e.
- constructor.
- apply first_choices_0_cons in H. destruct H. intuition.
  apply first_choices_0_cons. intuition.
  inv H.
  constructor. intro. apply H5. clear H5. 
  apply selected_rec_cons; auto. constructor.
Qed.



Lemma first_choices_0_loser :
forall c election l,
~in_record l c ->
SF_spec.participates _ c election ->
SF_spec.first_choices candidate (in_record l) c election 0 ->
SF_spec.is_loser _ (in_record l) election c.
Proof.
intros. unfold SF_spec.is_loser in *.
split.
- unfold SF_spec.viable_candidate. 
  split.
  + unfold in_record. intuition_nosplit. apply H. unfold in_record. eauto.
  + auto.
- intros. eapply SF_spec.sf_first_choices_unique in H1; eauto. subst. omega.
Qed.

Lemma in_record_nil_nil (c: candidate) :
forall l, in_record l c <-> in_record ([] :: l) c.
split; intros; unfold in_record in *;
intuition_nosplit. exists x. simpl. intuition.
inv H. inv H0. exists x; simpl; auto.
Qed.

Lemma in_record_nil_nil_eq :
forall (l : list (list candidate)), in_record l = in_record ([] :: l).
intros. extensionality c. apply prop_ext.
apply in_record_nil_nil.
Qed.

Fixpoint flatten {A} (l : list (list A)) : list A :=
match l with
| h :: t => h ++ flatten t
| nil => nil
end.


Lemma in_flatten :
forall A (x: list A) l (c : A),
(exists x, In x l /\ In c x) <-> In c (flatten l).
split; intros.
- induction l.
  +  intuition_nosplit.
  + intuition_nosplit. simpl in *. destruct H.
    * subst. apply in_app_iff. auto.
    * apply in_app_iff. right. apply IHl. eauto.
- induction l.
  inv H.
  simpl in *. apply in_app_or in H. destruct H.
  eauto.
  edestruct IHl; eauto.
  exists x0. intuition.
Qed.

Lemma in_record_flatten (c : candidate): 
forall l, in_record l c <-> in_record ([flatten l]) c.
Proof.
split; intros;
unfold in_record in *; intuition_nosplit.
exists (flatten l). intuition. apply in_flatten; eauto.
inv H. apply in_flatten in H0. auto. apply nil.
inv H1.
Qed.

Fixpoint inb {A} {ed : (forall (a b : A), {a = b} + {a <> b})}  i (l : list A) :=
match l with
| h :: t => if ed i h then true else @inb A ed i t
| nil => false
end. 

Lemma inb_in :
forall A (i :A) l ed,
@inb A ed i l =true <-> In i l.
split; intros; induction l; simpl in *; try destruct (ed i a); intuition.
Qed.


Fixpoint remove_dups' {A} (ed : (forall (a b : A), {a = b} + {a <> b}))  (l : list A) acc  :=
match l with 
| h :: t => if @inb A ed h acc then remove_dups' ed t acc else remove_dups' ed t (h :: acc)
| nil => acc
end. 

Definition remove_dups {A} (ed : (forall (a b : A), {a = b} + {a <> b}))  (l : list A) :=
remove_dups' ed l nil.

Lemma in_acc_in :
forall A ed l (i :A) acc, In i acc -> In i (remove_dups' ed l acc).
Proof.
induction l; intros.
- simpl. auto.
- simpl in *. destruct (inb a acc) eqn:?. rewrite inb_in in *.
  intuition.
  intuition.
Qed.

Lemma In_remove_dups' :
forall {A} ed (l : list A) i acc, In i l -> In i (remove_dups' ed l acc).
Proof.
induction l; intros.
- inv H.
- simpl in *. destruct (inb a acc) eqn:?. rewrite inb_in in Heqb.
  destruct H. subst. apply in_acc_in. auto.
  intuition.
  intuition. subst. apply in_acc_in. simpl. auto.
Qed.

Lemma remove_dups_in :
forall {A} ed (l : list A) i acc, 
In i (remove_dups' ed l acc) ->
(In i l \/ In i acc).
Proof.
induction l; intros. 
- intuition.
- simpl in *. destruct (inb a acc) eqn:?.
  rewrite inb_in in Heqb. edestruct IHl; eauto.
  edestruct IHl; eauto. simpl in H0. intuition.
Qed.

Lemma remove_dups_in_iff :
forall A ed (i : A) l,
In i (remove_dups ed l) <-> In i l.
Proof.
intuition.
unfold remove_dups in H. apply remove_dups_in in H. firstorder.
unfold remove_dups. apply In_remove_dups'. auto.
Qed.


Lemma nodup_remove_dups' :
forall A ed (l : list A) acc,
NoDup acc -> 
NoDup (remove_dups' ed l acc).
Proof.
induction l; intros; simpl. auto. 
simpl. destruct (inb a acc) eqn:?.
auto.  apply IHl. constructor.
intro. rewrite <- inb_in in H0. instantiate (1:= ed) in H0. 
congruence. 
auto.
Qed.

Lemma nodup_remove_dups :
forall A ed (l : list A) ,
NoDup (remove_dups ed l ).
Proof. unfold remove_dups. intros. apply nodup_remove_dups'. constructor.
Qed.

Lemma in_record_remove_dups (c : candidate): 
forall l ed, in_record l c <-> in_record ([remove_dups ed (flatten l)]) c.
Proof.
split; intros.
unfold in_record in *. intuition_nosplit.
exists (remove_dups ed (flatten l)).
intuition.
apply remove_dups_in_iff. apply in_flatten. apply nil. 
eauto.
unfold in_record in *. intuition_nosplit.
inv H. apply remove_dups_in_iff in H0. apply in_flatten in H0.
eauto. apply nil. inv H1.
Qed.

Lemma in_record_remove_dups_eq :
forall l ed, @in_record candidate l  = in_record ([remove_dups ed (flatten l)]).
Proof.
intros. extensionality c. apply prop_ext. apply in_record_remove_dups.
Qed.

Lemma in_record_duplicate_remove :
forall h t l c,
@in_record candidate l h -> 
(in_record ((h::t) :: l) c <-> in_record (t :: l) c).
intuition.
- unfold in_record in *; intuition_nosplit; simpl in *; 
  repeat (intuition; subst; eauto; simpl in *).
- unfold in_record in *. intuition_nosplit. simpl in H0.
  destruct H0. subst. simpl.
  exists (h :: x). intuition.
  simpl. eauto.
Qed.

Lemma in_record_duplicate_remove_eq :
forall h t l,
@in_record candidate l h -> 
(in_record ((h::t) :: l)  = in_record (t :: l) ).
Proof.
intros. extensionality c. apply prop_ext. apply in_record_duplicate_remove; auto.
Qed.

Lemma selected_cons' : 
forall r a b c,
Forall r a ->
~SF_spec.overvote _ a ->
SF_spec.selected_candidate candidate r b c ->
SF_spec.selected_candidate _ r (a :: b) c.
Proof.
intros. rewrite Forall_forall in *.
induction b.
inv H1. intuition_nosplit. 
destruct H1.  intuition_nosplit.
unfold SF_spec.selected_candidate.
split. 
- rewrite <- continuing2_continuing in *.
  unfold continuing2 in *.
  intuition_nosplit. exists x0. intuition.
  constructor; try rewrite Forall_forall; auto. 
- exists x. intuition.
  constructor; auto.
  rewrite Forall_forall. auto.
Qed.

Lemma first_choices_0_not_next :
forall election c b l rnk
(OV: ~SF_spec.overvote _ rnk),
 SF_spec.first_choices candidate (in_record l) c election 0 ->
In b election ->
SF_spec.next_ranking candidate (in_record l) b rnk ->
~In c rnk.
Proof.
intros.
intro.
induction election.
inv H0.
simpl in H0.
destruct H0.
- clear IHelection. subst. induction b.  
  + inv H1.
  + inv H1. 
    * apply IHb; auto.  inv H. intuition. 
      constructor. intro. apply H3. clear H3. apply selected_cons'; auto.
      auto.
    * destruct H6. intuition. inv H. apply H5. clear H5.
      split. rewrite <- continuing2_continuing. unfold continuing2.
      exists rnk. intuition. eapply SF_spec.next_ranking_valid.
      apply H4. intuition.
      exists rnk. intuition. eapply SF_spec.next_ranking_valid. apply H4. intuition.
- apply IHelection; auto. inv H. auto.
Qed.

Lemma not_selected_eliminated :
forall r c a b,
~SF_spec.overvote candidate (c :: a) ->
~SF_spec.selected_candidate _ r ((c :: a)::b) c ->
r c.
Proof.
intros.
- unfold SF_spec.selected_candidate in H0. rewrite <- continuing2_continuing in H0.
  destruct (classic (r c)). auto. exfalso.
  apply H0. clear H0. split.
  unfold continuing2. exists (c :: a).
  intuition. eapply SF_spec.next_ranking_valid with (c := c). 
  simpl. auto. auto.
  exists (c::a). intuition.
  apply SF_spec.next_ranking_valid with (c := c). simpl. auto.
  intuition.
Qed.

Lemma rem_0_still_next :
forall c l  x b election,
SF_spec.first_choices candidate (in_record [l]) c (election) 0 ->
In b election ->
SF_spec.next_ranking candidate (in_record [c :: l]) b x ->
SF_spec.next_ranking candidate (in_record [l]) b x.
intros. induction election.
- inv H0.
- simpl in H0. destruct H0. 
  + subst. clear IHelection.
    induction b. 
    * inv H1.
    * { inv H. inv H1.
        - destruct a.
          + constructor; auto. apply IHb; auto. constructor.
            * intro. apply H3. clear H3. apply selected_cons'; auto.
            * auto.
          + rewrite Forall_forall in H2. pose proof (H2 c0).  simpl in H. intuition.
            clear H6. unfold in_record in H. intuition_nosplit.
            simpl in H. intuition. subst.
            simpl in H1. destruct H1.
            * subst. constructor; auto. apply not_selected_eliminated in H3; auto.
              rewrite Forall_forall. intros.
              simpl in H. destruct H. solve_rcv.
              apply SF_spec.not_overvote_all_same with (c := c0) in H4; simpl; auto.
              rewrite Forall_forall in H4. specialize (H4 x0).
              simpl in H4. intuition. subst. auto. apply (fun _ => False).
              apply H0. clear H0. constructor; auto.
              intro. apply H3. apply selected_cons'; auto. apply not_selected_eliminated in H3; auto.
              rewrite Forall_forall. intros. simpl in *. intuition; try solve[solve_rcv].
              apply SF_spec.not_overvote_all_same with (c := c0) in H4; simpl; auto.
              rewrite Forall_forall in H4. specialize (H4 x0). simpl in *. intuition.
              subst. auto. apply (fun _ => False).
            * constructor; auto. apply SF_spec.not_overvote_all_same with (c := c0) in H4;
                                 simpl; auto.
              rewrite Forall_forall in *.
              intros. simpl in H1. intuition; subst; auto. unfold in_record. exists l.
              simpl; auto. exists l. intuition. assert (c0 = x0). apply H4; simpl; auto.
              subst. auto. apply (fun _ => False).
              apply H0. clear H0. constructor; auto.
              intro. apply H3. apply selected_cons'; auto. 
              rewrite Forall_forall. intros. simpl in *. intuition; try solve[solve_rcv].
              apply SF_spec.not_overvote_all_same with (c := c0) in H4; simpl; auto.
              rewrite Forall_forall in H4. specialize (H4 x0). simpl in *. intuition.
              subst. exists l. simpl. auto. apply (fun _ => False).
        - destruct H6.
           + eapply SF_spec.next_ranking_valid; eauto.
           + eapply SF_spec.next_ranking_valid; eauto.
             right. intro. apply H. unfold in_record in H0. intuition_nosplit.
             exists (c::l). intuition. simpl. inv H0. auto. inv H4.
      }
  + apply IHelection; auto. rewrite first_choices_0_cons in H. intuition.
Qed.

Lemma rem_0_still_continuing :
forall election c l b,
SF_spec.first_choices candidate (in_record [l]) c (election) 0 ->
In b election ->
SF_spec.continuing_ballot candidate (in_record [c :: l]) b ->
SF_spec.continuing_ballot candidate (in_record [l]) b.
intros. rewrite <- continuing2_continuing in *. unfold continuing2 in *.
intuition_nosplit. exists x. intuition.
eapply rem_0_still_next; eauto.    
Qed.

Lemma next_ranking_add_c : 
forall c l a x election,
SF_spec.first_choices candidate (in_record [l]) c election 0 ->
In a election ->
SF_spec.next_ranking candidate (in_record [l]) a x ->
SF_spec.next_ranking candidate (in_record [c::l]) a x.
Proof.
  intros c l a x election.
  remember (in_record [l]) as P.
  intros H H1 H2.
  assert( SF_spec.overvote _ x \/ ~In c x ).
  { subst P.
    destruct (classic (SF_spec.overvote _ x)); auto. right.
    intro.
    induction election.
    elim H1.
    rewrite first_choices_0_cons in H. destruct H.
    simpl in H1. destruct H1; auto.
    subst a0.
    inversion H; clear H; subst.
    apply H6.
    split.
    intro.
    destruct H; auto.
    elim H.
    exists x. auto.
    destruct H as [q [??]].
    assert (x = q).
    eapply SF_spec.next_ranking_unique; eauto. subst q.
    auto.
    exists x; split; auto.
  }
  clear H H1.

  induction H2.
  * apply SF_spec.next_ranking_eliminated; auto.
    rewrite Forall_forall; intros.
    rewrite Forall_forall in H.
    rewrite HeqP in H.
    apply H in H3.
    destruct H3 as [q [??]].
    simpl in H3.
    destruct H3 as [?|[]]. subst q.
    exists (c::l). simpl; auto.
  * apply SF_spec.next_ranking_valid with c0; auto.
    intuition.
    right. intro.
    destruct H0 as [q [??]].
    simpl in H0. intuition. subst q.
    simpl in H3. destruct H3.
    subst c0. auto.
    apply H2.
    rewrite HeqP.
    exists l. split; simpl; auto.
Qed.

Lemma total_selected_remove_0 :
forall election c l t,
  SF_spec.first_choices candidate (in_record [l]) c election 0 ->
  SF_spec.total_selected candidate (in_record [c :: l]) election t ->
  SF_spec.total_selected candidate (in_record [l]) election t.
Proof.
induction election; intros.
inv H0. constructor.
inv H0.
constructor.
eapply rem_0_still_continuing; simpl; eauto. simpl. eauto. 
eapply IHelection; eauto. inv H; auto. constructor; auto.
unfold SF_spec.exhausted_ballot in *. 
destruct H3.
left. intro. apply H0. clear H0.
intuition_nosplit. exists x. eapply next_ranking_add_c; eauto.
simpl. auto.
right. intuition_nosplit. exists x. intuition.
eapply rem_0_still_next in H0; simpl; eauto. simpl. eauto.
eapply IHelection; eauto.
inv H. auto.
Qed.


Lemma not_isloser_nil :
forall loser r,
~ SF_spec.is_loser candidate r [] loser. 
intros. intro.
unfold SF_spec.is_loser in *.
intuition. inv H0. inv H2. intuition.
Qed.

Lemma not_winner_nil :
forall r winner,
~SF_spec.winner candidate [] r winner.
intros. intro. inv H. 
- unfold SF_spec.majority in *.
  specialize (H0 0 0). assert (0 * 2 > 0).
  apply H0. constructor. constructor. omega.
- apply not_isloser_nil in H1. auto.
Qed.

Lemma in_record_flatten_eq : forall r,
@in_record candidate r = in_record [flatten r].
intros. extensionality c. apply prop_ext. apply in_record_flatten.
Qed.

End cand.
