Require Import Classical.
Require Import List.
Require Import Arith.

Require Import Ranked_properties.
Require Import SF_spec.
Require Import SF_tactic.
Require Import SF_properties.

(**  The formal specification given in SF_spec always chooses exactly one loser at each
     round; the choice is nondeterministic in the case of ties.  However, the statute
     text and actual election practice is to implement the following optimization:

         In a given round, choose the largest set of losers such that the combined sum
         of continuing votes for all losing candidates is less than the continuing votes
         for all other candidates.  Simultaneously eliminate all losing candidates in this set.

     Here we prove that this procedure is indeed just an optimization of the simple procedure
     that chooses exactly one loser at each round.  Actually, we prove something slightly more
     general, which is that one may chose _any_ set satisfying the condition above and the
     result is unchanged (i.e., prefering the largest such set makes no difference in the end).
  *)

Lemma first_choice_loser_set :
  forall (candidate:Set) e c cs elim x y,
    In c cs ->
    count_votes candidate (fun b => exists c, selected_candidate _ elim b c /\ In c cs) e x ->
    first_choices _ elim c e y ->
    y <= x.
Proof.
  intros candidate e. induction e; simpl; intros.
  * inv H0. inv H1. auto.
  * inv H0; inv H1; auto.
    cut (n' <= n). omega.
    eapply IHe; eauto.
    cut (y <= n). omega.
    eapply IHe; eauto.
    elim H4.
    exists c. split; auto.
    eapply IHe; eauto.
Qed.

Lemma count_votes_total candidates P e :
  exists c, count_votes candidates P e c.
Proof.
  induction e.
  * exists 0. constructor.
  * destruct IHe as [n ?].
    destruct (classic (P a)).
    exists (S n).
    apply count_satisfies; auto.
    exists n.
    apply count_not_satisfies; auto.
Qed.

Lemma count_votes_monotone candidates (P P':ballot candidates -> Prop) e x y :
  (forall b, P b -> P' b) ->
  count_votes candidates P e x ->
  count_votes candidates P' e y ->
  x <= y.
Proof.
  intros. revert x y H0 H1. induction e; intros.
  * inv H0. inv H1. auto.
  * inv H0; inv H1; auto.
    cut ( n <= n0 ). omega.
    apply IHe; auto.
    elim H3. apply H. auto.
Qed.

Lemma majority_unique :
  forall candidate r e x x',
    SF_spec.majority candidate r e x ->
    SF_spec.majority candidate r e x' ->
    x = x'.
Proof.
  intros.
  destruct (classic (x = x')); auto. elimtype False.
  destruct (SF_spec.total_selected_total candidate r e) as [t ?].
  destruct (SF_spec.sf_first_choices_total candidate r e x) as [n ?].
  destruct (SF_spec.sf_first_choices_total candidate r e x') as [n' ?].
  generalize (H t n H2 H3); intro.
  generalize (H0 t n' H2 H4); intro.
  assert ( n + n' <= t ).
  { clear H H0 H5 H6.
    revert t n n' H2 H3 H4.
    induction e; simpl; intros.
    inv H2. inv H3. inv H4. auto.
    inv H2. inv H3. inv H4.
    elim H1.
    eapply selected_candidate_unique; eauto.
    cut (n'0 + n' <= n0). omega.
    apply IHe; eauto.
    inv H4.
    cut (n + n'0 <= n0). omega.
    apply IHe; eauto.
    cut (n + n' <= n0). omega.
    apply IHe; eauto.
    inv H3.
    rewrite exhausted_ballot_next_ranking_iff in H5.
    destruct H2.
    destruct H0 as [q [??]].
    elim H.
    right. exists q. split; auto.
    inv H4.
    rewrite exhausted_ballot_next_ranking_iff in H5.
    destruct H3.
    destruct H0 as [q [??]].
    elim H.
    right. exists q. split; auto.
    apply IHe; auto.
  }
  omega.
Qed.

Lemma exhausted_ballot_monotone :
  forall (candidate:Set) (elim elim':candidate -> Prop) b,
    (forall x, (exists r, In r b /\ In x r) -> elim x -> elim' x) ->
    SF_spec.exhausted_ballot candidate elim b ->
    SF_spec.exhausted_ballot candidate elim' b.
Proof.
  unfold exhausted_ballot. intuition.
  left. intros [r ?].
  induction H0.
  destruct (classic (Forall elim r')).
  apply IHnext_ranking.
  intros.
  apply (H x); auto.
  { destruct H5 as [r0 [??]]. exists r0. split; simpl; auto. }
  intro.
  apply H1.
  destruct H5 as [r0 ?].
  exists r0.
  apply SF_spec.next_ranking_eliminated; auto.
  elim H1.
  exists r'.
  destruct r'.
  elim H4.
  rewrite Forall_forall.
  simpl; intuition.
  apply SF_spec.next_ranking_valid with c; simpl; auto.
  right.
  intro.
  apply H4.
  rewrite Forall_forall; intros.
  destruct (classic (x = c)).
  subst x; auto.
  elim H2.
  exists x. exists c.
  simpl; intuition.
  apply H1. exists r.
  apply SF_spec.next_ranking_valid with c; auto.
  intuition.
  right. intro.
  apply H3; auto.
  apply H; auto.
  exists r; split; simpl; auto. 
  destruct H1 as [r [??]].
  right. exists r. split; auto.
  induction H0.
  apply SF_spec.next_ranking_eliminated; auto.
  rewrite Forall_forall. intros.
  apply H.
  exists r'; split; simpl; auto.
  rewrite Forall_forall in H0; auto.
  apply IHnext_ranking.
  intros. apply H; auto.
  destruct H4 as [r0 [??]].
  exists r0; split; simpl; auto.
  auto.
  apply SF_spec.next_ranking_valid with c; auto.
Qed.

Lemma total_selected_elim_eq :
  forall candidate elim elim' e n,
    (forall x, participates _ x e -> (elim x <-> elim' x)) ->
    SF_spec.total_selected candidate elim e n ->
    SF_spec.total_selected candidate elim' e n.
Proof.
  intros.
  induction H0.
  * apply total_nil.
  * apply total_continuing; auto.
    intro. apply H0.
    eapply exhausted_ballot_monotone. 2: eauto.
    intros. rewrite H; auto.
    hnf; simpl; eauto.
    apply IHtotal_selected.
    intros. apply H.
    destruct H2 as [q [??]].
    exists q; split; simpl; auto.
  * apply total_exhausted; auto.
    eapply exhausted_ballot_monotone. 2: eauto.
    intros. rewrite <- H; auto.
    hnf; simpl; eauto.
    apply IHtotal_selected.
    intros. apply H.
    destruct H2 as [q [??]].
    hnf; simpl; eauto.
Qed.

Lemma next_ranking_elim_eq :
  forall candidate elim elim' b r,
    (forall x, (exists r, In r b /\ In x r) -> (elim x <-> elim' x)) ->
    SF_spec.next_ranking candidate elim b r ->
    SF_spec.next_ranking candidate elim' b r.
Proof.
  intros. induction H0.
  * apply next_ranking_eliminated; auto.
    rewrite Forall_forall; intros.
    rewrite <- H.
    rewrite Forall_forall in H0. auto.
    simpl; eauto.
    apply IHnext_ranking; auto.
    intros.
    apply H.
    destruct H3 as [r0 [??]].
    simpl; eauto.
  * apply next_ranking_valid with c; intuition.
    right.
    rewrite <- H. auto.
    simpl; eauto.
Qed.


Lemma selected_candidate_elim_eq :
  forall candidate elim elim' b c,
    (forall x, (exists r, In r b /\ In x r) -> (elim x <-> elim' x)) ->
    SF_spec.selected_candidate candidate elim b c ->
    SF_spec.selected_candidate candidate elim' b c.
Proof.
  intros.
  destruct H0; split.
  intro. apply H0.
  eapply exhausted_ballot_monotone. 2: eauto.
  intuition. rewrite H; auto.
  destruct H1 as [r [??]].
  exists r; split; auto.
  eapply next_ranking_elim_eq. 2: eauto.
  auto.
Qed.

Lemma first_choices_elim_eq :
  forall candidate elim elim' e c n,
    (forall x, SF_spec.participates _ x e -> (elim x <-> elim' x)) ->
    SF_spec.first_choices candidate elim c e n ->
    SF_spec.first_choices candidate elim' c e n.
Proof.
  intros.
  induction H0.
  * apply first_choices_nil.
  * apply first_choices_selected; auto.
    eapply selected_candidate_elim_eq. 2: eauto.
    intros; apply H.
    hnf; simpl; eauto.
    apply IHfirst_choices.
    intros. apply H.
    destruct H2 as [q [??]].
    exists q; simpl; eauto.
  * eapply first_choices_not_selected; auto.
    intro. apply H0.
    eapply selected_candidate_elim_eq. 2: eauto.
    intros. rewrite H; intuition.
    hnf; simpl; eauto.
    apply IHfirst_choices.
    intros; apply H.
    destruct H2 as [q [??]].
    exists q; simpl; eauto.
Qed.

Lemma majority_elim_eq :
  forall candidate elim elim' e c,
    (forall x, SF_spec.participates _ x e -> (elim x <-> elim' x)) ->
    SF_spec.majority candidate elim e c ->
    SF_spec.majority candidate elim' e c.
Proof.
  intros; hnf; intros.
  apply H0; auto.
  eapply total_selected_elim_eq; eauto.
  intros. rewrite H; auto.
  intuition.
  eapply first_choices_elim_eq; eauto.
  intros. rewrite H; auto.
  intuition.
Qed.

Lemma is_loser_elim_eq :
  forall candidate elim elim' e c,
    (forall x, SF_spec.participates _ x e -> (elim x <-> elim' x)) ->
    SF_spec.is_loser candidate elim e c ->
    SF_spec.is_loser candidate elim' e c.
Proof.
  repeat intro.
  destruct H0. split.
  destruct H0. split; auto.
  rewrite <- H; auto.
  intros.
  eapply H1.
  2: eapply first_choices_elim_eq. 3: eauto.
  3: eapply first_choices_elim_eq. 4: eauto.
  destruct H2; split; auto.
  rewrite H; auto.
  intro. symmetry. auto.
  intro. symmetry. auto.
Qed.

Lemma winner_elim_eq :
  forall candidate elim elim' e c,
    (forall x, SF_spec.participates _ x e -> (elim x <-> elim' x)) ->
    SF_spec.winner candidate e elim c ->
    SF_spec.winner candidate e elim' c.
Proof.
  intros.
  revert elim' H.
  induction H0; intros.
  * apply winner_now.
    eapply majority_elim_eq; eauto.
  * apply winner_elimination with loser; auto.
    red; intros [c ?].
    apply H. exists c.
    eapply majority_elim_eq; eauto.
    intro. intro.
    rewrite H2; intuition.
    eapply is_loser_elim_eq; eauto.
    apply IHwinner.
    unfold eliminated'.
    unfold update_eliminated.
    intuition.
    rewrite H2 in H5; auto.
    rewrite H2; auto.
Qed.

Lemma disjoint_first_choices :
  forall (candidate:Set) (eliminated:candidate -> Prop) e c1 c2 n1 n2 t,
    c1 <> c2 ->
    first_choices _ eliminated c1 e n1 ->
    first_choices _ eliminated c2 e n2 ->
    total_selected _ eliminated e t ->
    n1 + n2 <= t.
Proof.
  intros until e. induction e; intros.
  * inv H0. inv H1. inv H2. omega.
  * inv H2. inv H0; inv H1.
    + elim H. eapply selected_candidate_unique; eauto.
    + cut (n' + n2 <= n). omega.
      eapply IHe; eauto.
    + cut (n1 + n' <= n). omega.
      eapply IHe; eauto.
    + cut (n1 + n2 <= n). omega.
      eapply IHe; eauto.
    + eapply IHe; eauto.
      inv H0; auto.
      destruct H4. elim H0; auto.
      inv H1; auto.
      destruct H4. elim H1; auto.
Qed.


Section sf_spec_opt.
  Variable candidate : Set.
  Variable e : election candidate.
  Variable losers : list candidate.
  Variable loserCount : nat.

  Variables eliminated eliminated':candidate -> Prop.

  Hypothesis Hdups : NoDup losers.

  Hypothesis Hcount : count_votes _ (fun b => exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers) e loserCount.
  Hypothesis Hviable : forall l, In l losers -> viable_candidate _ eliminated e l.
  Hypothesis Hnonloser : exists c, ~In c losers /\ SF_spec.viable_candidate _ eliminated e c.
  Hypothesis Hdominated :
      forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count.
  Hypothesis Helim_eq :
      forall x, eliminated' x <-> eliminated x \/ In x losers.

  Lemma sf_opt_loser_in_set :
    forall
      (loser : candidate),
      length losers > 0 ->
      is_loser candidate eliminated e loser ->
      In loser losers.
  Proof.
    intros.
    destruct (classic (In loser losers)); auto. elimtype False.
    destruct (SF_spec.sf_first_choices_total _ eliminated e loser) as [lCount HlCount].
    assert (loserCount < lCount).
    apply Hdominated with loser; auto.
    destruct H0; auto.
    destruct losers.
    simpl in H. omega.
    destruct H0.
    destruct (SF_spec.sf_first_choices_total _ eliminated e c) as [cn Hcn].
    assert( lCount <= loserCount ).
    transitivity cn.
    apply H3 with c; auto.
    apply Hviable. simpl; auto.
    eapply first_choice_loser_set; eauto. simpl; auto.
    simpl in H2.
    omega.
  Qed.

  Lemma sf_opt_inductive_step :
    forall
      (loser : candidate)
      (losers' : list candidate),

      is_loser candidate eliminated e loser ->
      (forall x0 : candidate, In x0 losers <-> x0 = loser \/ In x0 losers') ->

      forall (c : candidate) (count : nat),
        ~ In c losers' ->
        viable_candidate candidate (update_eliminated candidate eliminated loser) e c ->
        first_choices candidate (update_eliminated candidate eliminated loser) c e count ->
        loserCount < count.
   Proof.
     intros.
     destruct (SF_spec.sf_first_choices_total _ eliminated e c) as [count0 ?].
     destruct (SF_spec.sf_first_choices_total _ eliminated e loser) as [lCount HlCount].
     assert ( count0 > 0 \/ (lCount = 0 /\ count0 = 0) ).
     { destruct count0. auto.
       cut ( lCount <= 0 ). omega.
       destruct H.
       apply H5 with c; auto.
       destruct H2; split; auto.
       intro. apply H2; hnf; auto.
       left. omega.
     }
     destruct H5.
     apply lt_le_trans with count0; auto.
     apply (Hdominated c count0); auto.
     intro.
     rewrite H0 in H6.
     destruct H6; auto.
     { subst c. destruct H2. elim H2; hnf; auto. }
     { destruct H2; split; auto.
       intro. apply H2; hnf; auto. }
     apply first_choices_monotone with candidate eliminated (SF_spec.update_eliminated _ eliminated loser) e c; auto.
     unfold update_eliminated; simpl; auto.
     { intros [?|?].
       destruct H2.
       elim H2; hnf; simpl; auto.
       subst c.
       destruct H2. elim H2; hnf; auto.
     }
     unfold update_eliminated; simpl; auto.
     destruct H5. subst.
     destruct (classic (In c losers)).
     rewrite H0 in H5.
     destruct H5. 2: elim H1; auto.
     subst c.
     destruct H2.
     elim H2; hnf; simpl; auto.
     assert (loserCount < 0).
     apply Hdominated with c; auto.
     destruct H2; split; auto.
     intro; apply H2; hnf; auto.
     elimtype False; omega.
   Qed.

   Lemma sf_opt_majority_forward :
     forall w,
       majority _ eliminated e w ->
       majority _ eliminated' e w.
   Proof.
     repeat intro.
     destruct (SF_spec.sf_first_choices_total _ eliminated e w) as [wc ?].
     destruct (SF_spec.total_selected_total _ eliminated e) as [t ?].
     generalize (H t wc H3 H2). intros.
     red. red in H4.
     assert ( wc <= winner_votes ).
     { eapply first_choices_monotone.
       2: apply H2.
       2: apply H1.
       rewrite Helim_eq. intros [?|?].
       destruct (nonzero_first_choices_selected _ eliminated w e wc) as [b [??]]; auto.
       omega.
       eapply selected_candidate_not_eliminated; eauto.
       { destruct Hnonloser as [c [??]].
         destruct (sf_first_choices_total _ eliminated e c) as [cn ?].
         assert (loserCount < cn).
         eapply Hdominated; eauto.
         assert ( cn + wc <= t ).
         { eapply disjoint_first_choices.
           2: eauto. 2: eauto. 2: eauto.
           intro. subst c. contradiction.
         }
         assert ( wc <= loserCount ).
         {
           clear -Hcount H5 H2.
           revert wc loserCount Hcount H2.
           induction e; intros.
           * inv H2. omega.
           * inv H2; inv Hcount.
             + cut (n' <= n). omega.
               apply IHe0; auto.
             + elim H2; eauto.
             + cut (wc <= n). omega.
               apply IHe0; eauto.
             + apply IHe0; eauto.
         }
         omega.
       }
       intros. rewrite Helim_eq. auto.
     }
     assert ( total_votes <= t ).
     { clear -H0 H3 Helim_eq.
       revert total_votes t H0 H3.
       induction e; intros.
       inv H3. inv H0. auto.
       inv H3. inv H0.
       cut (n0 <= n). omega.
       apply IHe0; auto.
       transitivity n.
       apply IHe0; auto.
       omega.
       inv H0.
       elim H3.
       eapply exhausted_ballot_monotone.
       2: eauto.
       intros. rewrite Helim_eq. auto.
       apply IHe0; auto.
     }
     omega.
  Qed.

End sf_spec_opt.


Lemma next_ranking_back :
  forall (candidate:Set) (elim elim':candidate -> Prop) b r c,
    (forall x, elim x -> elim' x) ->
    In c r ->
    next_ranking _ elim' b r ->
    next_ranking _ elim b r \/
    (exists c' r',
       ~overvote _ r' /\
       next_ranking _ elim b r' /\
       In c' r' /\ elim' c' /\ ~elim c').
Proof.
  intros. induction H1.
  * destruct (classic (Forall elim r')).
    destruct IHnext_ranking; auto.
    left. apply SF_spec.next_ranking_eliminated; auto.
    destruct H5 as [c' [q [?[?[?[??]]]]]].
    right.
    exists c'. exists q. intuition.
    apply SF_spec.next_ranking_eliminated; auto.
    destruct (classic (exists x, In x r' /\ ~elim x)).
    destruct H5 as [x [??]].
    right. exists x. exists r'.
    repeat split; auto.
    apply SF_spec.next_ranking_valid with x; auto.
    rewrite Forall_forall in H1.
    apply H1; auto.
    elim H4.
    rewrite Forall_forall; intros.
    destruct (classic (elim x)); auto.
    elim H5.
    eauto.
  * left. apply SF_spec.next_ranking_valid with c0; auto.
    intuition.
Qed.

Lemma continuing_ballot_back :
  forall (candidate:Set) (elim elim':candidate -> Prop) b,
  (forall x, elim x -> elim' x) ->
  continuing_ballot _ elim' b ->
  continuing_ballot _ elim b.
Proof.
  repeat intro.
  apply H0.
  destruct H1.
  left. intros [r ?]. elim H1.
  clear H0 H1.
  induction H2.
  destruct (classic (exists x, In x r' /\ ~elim x)).
  destruct H3 as [x [??]].
  exists r'.
  apply SF_spec.next_ranking_valid with x; auto.
  destruct IHnext_ranking as [q ?].
  exists q.
  apply SF_spec.next_ranking_eliminated; auto.
  rewrite Forall_forall; intros.
  destruct (classic (elim x)); auto.
  elim H3; eauto.
  exists r.
  apply SF_spec.next_ranking_valid with c; auto.
  intuition.
  destruct H1 as [r [??]].
  clear H0.
  hnf.
  right.
  exists r. split; auto.
  induction H1.
  apply SF_spec.next_ranking_eliminated; auto.
  rewrite Forall_forall; intros.
  apply H.
  rewrite Forall_forall in H0.
  apply H0; auto.
  apply SF_spec.next_ranking_valid with c; auto.
Qed.


Lemma selected_candidate_back :
  forall (candidate:Set) (elim elim':candidate -> Prop) b c,
    (forall x, elim x -> elim' x) ->
    selected_candidate _ elim' b c ->
    selected_candidate _ elim b c \/
    (exists x, selected_candidate _ elim b x /\ elim' x /\ ~elim x).
Proof.
  intros.
  destruct H0.
  destruct H1 as [r [??]].
  destruct (next_ranking_back candidate elim elim' b r c); auto.
  left. split; auto.
  eapply continuing_ballot_back; eauto.
  eauto.
  destruct H3 as [c' [r' [?[?[?[??]]]]]].
  right. exists c'.
  repeat split; auto.
  eapply continuing_ballot_back; eauto.
  exists r'; split; auto.
Qed.

Lemma count_votes_unique :
  forall (candidate:Set) (P:ballot candidate -> Prop) e n1 n2,
    count_votes _ P e n1 ->
    count_votes _ P e n2 ->
    n1 = n2.
Proof.
  intros until e. induction e; intros.
  * inv H. inv H0. auto.
  * inv H; inv H0; auto.
    elim H2; auto.
    elim H3; auto.
Qed.

Lemma count_votes_add :
  forall (candidate:Set) (P1 P2 P:ballot candidate -> Prop) e n1 n2,
    (forall b, P b <-> P1 b \/ P2 b) ->
    (forall b, P1 b -> P2 b -> False) ->
    count_votes _ P1 e n1 ->
    count_votes _ P2 e n2 ->
    count_votes _ P e (n1+n2).
Proof.
  intros. revert n1 n2 H1 H2.
  induction e; intros.
  * inv H1. inv H2. simpl. constructor.
  * inv H1; inv H2.
    elim (H0 a); auto.
    simpl.
    apply count_satisfies.
    apply H. auto.
    apply IHe; auto.
    replace (n1 + S n) with (S (n1 + n)) by omega.
    apply count_satisfies.
    apply H; auto.
    apply IHe; auto.
    apply count_not_satisfies.
    intro.
    rewrite H in H1.
    intuition.
    apply IHe; auto.
Qed.

Lemma elim_loser_list :
  forall
    (candidate:Set)
    (eliminated:candidate -> Prop)
    (losers : list candidate)
    (losers' : list candidate)
    (loser  : candidate)
    b,

    (In loser losers) ->
    (forall x, In x losers <-> x = loser \/ In x losers') ->
    (exists c, SF_spec.selected_candidate _ (update_eliminated _ eliminated loser) b c /\ In c losers') ->
    (exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers).
Proof.
  intros.
  destruct H1 as [c [??]].
  destruct (selected_candidate_back _ eliminated (update_eliminated _ eliminated loser) b c); auto.
  { unfold update_eliminated; auto. }
  exists c; split; auto.
  rewrite H0; auto.
  destruct H3 as [x [?[??]]].
  hnf in H4.
  destruct H4. contradiction.
  subst x.
  exists loser; auto.
Qed.

Lemma decompose_losers' :
 forall
    (candidate:Set)
    (eliminated:candidate -> Prop)
    (e:election candidate)
    (losers : list candidate)
    (loser  : candidate),
   NoDup losers ->
   In loser losers ->
   (forall l, In l losers -> viable_candidate _ eliminated e l) ->

   exists losers',
     NoDup losers' /\
     (forall l, In l losers' -> viable_candidate _ (update_eliminated _ eliminated loser) e l) /\
     length losers = S (length losers') /\
     (~In loser losers') /\
     (forall x, In x losers <-> x = loser \/ In x losers').
Proof.
  intros until losers. induction losers; intros. elim H0.
  inv H.
  simpl in H0. destruct H0.
  * subst a.
    exists losers.
    intuition.
    destruct (H1 loser); simpl; auto.
    split; auto.
    unfold update_eliminated.
    intuition.
    destruct (H1 l); simpl; auto.
    subst l; auto.
    destruct (H1 l); simpl; auto.
    simpl in H. intuition.
    simpl; auto.
  * destruct (IHlosers loser) as [losers' [?[?[?[??]]]]]; auto.
    intros; apply H1; simpl; auto.
    exists (a::losers'); intuition.
    constructor; auto.
    intro.
    apply H4.
    rewrite H7. auto.
    simpl in H8. destruct H8.
    subst l.
    destruct (H1 a); simpl; auto.
    split; auto.
    unfold update_eliminated; auto.
    intuition.
    subst a. contradiction.
    destruct (H1 l); simpl; auto.
    rewrite H7; auto.
    simpl. omega.
    simpl in H8.
    destruct H8.
    subst a.
    contradiction.
    contradiction.
    simpl in H8.
    rewrite H7 in H8.
    simpl. intuition.
    simpl; auto.
    subst x; auto.
    simpl in H9; simpl.
    rewrite H7.
    intuition.
Qed.


Lemma decompose_losers :
 forall
    (candidate:Set)
    (eliminated:candidate -> Prop)
    (e:election candidate)
    (losers : list candidate)
    (loser  : candidate)
    (loserCount : nat),
   NoDup losers ->
   In loser losers ->
   count_votes _ (fun b => exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers) e loserCount ->
   (forall l, In l losers -> viable_candidate _ eliminated e l) ->

   exists losers' loserCount',
     NoDup losers' /\
     count_votes _ (fun b => exists c, SF_spec.selected_candidate _ (update_eliminated _ eliminated loser) b c /\ In c losers') e loserCount' /\
     (forall l, In l losers' -> viable_candidate _ (update_eliminated _ eliminated loser) e l) /\
     loserCount' <= loserCount /\
     length losers = S (length losers') /\
     (~In loser losers') /\
     (forall x, In x losers <-> x = loser \/ In x losers').
Proof.
  intros.
  destruct (decompose_losers' candidate eliminated e losers loser)
           as [losers' [?[?[?[??]]]]]; auto.
  destruct (count_votes_total _
        (fun b : list (list candidate) =>
        exists c : candidate,
          selected_candidate candidate
            (update_eliminated candidate eliminated loser) b c /\
          In c losers') e) as [loserCount' ?].
  exists losers', loserCount'.
  intuition.
  eapply count_votes_monotone.
  2: eauto. 2: eauto.
  simpl.
  intro b.
  apply elim_loser_list; auto.
Qed.

Lemma sf_spec_optimization_backward :
  forall (candidate:Set)
         (len : nat)
         (eliminated eliminated':candidate -> Prop)
         (e:election candidate)
         (losers:list candidate)
         (loserCount:nat),

      len = length losers ->
      NoDup losers ->
      (forall l, In l losers -> viable_candidate _ eliminated e l) ->
      count_votes _ (fun b =>
                       exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers)
                  e loserCount ->
      (forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count) ->
      (exists c, ~In c losers /\ SF_spec.viable_candidate _ eliminated e c) ->
      (forall x, eliminated' x <-> eliminated x \/ In x losers) ->
      (forall x,
         SF_spec.winner candidate e eliminated' x ->
         SF_spec.winner candidate e eliminated x).
Proof.
  intros candidate n.
  induction n.
  * intros.
    eapply winner_elim_eq. 2: eauto.
    intros.
    rewrite H5.
    intuition.
    destruct losers. elim H9.
    inv H.
  * intros.
    destruct (classic (exists winner, majority _ eliminated e winner)).
    + destruct H7 as [winner ?].
      apply SF_spec.winner_now.
      replace x with winner; auto.
      inv H6.
      symmetry.
      eapply majority_unique.
      apply H8.
      eapply sf_opt_majority_forward; eauto.
      elim H8.
      exists winner.
      eapply sf_opt_majority_forward; eauto.
    + assert (exists loser, In loser losers /\ is_loser _ eliminated e loser).
      { destruct (sf_loser_exists _ e eliminated) as [loser ?].
        destruct losers. inversion H.
        exists c; auto.
        destruct (H1 c); simpl; auto.
        exists loser; split; auto.
        eapply sf_opt_loser_in_set; eauto.
        rewrite <- H. omega.
      }
      destruct H8 as [loser [??]].
      apply SF_spec.winner_elimination with loser; auto.
      destruct (decompose_losers _ eliminated e losers loser loserCount) as [losers' [loserCount' [?[?[?[?[?[??]]]]]]]]; auto.
      apply (IHn _ eliminated' e losers' loserCount'); auto.
      omega.
      eapply sf_opt_inductive_step; eauto.
      intros.
      apply le_lt_trans with loserCount; eauto.
      destruct H4 as [c [??]].
      exists c. split; auto.
      intro. apply H4.
      rewrite H16. auto.
      destruct H17; split; auto.
      unfold update_eliminated.
      intuition.
      subst c.
      contradiction.

      unfold update_eliminated.
      intro.
      rewrite H5.
      rewrite H16.
      intuition.
Qed.

Lemma sf_spec_optimization_forward :
  forall (candidate:Set)
         (len : nat)
         (eliminated eliminated':candidate -> Prop)
         (e:election candidate)
         (losers:list candidate)
         (loserCount:nat),

      len = length losers ->
      NoDup losers ->
      (forall l, In l losers -> viable_candidate _ eliminated e l) ->
      count_votes _ (fun b =>
                       exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers)
                  e loserCount ->
      (exists c, ~In c losers /\ SF_spec.viable_candidate _ eliminated e c) ->
      (forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count) ->
      (forall x, eliminated' x <-> eliminated x \/ In x losers) ->
      (forall x,
         SF_spec.winner candidate e eliminated x ->
         SF_spec.winner candidate e eliminated' x).
Proof.
  intros candidate n.
  induction n.
  * intros.
    eapply winner_elim_eq. 2: eauto.
    intros.
    rewrite H5.
    intuition.
    destruct losers. elim H9.
    inv H.
  * intros.
    inv H6.
      - apply SF_spec.winner_now.
        eapply sf_opt_majority_forward; eauto.
      - assert (In loser losers).
        { eapply sf_opt_loser_in_set; eauto.
          rewrite <- H. omega.
        }
        destruct (decompose_losers _ eliminated e losers loser loserCount) as [losers' [loserCounts' [?[?[?[?[?[??]]]]]]]]; auto.
        apply (IHn (SF_spec.update_eliminated _ eliminated loser) eliminated' e losers' loserCounts'); auto.
        rewrite H14 in H.
        injection H; auto.

        destruct H3 as [c [??]].
        exists c. split; auto.
        intro. apply H3.
        rewrite H16. auto.
        destruct H17; split; auto.
        unfold update_eliminated.
        intuition.
        subst c.
        contradiction.

        eapply sf_opt_inductive_step; eauto.
        intros.
        apply le_lt_trans with loserCount; eauto.
        unfold update_eliminated.
        intro.
        rewrite H5.
        rewrite H16.
        intuition.
Qed.

Theorem sf_spec_optimization :
  forall (candidate:Set)
         (eliminated eliminated':candidate -> Prop)
         (e:election candidate)
         (losers:list candidate)
         (loserCount:nat),

      count_votes _ (fun b =>
                       exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers)
                  e loserCount ->

      (exists c, ~In c losers /\ SF_spec.viable_candidate _ eliminated e c) ->

      (forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count) ->
      (forall x, eliminated' x <-> eliminated x \/ In x losers) ->
      (forall x,
         SF_spec.winner candidate e eliminated x <-> SF_spec.winner candidate e eliminated' x).
Proof.
  intros.
  assert (exists losers',
            NoDup losers' /\
            (forall l, In l losers' <-> viable_candidate _ eliminated e l /\ In l losers)).
  { clear. induction losers.
    * exists nil. simpl; intuition. constructor.
    * destruct IHlosers as [losers' [??]].
      destruct (classic (In a losers')).
      + exists losers'. intuition.
        rewrite H0 in H2; intuition.
        rewrite H0 in H2; simpl; intuition.
        rewrite H0. split; simpl in *; intuition.
        subst l. auto.
        rewrite H0 in H1.
        intuition.
      + destruct (classic (viable_candidate _ eliminated e a)).
        - exists (a::losers').
          split. constructor; auto.
          simpl; intuition subst; auto.
          rewrite H0 in H4; intuition.
          rewrite H0 in H4; intuition.
          rewrite H0; intuition.
        - exists losers'.
          simpl; intuition subst; auto.
          rewrite H0 in H3; intuition.
          rewrite H0 in H3; intuition.
          rewrite H0; intuition.
          rewrite H0; intuition.
  }
  destruct H3 as [losers' [??]].
  set (eliminated'' c := eliminated c \/ In c losers').

  cut (winner _ e eliminated x <-> winner _  e eliminated'' x).
  { intros. rewrite H5.
    cut (forall c, SF_spec.participates _ c e -> (eliminated'' c <-> eliminated' c)).
    intros. split; apply winner_elim_eq; auto.
    intros. symmetry; apply H6; auto.
    intros. unfold eliminated''.
    rewrite H2.
    intuition.
    right.
    rewrite H4 in H9. intuition.
    destruct (classic (eliminated c)); auto.
    right.
    rewrite H4. split; auto.
    split; auto.
  }

  assert (Hviable : 
   forall l : candidate,
   In l losers' -> viable_candidate candidate eliminated e l).
  { intros. rewrite H4 in H5. intuition. }

  assert (Hcount :    count_votes candidate
     (fun b : list (list candidate) =>
      exists c : candidate,
        selected_candidate candidate eliminated b c /\ In c losers') e
     loserCount).
  { revert H. apply count_eq.
    intuition.
    destruct H5 as [c [??]]. exists c; split; auto.
    rewrite H4; auto. split; auto.
    split.
    eapply selected_candidate_not_eliminated; eauto.
    destruct H5.
    destruct H7 as [r [??]].
    hnf; eauto.
    exists b; split; auto.
    exists r; split; auto.
    eapply next_ranking_in_ballot; eauto.
    destruct H5 as [c [??]].
    exists c; split; auto.
    rewrite H4 in H6. intuition.
  }
  assert (Hnonloser :    exists c : candidate,
     ~ In c losers' /\ viable_candidate candidate eliminated e c).
  { destruct H0 as [c [??]].
    exists c; split; auto.
    intro.
    apply H0.
    rewrite H4 in H6. intuition.
  }
  assert (Hdominated : forall (c : candidate) (count : nat),
   ~ In c losers' ->
   viable_candidate candidate eliminated e c ->
   first_choices candidate eliminated c e count -> loserCount < count).
  { intros.
    eapply H1; eauto.
    intro. apply H5.
    apply H4. split; auto.
  }
  assert (Helim :
     forall x0 : candidate, eliminated'' x0 <-> eliminated x0 \/ In x0 losers').
  { unfold eliminated''. intuition. }

  split.
  apply sf_spec_optimization_forward with (length losers') losers' loserCount; auto.
  apply sf_spec_optimization_backward with (length losers') losers' loserCount; auto.
Qed.
