Require Import Coq.Lists.List.
Require Import Classical.
Require Import RelDec.
Require Import Coq.Lists.List.
Require Import Sorting.
Require Import Orders.
Require Import Compare_dec.
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Arith.Wf_nat.
Require Import Recdef.
Import ListNotations.


Section election_spec.
  (** For this section, we hold the set of candidates abstract,
      and define ballots and some properties of ballots irrespective
      of how candidates are defined.
   *)
  Variable candidate:Set.
 
  Let ballot := candidate.
  Let election := list ballot.

  (** Does this candidate participate in that election? *)
  Definition participates candidate (election : election) : Prop := 
  In candidate election.

  (** How many votes  *)
  Inductive voteCount candidate : election -> N -> Prop :=
  | voteCountCandidate : forall countCandidate election' ct,
      candidate = countCandidate ->
      voteCount candidate election' ct ->
      voteCount candidate (countCandidate :: election') (ct + 1)
  | voteCountOther : forall countCandidate election' ct,
      candidate <> countCandidate ->
      voteCount candidate election' ct ->
      voteCount candidate (countCandidate :: election') ct
  | voteCountNil : voteCount candidate nil 0.
  
  (** Does this candidate hold a plurality in that election? *)
  Definition hasPlurality winningCandidate (election : election) : Prop :=
    forall candidate candidateCount winningCandidateCount,
      candidate <> winningCandidate ->
      voteCount candidate election candidateCount ->
      voteCount winningCandidate election winningCandidateCount ->
      N.gt winningCandidateCount candidateCount.

End election_spec.

Section candidate.

  Local Open Scope N_scope.
  
  Variable candidate : Set.
  Variable reldec_candidate : RelDec (@eq candidate).

  Let ballot := candidate.
  Let election := list ballot.

  Definition getParticipants all :=
    fold_right (fun cand result => if existsb (eq_dec cand) result
                                then result
                                else cand :: result) nil all.
  
  Definition countParticipant election toCount  :=
    fold_right (fun candidate total => if eq_dec toCount candidate then 1 + total else total)
               0 election.

  Definition addTallies participants election :=
    map (fun participant => (participant, countParticipant election participant)) participants.

  Fixpoint getMax' (pairs : list (candidate * N)) (first : (candidate * N * bool)) : (candidate * N * bool) :=
    match pairs with
    | (cand, ct) :: t => match (getMax' t first) with (retcd, retn, retunique) =>
                                           if N.eqb ct retn
                                           then (retcd, retn, false)
                                           else
                                             if (N.leb ct retn)
                                             then (retcd, retn, retunique)
                                             else (cand, ct, true)
                        end
    | [] => first
    end.

  Definition getMaxCand pairs : option candidate :=
    match pairs with
    | [] => None
    | h :: t => match (getMax' pairs ((fst h), 0, false)) with
               | (_, _, false) => None
               | (cd, _, _) => Some cd
               end
    end.

  Definition runPluralityElection election :=
    let allCandidates := getParticipants election in
    let tally := addTallies allCandidates election in
    getMaxCand tally.

End candidate.

Section cand.

  Variable candidate : Set.
  Variable reldec_candidate : RelDec (@Logic.eq candidate).
  Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.
  
  Local Open Scope N_scope.

  Lemma existb_false_forall : forall A l b, (@existsb A b l = false) <-> (forall i, In i l -> b i = false).
    intros A l b; split.
    - induction l.
      + simpl. intuition.
      + simpl. intros. 
        rewrite Bool.orb_false_iff in *.
        intuition; subst; auto.
    - induction l.
      + simpl. intuition.
      + intuition. simpl. rewrite Bool.orb_false_iff. intuition.
  Qed.
  
  Lemma getParticipantsCorrect :
    forall cd election, In cd (getParticipants candidate reldec_candidate election) <->
                   participates candidate cd election.
  Proof.
    split.
    - intros H.
      induction election.
      + auto.
      + simpl in *.
        unfold getParticipants in H.
        simpl in *. destruct (existsb (eq_dec a)
              (fold_right
                 (fun (cand : candidate) (result : list candidate) =>
                    if existsb (eq_dec cand) result then result else cand :: result) 
                 [] election)) eqn:?.
        * rewrite existsb_exists in *. destruct Heqb.
          intuition.
        * rewrite existb_false_forall in Heqb.
          { edestruct (rel_dec_p a cd).
            - auto.
            - right.
              apply IHelection. unfold getParticipants. inversion H. intuition. auto.
          }
    - intros.
      induction election.
      + auto.
      + simpl. destruct (existsb (eq_dec a) (getParticipants candidate reldec_candidate election)) eqn:?.
        rewrite existsb_exists in Heqb. destruct Heqb. intuition. apply reldec_correct_candidate in H2. subst.
        inversion H; subst; clear H; auto. simpl.
        destruct (rel_dec_p a cd). auto. inversion H; auto.
  Qed.

  Lemma fold_right_cons : forall B A (f:B -> A -> A) (l:list B) b a0, fold_right f a0 (b::l) = f b (fold_right f a0 l).
  Proof.
    intros; reflexivity.
  Defined.
  
  
  Theorem count_correct : forall election cand count,
      countParticipant candidate reldec_candidate election cand = count <-> voteCount candidate cand election count.
  Proof.
    intros election. split. revert count.
    - induction election; intros.
      + simpl in H. subst. constructor.
      + unfold countParticipant in H. rewrite fold_right_cons in H.
        destruct (eq_dec cand a) eqn:?.
        * subst. rewrite N.add_comm.
          { constructor.
            - apply reldec_correct_candidate in Heqb. auto.
            - apply IHelection. unfold countParticipant. auto.
          }
        * apply neg_rel_dec_correct in Heqb.
          { constructor.
            - auto.
            - apply IHelection. subst. auto.
          }
    - intros. generalize dependent count. induction election; intros.
      + simpl. inversion H. auto.
      + unfold countParticipant. rewrite fold_right_cons.
        destruct (eq_dec cand a) eqn:?.
        * apply reldec_correct_candidate in Heqb.
          subst.
          { inversion H.
            - subst. rewrite (N.add_comm ct). f_equal.
              apply IHelection. auto.
            - intuition.
          }
        * apply neg_rel_dec_correct in Heqb.
          inversion H; intuition.
  Qed.

  Lemma addTallies_correct : forall participants election c n,
      In (c, n) (addTallies candidate reldec_candidate participants election) ->
      voteCount candidate c election n.
  Proof.
    unfold addTallies.
    intros. apply in_map_iff in H. destruct H.  destruct H.
    inversion H. subst. clear H.
    remember (countParticipant candidate reldec_candidate election c). symmetry in Heqn.
    apply count_correct in Heqn. auto.
  Qed.
    
  Theorem getMax'_correct : forall (prs : list (candidate * N)) fst resCand resCt resUnique,
      getMax' candidate prs fst = (resCand, resCt, resUnique) ->
      forall cd n, In (cd, n) prs -> n <= resCt.
  Proof.
    intros prs.
    induction prs; intros.
    - inversion H0.
    - simpl in H0.
      destruct H0.
      + subst.  simpl in H.
        destruct (getMax' candidate prs fst) eqn:?. destruct p.
        destruct (n =? n0) eqn:?.
        * apply N.eqb_eq in Heqb0. subst.
          inversion H; subst; clear H. apply N.le_refl.
        * { destruct (n <=? n0) eqn:?.
            - inversion H; subst; clear H. apply N.leb_le in Heqb1. auto.
            - inversion H; subst; clear H. apply N.le_refl.
          }
      + simpl in H. destruct a. destruct (getMax' candidate prs fst) eqn:?.
        destruct p. destruct (n0=? n1) eqn:?.
        * inversion H. subst; clear H. apply N.eqb_eq in Heqb0. subst. eapply IHprs in Heqp.
          eauto. apply H0.
        * {destruct (n0 <=? n1) eqn:?; inversion H; subst; clear H.
           - eapply IHprs in Heqp. eauto. apply H0.
           - eapply IHprs in Heqp. instantiate (1 := n) in Heqp.
             apply N.eqb_neq in Heqb0.
             apply N.leb_gt in Heqb1.
             eapply N.le_lt_trans in Heqp; eauto.
             apply N.lt_le_incl. auto. eauto.
          }
  Qed.

   Theorem getMax'_unique : forall (prs : list (candidate * N)) fst resCand resCt,
      getMax' candidate prs fst = (resCand, resCt, true) ->
      In (resCand, resCt) prs -> exists f b, prs = f ++ (resCand, resCt) :: b /\ ~ In resCt (map (@snd candidate _) f) /\ ~ In resCt (map (@snd candidate _) b).
   Proof.
     intros prs.
     induction prs; intros.
     - inversion H0.
     - simpl in *. destruct a. destruct ( getMax' candidate prs fst) eqn:?.
       destruct p. destruct (n=? n0) eqn:?.
       + inversion H.
       + destruct (n <=? n0) eqn:?.
         * inversion H; subst; clear H.
           { destruct H0.
             - inversion H; subst; clear H.
               apply N.eqb_neq in Heqb0. intuition.
             - apply IHprs in Heqp; auto.
               destruct Heqp. destruct H0.
               destruct H0. destruct H1.
               exists ((c,n) :: x).
               exists x0.
               split.
               + simpl. f_equal. auto.
               + split.
                 *  simpl. intro.
                    { destruct H3.
                      - apply N.eqb_neq in Heqb0; intuition.
                      - auto.
                    }
                 * auto.
           }
         * inversion H; subst; clear H.
           apply N.leb_gt in Heqb1. clear H0.
           exists nil. exists prs. split. auto.
           split. auto. intro. eapply in_map_iff in H.
           destruct H. destruct x. destruct H.
           simpl in H. subst.
           eapply getMax'_correct in H0; eauto.
           rewrite <- N.nlt_ge in H0. intuition.
   Qed.

   Lemma get_participants_nodup : forall l, NoDup (getParticipants candidate reldec_candidate l).
   Proof.
     induction l; intros.
     - simpl. constructor.
     - simpl. destruct (existsb (eq_dec a) (getParticipants candidate reldec_candidate l)) eqn:?.
       + auto.
       + rewrite existb_false_forall in Heqb. constructor.
         * intro. specialize (Heqb a). intuition.
           apply neg_rel_dec_correct in H0. intuition. 
         * auto.
   Qed.

   Lemma addTalliesNoDup : forall participants election,
       NoDup participants -> NoDup (map (@fst candidate _) (addTallies candidate reldec_candidate participants election)).
   Proof.
     induction participants; intros.
     - simpl. auto.
     - simpl. inversion H.
       subst. clear H.
       constructor.
       + { clear H3  IHparticipants.
           induction participants.
           - simpl. auto.
           - simpl. intro.
             destruct H.
             + subst. apply H2. simpl. auto.
             + apply IHparticipants. intro. apply H2.
               right. auto. auto.
         }
       + apply IHparticipants. auto.
   Qed.

(*   
  Theorem getMaxCand_correct : forall cand prs election mx,
      (forall cnd cnt, In (cnd, cnt) prs -> voteCount candidate cnd election cnt) ->
      (getMax' candidate mx = Some cand <-> hasPlurality candidate cand election).
  Proof.
    intros cand prs election H.
    split; intros.
    - induction prs.
      + simpl in *; congruence.
      + simpl in H0. 
  *)  
       
                               
   Lemma in_ne_in_other : forall A (l : list A) i1 i2,
       In i1 l ->
       In i2 l ->
       i1 <> i2 ->
       exists s f, l = s ++ i1 :: f /\ (In i2 s \/ In i2 f).
   Proof.
     induction l; intros.
     - inversion H.
     - simpl in *. destruct H, H0; subst.
       + intuition. 
       + exists nil. exists l. intuition.
       + apply in_split in H. destruct H. destruct H. subst.
         exists (i2 :: x). exists x0. intuition.
       + specialize (IHl i1 i2 H H0 H1).
         destruct IHl. destruct H2. destruct H2.
         subst.
         exists (a::x). exists x0. split. auto.
         clear H.
         apply in_app_or in H0.
         destruct H0. left. simpl. auto.
         right. simpl in H. intuition.
   Qed.
   
   Lemma getMax'_false_in : forall prs c winner n,
       getMax' candidate prs (c, 0, false) = (winner, n, true) ->
       In (winner, n) prs.
   Proof.
     induction prs; intros.
     - simpl in H. congruence.
     - simpl in H. destruct a. destruct (getMax' candidate prs (c, 0, false)) eqn:?.
       destruct p.
       destruct (n0 =? n1) eqn:?.
       +  congruence.
       +  destruct (n0 <=? n1) eqn:?.
          *  inversion H; subst; clear H.
             apply IHprs in Heqp. right. auto.
          * inversion H; subst; clear H.
            left. auto.
   Qed.
   
   Ltac inv H := inversion H; subst; clear H.
   Lemma voteCount_unique :
     forall cand election ct1 ct2,
       voteCount candidate cand election ct1 ->
       voteCount candidate cand election ct2 ->
       ct1 = ct2.
   Proof.
     induction election; intros.
     - inversion H. inversion H0. auto.
     - inv H; inv H0.
       + rewrite N.add_comm. rewrite (N.add_comm ct0). f_equal. apply IHelection; auto.
       + intuition.
       + intuition.
       + apply IHelection; auto.
   Qed.

   Lemma participates_in_count : forall participants election cand count,
       In cand participants ->
       voteCount candidate cand election count ->
       In (cand, count) (addTallies candidate reldec_candidate participants election).
   Proof.
     induction participants; intros.
     - inversion H.
     - simpl in H. destruct H.
       + subst. simpl. left. f_equal.
         apply count_correct. auto.
       + simpl. right. apply IHparticipants; auto.
   Qed.

   Lemma split_l_map : forall A B (l : list (A * B)),
       fst (split l) = map (@fst A B) l.
   Proof.
     induction l; intros.
     auto.
     simpl in *. destruct a. simpl in *.
     destruct (split l) eqn:?. simpl in *. f_equal.
     auto.
     Qed.

      Lemma split_r_map : forall A B (l : list (A * B)),
       snd (split l) = map (@snd A B) l.
   Proof.
     induction l; intros.
     auto.
     simpl in *. destruct a. simpl in *.
     destruct (split l) eqn:?. simpl in *. f_equal.
     auto.
     Qed.

   

   Lemma noDup_fst_noDup : forall A B (l : list (A*B)),
       NoDup (map (@fst A B) l) -> NoDup l.
   Proof.
     induction l; intros.
     - constructor.
     - inv H.  destruct a.
       simpl in *. constructor.
       + intuition.
         apply H2. apply in_split_l in H. simpl in H.
         rewrite <- split_l_map. auto.
       + intuition.
   Qed.

   Lemma noDup_same_split:
     forall A (i: A) h1 t1 h2 t2,
       NoDup (h1 ++ i :: t1) ->
       h1 ++ i :: t1 = h2 ++ i :: t2 ->
       h1 = h2 /\ t1 = t2.
   Proof.
     intros. assert (NoDup (h2 ++ i :: t2)). rewrite H0 in *. auto.
     generalize dependent h2. generalize dependent t1. revert t2.
     induction h1; intros.
     - simpl in *.
       induction h2.
       +  simpl in *. inv H0. auto.
       +  simpl in *. 
          inv H1. inv H0. clear - H. inv H. exfalso. apply H2.
          apply in_app_iff. right. simpl. auto.
     - simpl in *. inv H0.
       inv H.
       induction h2.
       + inv H3.  exfalso. apply H4. apply in_app_iff. right. simpl; auto.
       + inv H3. inv H1. apply IHh1 in H2; auto. intuition. subst. auto.
   Qed.
             

Lemma not_participant_no_votes : forall cd election,
            ~ participates candidate cd election -> voteCount candidate cd election 0.
          Proof.
            induction election; intros.
            - constructor.
            - simpl in *. intuition.
              apply voteCountOther; auto.
          Qed.

              Lemma voteCount_decidable : forall cd election,
                  exists n, voteCount candidate cd election n.
              Proof.
                induction election; intros. exists 0. constructor.
                destruct IHelection.
                destruct (rel_dec_p cd a). subst. 
                exists (x + 1). constructor; auto.
                exists x. constructor; auto.
              Qed.
              
          
          Lemma participant_nonzero_votes : forall cd election,
              participates candidate cd election -> exists n, voteCount candidate cd election (n + 1).
          Proof.
            induction election; intros.
            - inversion H.
            - simpl in H. destruct H.
              + subst.
                destruct (voteCount_decidable cd election); auto.
                exists x. constructor; auto.
              + intuition. destruct H0.
                destruct (rel_dec_p cd a).
                subst. exists (x + 1 ). constructor; auto.
                exists x. apply voteCountOther; auto.
          Qed.

                      Lemma in_tally_participant : forall cd ct election participants,
                In (cd, ct) (addTallies candidate reldec_candidate participants election) ->
                In cd participants.
            Proof.
              induction participants; intros.
              - simpl in *. auto.
              - simpl in *. destruct H.
                + inv H. auto.
                + intuition.
            Qed.

                      Lemma n_succ_gt_O : forall (n:N),   0 < N.succ n.
            induction n using N.peano_ind.
            rewrite <- N.compare_lt_iff. auto.
            rewrite  <- N.compare_lt_iff in *. simpl in *. destruct (N.succ n). congruence.
            auto.
                      Qed.
   
   Theorem pluralityCorrect :
     forall election winner,
       runPluralityElection candidate reldec_candidate election = Some winner ->
       hasPlurality candidate winner election.
   Proof.
     unfold runPluralityElection.  intros.
     -  unfold getMaxCand in H. destruct (addTallies candidate reldec_candidate (getParticipants candidate reldec_candidate election) election) eqn:?; try congruence.
        destruct (getMax' candidate (p :: l) (fst p, 0, false)) eqn:?.
        destruct p0. destruct b eqn:?; inversion H; subst; clear H.
        pose proof getMax'_correct _ _ _ _ _ Heqp0.
        unfold hasPlurality. intros candidate0 candidateCount winningCandidateCount H0 H1 H2.
        pose proof addTallies_correct (getParticipants candidate reldec_candidate election) election.
        
        pose proof getMax'_false_in _ _ _ _ Heqp0.
        rewrite Heql in *.
        pose proof (H3 _ _ H4).
        
        eapply voteCount_unique in H2; eauto. subst.
        edestruct (in_dec (rel_dec_p) candidate0 (getParticipants candidate reldec_candidate election)).
        + pose proof (participates_in_count _ _ _ _ i H1).
          rewrite Heql in *. apply H in H2.
          assert (candidateCount <> winningCandidateCount).
          { 
            apply getMax'_unique in Heqp0; auto.
            destruct Heqp0.
            destruct H6. destruct H6. intuition. subst.
            eapply participates_in_count in H1; eauto.
            rewrite Heql in *.
            pose proof (in_ne_in_other _ (p::l) _  _ H4 H1).
            destruct H7.
            - intro. inv H7; auto.
            - destruct H7. 
              + rewrite H6 in *.
                assert (NoDup (p :: l)).
                { rewrite H6 in *. rewrite <- Heql in *.
                  apply noDup_fst_noDup. 
                  apply addTalliesNoDup.
                  apply get_participants_nodup. }
                rewrite H6 in *. destruct H7.
                apply noDup_same_split in H7; auto. destruct H7. subst x x0.
                intuition.
                * clear - H9 H7. apply H9; clear H9. apply in_split_r in H7.
                  rewrite <- split_r_map. simpl in *. auto.
                * clear - H10 H7. apply H10; clear H10. apply in_split_r in H7.
                  rewrite <- split_r_map. simpl in *. auto.
          }
          rewrite N.gt_lt_iff.
          apply N.le_neq; auto.
        + assert (~participates candidate candidate0 election).
          { intro. apply n. clear - H2. apply getParticipantsCorrect in H2. auto. }
          apply not_participant_no_votes in H2.
          eapply (voteCount_unique _ _ _ _ H1) in H2. subst.
          assert (participates candidate winner election).
          { rewrite <- Heql in *. apply in_tally_participant in H4. apply getParticipantsCorrect.
            auto. }
          
          apply participant_nonzero_votes in H2. destruct H2. 
          apply (voteCount_unique _ _ _ _ H5) in H2.
          rewrite N.gt_lt_iff.
          subst.
          replace (x + 1) with (N.succ x).
          apply n_succ_gt_O.
          rewrite N.add_1_r. auto.
Qed.
