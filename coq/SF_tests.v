Require Import SF_imp.
Require Import RelDec.
Require Import List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Import ListNotations.

Local Open Scope N.

Parameter T : Set.

Parameter eqb_t : T -> T -> bool.

Parameter reldec_t : @RelDec T eq.

Definition option_eq {A} (eq : A -> A -> bool) (a b : option A)  : bool :=
match a,b with
| Some a', Some b' => eq a' b'
| None, None => true
| _, _ => false
end.  

Definition option_eq_t := option_eq eqb_t.

Definition prop_drop_none_keeps (l : list (option T)) (i : T) : bool :=
  Bool.eqb (existsb (option_eq_t (Some i)) l) (existsb (eqb_t i) (drop_none l)).

Definition prop_next_ranking_contains rec bal :=
match (next_ranking T _ rec bal) with
| Some (c, _) => existsb (existsb (eqb_t c)) bal
| _ => true
end.

Definition prop_next_ranking_not_eliminated rec bal :=
match (next_ranking T _ rec bal) with
| Some (c, _) => negb (eliminated T _ rec c)
| _ => true
end.


Fixpoint is_overvote (rec : record T) (b : ballot T) : bool :=
match b with
| [] :: t => is_overvote rec t
| (h :: l) :: t => if (forallb (eq_dec h) l) then 
                     if false (*(eliminated T _ rec h)*) then is_overvote rec t else false
                   else true
| [] => false
end.

Definition prop_next_ranking_not_overvote rec bal :=
match (next_ranking T _ rec bal) with
| Some (c, _) => negb (is_overvote rec bal)
| _ => true
end.

Fixpoint get_first  (r : list (T * N)) (c : T) : N :=
match r with 
| (c', n) :: t => if (eq_dec c c') then n else get_first t c
| nil => 0%N
end.

Definition prop_increment_get c r := 
N.eqb ((get_first r c) + 1) (get_first (increment T _ r c) c).

Fixpoint count_candidate (l : list (option T)) (c : T) := 
match l with
| Some c' :: t => if (eq_dec c c') then 1 + (count_candidate t c) else count_candidate t c
| h :: t => count_candidate t c
| nil => 0
end.

Definition prop_count_tabulate'' (l : list (option T)) (c : T) :=
N.eqb (count_candidate l c) (get_first (tabulate' T _ l) c).

Definition pair_eq {A B} (eq_a : A -> A -> bool) (eq_b : B -> B -> bool)
           (a b : (A * B))  : bool :=
match a,b with
| (a1, a2), (b1, b2) => andb (eq_a a1 b1) (eq_b a2 b2)
end.  

Definition pair_eq_t_n (a b : (T * N)) : bool := 
  pair_eq eq_dec N.eqb a b.

Definition prop_option_split (l : list (option (T * N))) c n :=
let res := option_split l in
if (existsb (option_eq pair_eq_t_n (Some (c, n))) l)
then (andb (existsb (option_eq eq_dec (Some c)) (fst res)) (existsb (option_eq N.eqb (Some n)) (snd res)))
else true.

Definition prop_get_bottom_votes_correct (v : list (T * N)) c n :=
match v with
| (c', n') :: t => 
  if
    (andb (existsb (pair_eq_t_n (c, n)) v) (N.eqb n n'))
  then
    (existsb (eq_dec c) (get_bottom_votes T v))
  else true
| _ => true
end.
