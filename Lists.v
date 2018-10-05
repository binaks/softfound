Require Export Induction.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  simpl. reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => 1 + (length t)
  end.

Fixpoint app (l_1 l_2 : natlist) : natlist :=
  match l_1 with
  | nil => l_2
  | h :: t => h :: (app t l_2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_appl: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd_1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd_2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_t1: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match beq_nat h 0 with
              | true => nonzeros t
              | false => h :: (nonzeros t)
              end
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match evenb h with
              | true => oddmembers t
              | false => h :: (oddmembers t)
              end
end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddnumbers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddnumbers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l_1 l_2 : natlist) : natlist :=
  match l_1 with
  | nil => l_2
  | h :: t => match l_2 with
              | nil => l_1
              | h' :: t' => h :: h' :: (alternate t t')
              end
end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match beq_nat h v with
              | true => S (count v t)
              | false => count v t
              end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum_1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match count v s with
  | 0 => false
  | _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => (remove_all v  t)
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s_1:bag) (s_2:bag) : bool :=
  match s_1 with
  | nil => true
  | h :: t => match member h s_2 with
              | true => subset t (remove_one h s_2)
              | false => false
              end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - reflexivity.
  - reflexivity. Qed.

Theorem app_assoc : forall l_1 l_2 l_3 : natlist,
  (l_1 ++ l_2) ++ l_3 = l_1 ++ (l_2 ++ l_3).
Proof.
  intros l_1 l_2 l_3.
  induction l_1 as [| n l_1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => (rev t) ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l_1 l_2 : natlist,
  length (l_1 ++ l_2) = (length l_1) + (length l_2).
Proof.
  intros l_1 l_2. induction l_1 as [| n l_1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl1'].
  - reflexivity.
  - simpl. rewrite -> app_length, plus_comm.
    rewrite -> IHl1'. simpl. reflexivity. Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> IHl'.
    reflexivity.
  Qed.

Theorem rev_app_distr : forall l_1 l_2 : natlist,
  rev (l_1 ++ l_2) = rev l_2 ++ rev l_1.
Proof.
  intros l_1 l_2.
  induction l_1 as [| n l_1' IHl1'].
  - simpl.
    rewrite -> app_nil_r.
    reflexivity.
  - simpl.
    rewrite -> IHl1'.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. 
    rewrite -> rev_app_distr.
    simpl.
    rewrite -> IHl'.
    reflexivity.
  Qed.

Theorem app_assoc4 : forall l_1 l_2 l_3 l_4 : natlist,
  l_1 ++ (l_2 ++ (l_3 ++ l_4)) = ((l_1 ++ l_2) ++ l_3) ++ l_4.
Proof.
  intros l_1 l_2 l_3 l_4.
  rewrite -> app_assoc, app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l_1 l_2 : natlist,
  nonzeros (l_1 ++ l_2) = (nonzeros l_1) ++ (nonzeros l_2).
Proof.
  intros l_1 l_2.
  induction l_1 as [|n l_1' IHl1'].
  - reflexivity.
  - simpl.
    rewrite -> IHl1'.
    destruct beq_nat.
    + reflexivity.
    + reflexivity.
  Qed.

Definition beq_natlist (l_1 l_2 : natlist) : bool :=
  (subset l_1 l_2) && (subset l_2 l_1).

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.








