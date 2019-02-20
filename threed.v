(** Copyright (c) 2015-2019 George M. Van Treeck.
    Rights granted under the Creative Commons
    Attribution License.
    This software uses The Coq Proof Assistance,
    Copyright (c) 1999-2019  The Coq Development Team
    Rights granted under
    GNU Lesser General Public License Version 2.1. *)

Require Import Arith Omega Bool List.

Section Symmetric.
(** This section contains definitions, theorem, and
   proof that an ordered and symmetric geometric is
   cyclic set. *)

(** Generic element type for a set (list). *)
Variable A: Type.
(** Indexes into to sets. *)
Variables i j k: nat.
(** Length of list *)
Variable n: nat.
(** The list to be permuted. *)
Variables x : list A.
(** default value returned when no set member found. *)
Variable default_element: A.
(** Definition of an empty set. *)
Definition empty_list : list A := nil.

(** Returns the element at position i in the list. *)
Fixpoint mem (i:nat) (l:list A) {struct l} : A :=
    match i, l with
    | O, _ => default_element
    | S m, nil => default_element
    | S m, h::t => mem m t
    end.

(** Definition of a successor. The underlying definition
   is not used in the proof of the symmetric_is_cyclic theorem. *)
Definition successor(i: nat) (l: list A) : A := mem (i+1) l.

(** Definition of a predecessor. The underlying definition
   is not used in the proof of the symmetric_is_cyclic theorem. *)
Definition predecessor (i: nat) (l: list A) : A := mem (i-1) l.

(** A declarative (opaque) definiton of a symmetric Geometry *)
Hypothesis symmetric_geometry :
  successor i x = mem j x /\ predecessor j x = mem i x.

(** A symmetric and ordered geometry is cyclic set. *)
Theorem ordered_symmetric_is_cyclic :
   i = n /\ j = 1 ->
   successor(n) x = mem 1 x /\ predecessor 1 x = mem n x.
Proof.
  decompose [and] symmetric_geometry.
  intros. decompose [and] H1. split.
  rewrite <- H2. rewrite <- H3. exact H.
  rewrite <- H2. rewrite <- H3. exact H0.
Qed.

End Symmetric.

Section CyclicOrder.

(** From the theorem ordered_symmetric_is cyclic, an
   ordered and symmetric set is a cyclic set, which implies
   the successors and predecessors are cycic.*)

(** Assumes 1 <= m <= setsize. *)

(** Cyclic successor. *)
Definition cyclic_successor (m setsize: nat) : nat :=
  if beq_nat m setsize then 1 else S m.
(** Cyclic predecssor *)
Definition cyclic_predecessor (m setsize: nat) : nat :=
  if beq_nat m 1 then setsize else pred m.

(** Forall n = setsize, n + 1 := 1. *)
Lemma n_plus_one_is_one : forall n setsize: nat,
  n = setsize -> cyclic_successor n setsize = 1.
Proof.
  intros. unfold cyclic_successor.
  assert (eq_beq_true :
      n = setsize -> beq_nat n setsize = true).
    intros. apply beq_nat_true_iff. exact H0.
  rewrite -> eq_beq_true. reflexivity. exact H.
Qed.

(** Forall m = 1, m - 1 := 1. *)
Lemma one_minus_one_is_one : forall m setsize: nat,
  m = 1 -> cyclic_predecessor m setsize = setsize.
Proof.
  intros. unfold cyclic_predecessor.
  assert (eq_beq_true :
      m = 1 -> beq_nat m 1 = true).
    intros. apply beq_nat_true_iff. exact H0.
  rewrite -> eq_beq_true. reflexivity. exact H.
Qed.


(** Generate a list of "setsize" number of cyclic successor
    indexes, starting at position "start" *)
Fixpoint cyclic_successor_permutation
    (start len setsize: nat) {struct len} : list nat :=
  match len with
    | 0 => nil
    | S x => start ::
      cyclic_successor_permutation
          (cyclic_successor start setsize) x setsize
  end.

(** Generate a list of "setize" number of cyclic predecessor
    indexes, starting at position "start" *)
Fixpoint cyclic_predecessor_permutation (start len setsize: nat)
    {struct len} : list nat :=
  match len with
    | 0 => nil
    | S x => start ::
      cyclic_predecessor_permutation
          (cyclic_predecessor start setsize) x setsize
  end.

(** Generate a pair of cyclic permutation lists, one a
    successor list and the other a predecessor list. *)
Fixpoint cyclic_permutation_pair (start len setsize: nat)
    {struct len} : list (list nat) :=
      (cyclic_successor_permutation start len setsize) ::
      (cyclic_predecessor_permutation start len setsize) :: nil.

(** Generate a list containing "count" number of cyclic
    permutation pairs *)
Fixpoint cyclic_permutations (count setsize: nat)
    (l':list (list nat)) {struct count} : list (list nat) :=
  match count with
    | 0 => nil
    | S count0 => cyclic_permutations
        count0 setsize
            (cyclic_permutation_pair count0 setsize setsize)
            ++ l'
   end.

(** Generate a list of all cyclic permutations. *)
Definition all_cyclic_permutations (setsize: nat) :
  list (list nat) :=
    cyclic_permutations (S setsize) setsize ((nil)::nil).

(** Show all permutations where the number of dimensions equals 1. *)
Eval compute in all_cyclic_permutations 1.
(** Outputs the following:
     = (1 :: nil) :: (1 :: nil) :: nil :: nil
*)

(** Show all permutations where the number of dimensions equals 2. *)
Eval compute in all_cyclic_permutations 2.
(** Outputs the following:
= (1 :: 2 :: nil) :: (1 :: 2 :: nil) ::
  (2 :: 1 :: nil) :: (2 :: 1 :: nil) :: nil :: nil
*)

(** Show all permutations where the number of dimensions equals 3. *)
Eval compute in all_cyclic_permutations 3.
(** Outputs the following:
     = (1 :: 2 :: 3 :: nil) :: (1 :: 3 :: 2 :: nil)
    :: (2 :: 3 :: 1 :: nil) :: (2 :: 1 :: 3 :: nil)
    :: (3 :: 1 :: 2 :: nil) :: (3 :: 2 :: 1 :: nil) :: nil :: nil
*)

(** NOTE that for the number dimensions, setsize in {1, 2, 3},
   all possible permutations were generated, because every
   dimension is cyclically adjacent (successor or predecessor)
   to every other dimension.

   Next, it will be proved by enumerating each case that for
   the number of dimensions, setsize in {1, 2, 3}, every
   dimension is cyclically adjacent to every other dimension. *)
Definition adjacent (m n setsize: nat) : Prop :=
  cyclic_successor m setsize = n \/
  cyclic_predecessor m setsize = n.

Lemma adj111 : adjacent 1 1 1. Proof. right; reflexivity. Qed.
Lemma adj122 : adjacent 1 2 2. Proof. right; reflexivity. Qed.
Lemma adj212 : adjacent 2 1 2. Proof. left; reflexivity. Qed.
Lemma adj123 : adjacent 1 2 3. Proof. left; reflexivity. Qed.
Lemma adj133 : adjacent 1 3 3. Proof. right; reflexivity. Qed.
Lemma adj213 : adjacent 2 1 3. Proof. right; reflexivity. Qed.
Lemma adj233 : adjacent 2 3 3. Proof. left; reflexivity. Qed.
Lemma adj313 : adjacent 3 1 3. Proof. left; reflexivity. Qed.
Lemma adj323 : adjacent 3 2 3. Proof. right; reflexivity. Qed.

(** The next computation shows that permutations
    ::3, 2::4, 3::1, 4::2 are missing where the setsize
    (number of dimensions) is 4. *)
Eval compute in all_cyclic_permutations 4.
(** Outputs the following:
     = (1 :: 2 :: 3 :: 4 :: nil) :: (1 :: 4 :: 3 :: 2 :: nil)
    :: (2 :: 3 :: 4 :: 1 :: nil) :: (2 :: 1 :: 4 :: 3 :: nil)
    :: (3 :: 4 :: 1 :: 2 :: nil) :: (3 :: 2 :: 1 :: 4 :: nil)
    :: (4 :: 1 :: 2 :: 3 :: nil) :: (4 :: 3 :: 2 :: 1 :: nil)
    :: nil :: nil
*)

(** It has been shown that not all possible permutations
   are possible in a cyclically ordered set, where setsize = 4.
   Therefore, it remains to prove that for all setsizes
   greater than 3, that some permutations are not
   possible (that is, some dimensions are not cyclically
   adjacent to each other).

   Because it is only necessary to show that some permutations
   are not possible where setsize > 3, it will be sufficient to
   prove that the first dimension is not cyclically adjacent to
   the third dimension for all setsize > 3. *)
Theorem not_all_mutually_adjacent_gt_3 : forall m n setsize: nat,
  m = 1 /\ 3 = n /\ (setsize > 3) -> ~adjacent m n setsize.
Proof.
  intros. unfold not. intros. unfold adjacent in H0.
  unfold cyclic_successor in H0. unfold cyclic_predecessor in H0.
  decompose [and or] H. decompose [or] H0.
  assert (m_lt_setsize: m < setsize).
    rewrite -> H1. omega.
  assert (lt_beq_false : forall m n: nat,
            m < n -> beq_nat m n = false).
    intros. apply beq_nat_false_iff. omega.
  apply lt_beq_false in m_lt_setsize. rewrite -> m_lt_setsize in H2.
  rewrite -> H1 in H2. rewrite <- H3 in H2. inversion H2.
  assert (eq_beq_true : forall m n: nat,
            m = n -> beq_nat m n = true).
    intros. apply beq_nat_true_iff. exact H5.
  apply eq_beq_true with (m := m) (n := 1) in H1.
  rewrite -> H1 in H2. rewrite <- H3 in H2. rewrite -> H2 in H4.
  omega.
Qed.

End CyclicOrder.