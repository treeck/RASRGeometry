(** Copyright (c) 2015-2022 George M. Van Treeck.
    Rights granted under the Creative Commons
    Attribution License.
    This software uses The Coq Proof Assistance,
    Copyright (c) 1999-2022  The Coq Development Team
    Rights granted under
    GNU Lesser General Public License Version 2.1. *)

Require Import Arith PeanoNat Lia Field Bool Sumbool List.

Require Import Rdefinitions Raxioms RIneq Rfunctions R_Ifp.

Section EuclideanRelations.

(**
   This file contains defintions and proofs for set operations,
   list opertations, the ruler measure, operations on lists of
   real numbers, and finally sections with proofs of volume,
   Minkowski ditances/Lp norms, etc.
*)
(*
   The definitions, lemmas, and proofs of the set operations,
   lists, ruler measure, volume, Minkowski distance, etc. are
   all in one file, because I wanted this file to be easy to
   use by just loading this one file and everything works
   without any special setup of load and import paths.
*)

(** ==================================================== *)
(** This section has generic set definitions and proofs. *)

(** Allow sets of any type. *)
Variable A : Type.
(** Equality of instances of a type is decideable. *)
Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

(** Member of the set. *)
Fixpoint set_member (a:A) (x: list A) : bool :=
    match x with
    | nil => false
    | a1 :: x1 => if (eq_dec a a1) then true else set_member a x1
    end.

(** Append a list of sets. *)
Fixpoint lists_appended (l: list (list A)) : list A :=
    match l with
    | nil => nil
    | a::x => a++(lists_appended x)
    end.

(** Return a list with the duplicates removed. *)
Fixpoint uniques(x: list A) : list A :=
    match x with
    | nil => nil
    | a1 :: x1 =>
        if set_member a1 x1 then
             uniques x1 else a1 :: uniques x1
    end.

(** Union of a list of sets. *)
Definition union (l: list (list A)) : list A :=
    uniques (lists_appended l).

(** Return a list of the duplicates. *)
Fixpoint dups(x: list A) : list A :=
    match x with
    | nil => nil
    | a1 :: x1 =>
        if set_member a1 x1 then
             a1 :: dups x1 else dups x1
    end.

(** Duplicates in a list of sets. *)
Definition duplicates (l: list (list A)) : list A :=
    dups (lists_appended l).

(** Intersection is the duplicates sets with non-unique
    duplicates removed. *)
Definition intersection (l: list (list A)) : list A :=
    uniques (duplicates l).

(** Difference between a set of uniques, nd, and dups, d. *)
Fixpoint diff_dups (nd d: list A) : list A :=
    match nd with
    | nil => nil
    | a1 :: x1 =>
        if set_member a1 d then
             diff_dups x1 d else a1 :: diff_dups x1 d
    end.

(** Difference between a list of sets. *)
Definition diff (l: list (list A)) : list A :=
    diff_dups (union l) (intersection l).

(** Sum the cardinals of a list of sets. *)
Fixpoint list_lengths_summed (l: list (list A)) : nat :=
    match l with
    | nil => 0
    | a::x => length a + (list_lengths_summed x)
    end.

(** The cardinal of an appended set is equal to sum of
    the cardinals of each set. *)
Lemma cardinal_lists_appended_eq_list_lengths_summed :
    forall (l: list (list A)),
    length (lists_appended l) = list_lengths_summed l.
Proof.
  intros.
  induction l. reflexivity.
  assert (app_l_lists : forall (x: list A) (y: list (list A)),
      lists_appended (x::y) = x++(lists_appended y)).
      intros. induction y. reflexivity. reflexivity.
  rewrite app_l_lists.
  assert (summed_lists : forall (x: list A) (y: list (list A)),
      list_lengths_summed (x::y) = length x + list_lengths_summed y).
      intros. induction y. reflexivity. reflexivity.
  rewrite summed_lists.
  rewrite app_length.
  lia.
Qed.

(** The length of a list is equal to length of the duplicate elements
   plus the unique elements. *)
Lemma set_mem_in_duplicates_or_union : forall (a: A) (l: list A),
    length l = length ((dups l) ++ (uniques l)).
Proof.
  intros.
  induction l. reflexivity. simpl.
  induction set_member. simpl. inversion IHl. reflexivity.
  assert (length (dups l ++ a0 :: uniques l) =
          length (a::nil) + length (dups l ++ uniques l)).
      simpl. rewrite -> app_length. simpl.
      assert (forall n: nat, S n = n + 1).
          intros. lia.
      rewrite -> H. rewrite -> plus_assoc. rewrite <- app_length.
      rewrite <- H. reflexivity.
  rewrite -> H. simpl. inversion IHl. reflexivity.
Qed.

(** The cardinal of a list of sets is equal to the cardinal of
    the union plus duplicates of that list of sets. *)
Lemma card_app_eq_card_union_plus_dups :
    forall (a: A) (l: list (list A)),
    length (lists_appended l) = length (duplicates l ++ union l).
Proof.
  intros. unfold duplicates. unfold union.
  apply set_mem_in_duplicates_or_union. assumption.
Qed.

(** The sum of the cardinal of sets equals the
    cardinal of the union plus the cardinal of the duplicates. *)
Theorem sum_eq_uniques_plus_duplicates :
    forall (a: A) (l: list (list A)),
    list_lengths_summed l = length (duplicates l) + length (union l).
Proof.
  intros. rewrite <- cardinal_lists_appended_eq_list_lengths_summed.
  rewrite <- app_length.
  apply card_app_eq_card_union_plus_dups. assumption.
Qed.


(** The size (cardinal) of the union set is less than and
    equal to the sum of set sizes. *)
Theorem union_sum_inequality :
    forall (a: A) (l: list (list A)),
    length (union l) <= list_lengths_summed l.
Proof.
  intros.
  rewrite -> sum_eq_uniques_plus_duplicates.
  apply le_plus_r. assumption.
Qed.

(** End of generic set operations and proofs. *)

(** ==================================================== *)
(** Start of generic operations on lists. *)

(** default value returned when no set member found. *)
Variable default_element: A.

(** Definition of an empty set. *)
Definition empty_list : list A := nil.

(** Returns the element at position i in the list. *)
Fixpoint list_mem (i:nat) (l:list A) {struct l} : A :=
    match i, l with
    | O, _ => default_element
    | S m, nil => default_element
    | S m, h::t => list_mem m t
    end.

(** End of generic operations on lists. *)

(** ================================================================ *)
(** Start of generic operations and proofs for lists of
    real numbers *)

Local Open Scope nat_scope.
Local Open Scope R_scope.
Local Open Scope list_scope.

(** If two natural numbers are equal then they are also equal
    as real numbers *)
Lemma eq_INR : forall (m n: nat), (m = n)%nat -> INR m = INR n.
Proof.
  induction 1; intros; apply @eq_refl.
Qed.

(** Return a list of n number of real values, initialized
    to 0. *)
Fixpoint rlist (n : nat) (r: R) : list R :=
  match n with
  | O => nil
  | S n' => r:: (rlist n' r)
  end.

(** Returns the element at position i in the list. *)
Fixpoint list_rmem (i:nat) (l:list R) {struct l} : R :=
    match i, l with
    | O, _ => 0
    | S m, Datatypes.nil => 0
    | S m, h::t => list_rmem m t
    end.

(** Raise a real number, r, to the n-th power. *)
Fixpoint Rpow (r: R) (n: nat) : R :=
    match n with
        | 0%nat => 1
        | S n' =>(r * Rpow r n')
    end.

(** x >= 0, n >= 1 -> x^{n} >= 0. *)
Hypothesis Rpow_ge_0 :
    forall (x: R) (n: nat), x >= 0 -> Rpow x n >= 0.

(** r1^n * r2^n = (r1 * r2)^n *)
Hypothesis pow_distributes : forall (r1 r2: R) (n: nat),
    (Rpow r1 n) * (Rpow r2 n) = Rpow (r1 * r2) n.

(** f(x) = f(y) -> x = y applied to power functions *)
Hypothesis pow_eq_args : forall (r1 r2: R) (n: nat),
    Rpow r1 n = Rpow r2 n -> r1 = r2.

(** f(x) <= f(y) -> x <= y applied to power functions *)
Hypothesis pow_le_args : forall (r1 r2: R) (n: nat),
    Rpow r1 n <= Rpow r2 n -> r1 <= r2.

(** f(x) >= f(y) -> x >= y applied to power functions *)
Hypothesis pow_ge_args : forall (r1 r2: R) (n: nat),
    Rpow r1 n >= Rpow r2 n -> r1 >= r2.

(** Assume that if real number, r, exists then that number is
    the n-th root some other real number, r'. *)
Hypothesis nth_root_exists :
    forall (r: R) (n: nat), exists (r': R), r = (Rpow r' n).

(** Two sets of real values are equal if all the elements
    at the same positions are also equal. *)
Inductive eq_list_R : list R -> list R -> Prop :=
  | eq_list_R_nil : eq_list_R Datatypes.nil Datatypes.nil
  | eq_list_R_cons : forall (i: nat) (l1 l2: list R),
      list_rmem i l1 = list_rmem i l2 -> eq_list_R l1 l2.

(** Lists with same real values at same positions are equal. *)
Hypothesis eq_list_R_is_eq : forall (l1 l2: list R),
    eq_list_R l1 l2 -> l1 = l2.

(** Reflexivity on lists of real values. *)
Lemma list_refl : forall (x y: list R), x = y -> y = x.
Proof. intros. apply eq_sym ; assumption. Qed.

(** Sum a list of real numbers. *)
Fixpoint sum_list (l: list R) : R :=
    match l with
      | Datatypes.nil => 0
      | a::l' => a + (sum_list l')
    end.

(** Raise each member of a list of real numbers to
    the n^th power . *)
Fixpoint pow_list (l: list R) (n: nat) : list R :=
  match l with
    | Datatypes.nil => Datatypes.nil
    | a::l' => (Rpow a n)::(pow_list l' n)
  end.

(** Specification of pow_list. *)
Hypothesis pow_list_spec : forall (i n: nat) (a: R) (l: list R),
    (list_rmem i l) = a <-> list_rmem i (pow_list l n) = Rpow a n.

(** Multiply each member of a list of real numbers by the number, r. *)
Fixpoint mult_list (l: list R) (r: R) : list R :=
    match l with
      | Datatypes.nil => Datatypes.nil
      | a::l' => (a*r)::(mult_list l' r)
    end.

(** Specification of mult_list. *)
Hypothesis mult_list_spec : forall (i: nat) (a r: R) (l: list R),
    (list_rmem i l) = a <-> list_rmem i (mult_list l r) = a * r.

(** r * (a1 + a2 + ... + an) = (a1*r) + (a2*r) + ... + (an*r). *)
Hypothesis mult_distributes_over_sum_list :
    forall (l: list R) (r: R),
    (sum_list l) * r = sum_list(mult_list l r).

(** The cartesian product of a list of numbers. *)
Fixpoint cartesian_product (l: list R) : R :=
    match l with
        | Datatypes.nil => 1
        | hd::tl => hd * cartesian_product tl
    end.

(** r^n * (a1 * a2 * ... * an) = (a1*r) * (a2*r) * ... * (an*r). *)
Hypothesis pow_distributes_over_cartesian_product :
    forall (l: list R) (r: R) (n: nat), n = length l ->
    (cartesian_product l) * Rpow r n = cartesian_product (mult_list l r).

(* Binomial coefficitnt, n Choose k at a time:
   n_Choose_k = n!/(k!(n-k)!). *)
Definition n_Choose_k (k n: nat) : R :=
  INR (fact(n))/(INR ((fact(k))* (fact(n-k)))).

(* Binomial expansion term *)
Definition binom_term (x y: R) (k n: nat) : R :=
  n_Choose_k k n * Rpow x (n - k) * Rpow y k.

(* List of binomial terms. *)
(** Raise each member of a list of real numbers to
    the n^th power . *)
Fixpoint binomial_term_list (l: list R) (x y: R) (k n: nat) :
  list R :=
  match l with
    | Datatypes.nil => Datatypes.nil
    | a::l' =>
     (binom_term x y k n)::(binomial_term_list l' x y (k + 1) n)
  end.

(** Specification of a list of n number of binomial terms. *)
Hypothesis binomial_term_list_spec :
    forall (a x y: R) (i k n: nat) (l: list R),
    (list_rmem i l) = a <->
    list_rmem i (binomial_term_list l x y k n) =
        binom_term x y k n.

(** Partially expanded binomial terms,
    x^n + n_Choose_k (n,1)x^(n-k)y^k + y^n. *)
Hypothesis binomial_expansion_equiv :
    forall (x y: R) (n: nat) (l: list R),
    sum_list (binomial_term_list l x y 0%nat n) =
        Rpow x n + Rpow y n +
           sum_list (binomial_term_list l x y 1%nat (n-1)).

(** Lower order binomial terms, for x y >= 0 :
    n_Choose_k (n,1)x^(n-k)y^ >= 0. *)
Hypothesis lower_order_binomial_terms :
    forall (x y: R) (n: nat) (l: list R),
    x = 0 /\ x > 0 /\ y = 0 /\ y > 0 ->
    sum_list (binomial_term_list l x y 1%nat (n-1)) >= 0.

Definition binomial_expansion (x y: R) (n: nat) : list R :=
    binomial_term_list (rlist n 0%R) x y 0%nat n.

Hypothesis binomial_eq :
    forall (x y: R) (n: nat),
    Rpow (x + y) n = sum_list (binomial_expansion x y n).


(** End of generic operations and proofs on lists of real numbers *)

(** ==================================================== *)
(** Start of definitions and proofs for the Ruler Measure *)

(** list_mem returns the ith list in list l. *)
Definition list_list_mem (i: nat) (l: list (list A)) :
    list A := nth i l nil.

(** The ruler measure definition is in terms of the
    floor function. The Coq starndard library does not
    have a real-valued version of the floor function.
    Therefore, the first step is define the floor
    function and prove some properties about the floor
    function. *)

(** Define the floor function as the integer part of
    a real-valued number. *)
Definition R_floor (x: R) : R := IZR (Int_part x).

(** The following lemmas about integer and fractional
    parts of a real number are used to prove properties
    of the R_floor function. *)

(** A real number is the sum of it's whole integer part
    plus the fractional part. *)
Lemma r_eq_ip_plus_frac :
    forall r: R, r = IZR (Int_part r) + frac_part r.
Proof.
  intros. unfold Int_part. unfold frac_part.
  unfold Int_part. apply eq_sym ; trivial. apply Rplus_minus.
Qed.

(** 0 <= r - floor r < 1. That is, a real number minus the
    integer part is equal to the size of the fractional part. *)
Lemma r_minus_floor_ge_0_lt_1 : forall r: R,
    r - R_floor r >= 0 /\ r - R_floor r < 1.
Proof.
  intros. unfold R_floor.
  assert (r = IZR (Int_part r) + frac_part r).
    apply r_eq_ip_plus_frac.
  apply (Rplus_eq_compat_l
    (- IZR (Int_part r)) (r) (IZR (Int_part r) + frac_part r)) in H.
  rewrite -> (Rplus_comm (- IZR (Int_part r)) r) in H.
  rewrite <- (Rplus_assoc
    (-IZR (Int_part r)) (IZR (Int_part r)) (frac_part r) ) in H.
  rewrite -> (Rplus_comm (- IZR (Int_part r))
    (IZR (Int_part r))) in H.
  rewrite -> (Rplus_opp_r (IZR (Int_part r))) in H.
  rewrite -> (Rplus_0_l (frac_part r)) in H.
  assert (frac_part r >= 0 /\ frac_part r < 1).
  apply base_fp. decompose [and] H0.
  assumption.
Qed.

(** If r >= 0 then |r| >= 0. *)
Lemma ge_0_abs_ge_0 : forall r: R, r >= 0 -> Rabs r >= 0.
Proof.
  intros; unfold Rabs; case (Rcase_abs r); intro.
  absurd (r >= 0). exact (Rlt_not_ge r 0 r0). assumption. assumption.
Qed.

(** 0 <= |r - floor r| < 1. *)
Lemma abs_r_minus_floor_ge_0_lt_1 : forall r: R,
    Rabs (r - R_floor r) >= 0 /\ Rabs(r - R_floor r) < 1.
Proof.
  intros. unfold R_floor.
  assert (r - IZR (Int_part r) >= 0 /\ r - IZR (Int_part r) < 1).
    apply r_minus_floor_ge_0_lt_1. decompose [and] H.
  split. revert H0. apply ge_0_abs_ge_0.
  assert (r - IZR (Int_part r) >= 0 ->
    Rabs (r - IZR (Int_part r))= r - IZR (Int_part r)).
  apply Rabs_right with (r := r - IZR (Int_part r)).
  rewrite -> H2. assumption. assumption.
Qed.

(** 0 <= |floor r - r| < 1. *)
Lemma abs_floor_minus_r_ge_0_lt_1 : forall r: R,
    Rabs (R_floor r - r) >= 0 /\ Rabs(R_floor r - r) < 1.
Proof.
  intros. rewrite (Rabs_minus_sym (R_floor r) r).
  apply abs_r_minus_floor_ge_0_lt_1.
Qed.

(** This lemma is missing from the standard library, RIneq.v. *)
Lemma R_lt_mult_lt : forall r r1 r2 : R,
     0 < r -> r1 < r2 -> r * r1 < r * r2.
Proof. intros. apply Rmult_lt_compat_l. assumption. assumption. Qed.

(**
   Now the ruler measure convergence proof follows:
*)

(** The exact size of a interval. *)
Definition exact_size (a b: R) : R := Rabs (b - a).

(** The number of subintervals with size, c. *)
Definition subintervals (a b c: R) : R :=
  R_floor (exact_size a b / c).

(** M is the ruler measure, subintervals * c. *)
Definition M (a b c: R) : R := (subintervals a b c) * c.

(** Used for rewriting between M and subintervals. *)
Lemma subintervals_times_c_eq_measure :
    forall a b c: R, c > 0 ->
    M a b c = (subintervals a b c) * c.
Proof. intros. unfold M. reflexivity. Qed.

(** Let r := subintervals in 0 <= |floor r - r| < 1. *)
Lemma subintervals_div_c_le_size : forall a b c: R,
    c > 0 ->
    Rabs(subintervals a b c - (exact_size a b) / c) < 1.
Proof.
  intros. unfold subintervals.
  apply abs_floor_minus_r_ge_0_lt_1.
Qed.

(** |M - s| < |c|}. *)
Lemma abs_M_minus_s_lt_abs_c : forall a b c: R,
    c > 0 ->
    Rabs((M a b c) - exact_size a b) < Rabs c.
Proof.
  intros. unfold M. unfold subintervals.
  assert (Rabs(R_floor(exact_size a b / c) -
      (exact_size a b) / c) < 1).
    apply subintervals_div_c_le_size.
    assumption.
  apply R_lt_mult_lt with (r := Rabs c)
    (r1 := Rabs (R_floor (exact_size a b / c) - exact_size a b / c))
    (r2 := 1) in H0.
  rewrite -> (Rmult_1_r (Rabs c)) in H0.
  rewrite <- (Rabs_mult (c)
    (R_floor (exact_size a b / c) - (exact_size a b / c))) in H0.
  unfold Rminus in H0.
  rewrite -> (Rmult_plus_distr_l (c)
    (R_floor (exact_size a b / c))
    (- (exact_size a b / c))) in H0.
  unfold Rdiv at 2 in H0.
  rewrite -> (Rmult_comm c (R_floor (exact_size a b / c))) in H0.
  rewrite -> (Ropp_mult_distr_r_reverse (c)
    (exact_size a b * / c)) in H0.
  rewrite <- (Rmult_assoc (c) (exact_size a b) (/ c)) in H0.
  rewrite -> (Rmult_comm c (exact_size a b)) in H0.
  rewrite -> (Rmult_assoc (exact_size a b) (c) (/ c)) in H0.
  rewrite -> (Rinv_r c) in H0.
  rewrite -> (Rmult_1_r (exact_size a b)) in H0.
  assumption.
  apply Rgt_not_eq.
  apply H.
  assert (c <> 0).
  apply Rgt_not_eq.
  apply H.
  revert H1.
    apply Rabs_pos_lt.
Qed.

(** Epsilon-delta proof. limit c->0,
    0 < |c - 0| < delta => |M - s| < epsilon. *)
Lemma M_minus_exact_size_lt_epsilon :
    forall a b c delta epsilon: R,
    c > 0 /\ 0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - 0) < delta ->
    Rabs(M a b c - exact_size a b) < epsilon.
Proof.
  intros. decompose [and] H.
  assert (Rabs (c - 0) = Rabs c).
  simple apply f_equal_R.
  simple apply Rminus_0_r.
  rewrite -> H5 in H6.
  assert (Rabs(M a b c - exact_size a b) < Rabs c).
    apply abs_M_minus_s_lt_abs_c. assumption.
  rewrite H3 in H6. revert H6. revert H7.
  apply Rlt_trans with
    (r1 := Rabs (M a b c - exact_size a b))
    (r2 := Rabs c)
    (r3 := epsilon).
Qed.

(** Defintion of a Epsilon-delta proof for ruler measure, M. *)
Hypothesis limit_x_Lim1_f_x_eq_Lim2 :
    forall (a b x Lim1 Lim2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    0 < delta /\ 0 < epsilon /\ g delta = epsilon /\
    Rabs (x - Lim1) < delta /\
    Rabs(f a b x - Lim2) < epsilon ->
    f a b x = Lim2.

(* The function relating delta to epsilon to prove
   convergence. *)
Definition delta_eq_epsilon(d: R) : R := d.

(** Epsilon-delta proof. limit c->0,
    0 < |x - 0| < delta, |M - s| < epsilon -> M = s. *)
Lemma limit_c_0_M_eq_exact_size :
    forall (a b c Lim1 Lim2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\ Lim2 = exact_size a b /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    Rabs (c - Lim1) < delta /\
    Rabs(M a b c - Lim2) < epsilon ->
    M a b c = exact_size a b.
Proof.
  intros. decompose [and] H.
  rewrite <- H2. rewrite <- H4.
  apply limit_x_Lim1_f_x_eq_Lim2 with (Lim1 := Lim1) (Lim2 := Lim2)
      (delta := delta) (epsilon := epsilon) (g := g).
  split. assumption. split. assumption.
  split.
  rewrite -> H1. unfold delta_eq_epsilon. assumption.
  split. assumption.
  rewrite -> H2. assumption.
Qed.

(** End RulerMeasure. *)

(** ======================================= *)
(**
  Now the definitions and theorems about volume and distance.
*)

(** List of the countable domain sets (x_i in X). *)
Variable list_x_i: list A.
(** List of countable domain sets, X = list(i=1 to n) list_x_i *)
Variable X: list (list A).
(** Xpd = union(i=1 to n) list_x_i *)
Variable Xpd: list A.
(** Counters *)
Variables i m n: nat.
(** The boundaries of a domain interval, [a_i,b_i},
   i in [1,n]). *)
Variables a_i b_i: R.
(** The list of the exact size of each interval,
    [a_i,b_i}, i in [1,n]). *)
Variable s: list R.
(** The list of cardnals corresponding to each list_x_i (the
    number of elements in the intervals [a_i,b_i},
    i in [1,n]). *)
Variable p: list R.
(** The ruler interval size. *)
Variable c: R.

(** Volume-specific variable definitions. *)

(** The countable size (length/area/volume) of a set of
    image elements. *)
Variable v v_c: R.
(** The boundaries of the image (size) interval, [v_0,v_m]. *)
Variables v_a v_b: R.

(** An Epsilon-delta definition for c^n used in
    lemma lim_power_c_to_n_eq_c. *)
Hypothesis limit_c_Lim1_f_c_eq_Lim2 :
    forall (c Lim1 Lim2 delta epsilon:R),
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    Rabs (c - Lim1) < delta /\
    Rabs(c - Lim2) < epsilon ->
    c = 0.

(** An Epsilon-delta definition for c^n used in
    lemma lim_power_c_to_n_eq_c. *)
Hypothesis limit_c_Lim1_f_c_n_eq_Lim2 :
    forall (c Lim1 Lim2 delta epsilon:R)
        (f: R->nat->R) (g: R->R),
    0 < delta /\ 0 < epsilon /\ g delta = epsilon /\
    Rabs (c - Lim1) < delta /\
    Rabs(f c n - Lim2) < epsilon ->
    f c n = 0.

(** This lemma is used in the volume proof. *)
Lemma lim_c_to_n_eq_0 :
    forall ( c Lim1 Lim2 delta epsilon:R)
        (f: R->nat->R) (g: R->R),
    c > 0 /\
    f = Rpow /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\ Lim2 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    Rabs (c - Lim1) < delta /\
    Rabs ((Rpow c n) - Lim2) < epsilon ->
    Rpow c n = 0.
Proof.
  intros. decompose [and] H.
  rewrite <- H2.
  apply limit_c_Lim1_f_c_n_eq_Lim2 with (Lim1 := Lim1) (Lim2 := Lim2)
      (delta := delta) (epsilon := epsilon) (g := g).
  split. assumption. split. assumption.
  split. rewrite -> H1. unfold delta_eq_epsilon. assumption.
  split. assumption.
  rewrite -> H2. assumption. 
Qed.

Lemma lim_c_to_n_eq_lim_c :
    forall ( c Lim1 Lim2 delta epsilon:R)
        (f: R->nat->R) (g: R->R),
    c > 0 /\
    f = Rpow /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\ Lim2 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    Rabs (c - Lim1) < delta /\
    Rabs ((Rpow c n) - Lim2) < epsilon ->
    Rpow c n = c.
Proof.
  intros. decompose [and] H.
  assert (Lim1 = Lim2). rewrite -> H3. rewrite -> H4. trivial.
  assert (c0 = 0).
  apply limit_c_Lim1_f_c_eq_Lim2 with (Lim1 := Lim1) (Lim2 := Lim2)
      (delta := delta) (epsilon := epsilon).
  split. assumption. split. assumption.
  split. assumption. split. assumption.
  rewrite <- H9. rewrite <- H7. assumption.
  assert (Rpow c0 n = 0).
  apply lim_c_to_n_eq_0 with (Lim1 := Lim1) (Lim2 := Lim2)
      (delta := delta) (epsilon := epsilon) (f := f) (g := g).
  split. assumption. split. assumption.
  split. assumption. split. assumption.
  split. assumption. split. assumption.
  split. assumption. split. assumption.
  split. assumption. assumption.
  rewrite <- H11 in H12. assumption.
Qed.

(**
  A countable volume measure of a list of domain sets:
  forall i in [1,n], x_i in ith set of X in 
  intersection X = empty_set /\
  p_i = cardinal of ith set of X ->
  size, v_c = |{(X_1,...,X_n)}|=|list_x_1|*...*|list_x_n|.
*)
Hypothesis countable_volume_measure :
    (i <= n)%nat /\ length X = n /\
    duplicates X = empty_list /\
    list_rmem i p = subintervals a_i b_i c /\
    v_c = cartesian_product p.

(** The Euclidean volume (length/area/volume) theorem:
    v, is the length of a real-valued interval in:
    {}a_1, b_1],...,[a_n, b_n]}, where:
    v_c = cartesian_product p => v = cartesian_product(i=1 to n) s_i /\
    v = v_{m} - v_{0} /\
    s_i = b_i - a_i. *)
Theorem Euclidean_volume :
    forall (Lim1 Lim2 delta epsilon p_v: R)
        (f: R->R->R->R) (g: R->R),
    (* ruler based definitions *)
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\ Lim2 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    Rabs (c - Lim1) < delta /\
    Rabs ((Rpow c n) - Lim2) < epsilon /\
    Rabs (M a_i b_i c - exact_size a_i b_i) < epsilon /\
    n = length s /\ length p = n /\
    (* The length of each domain interval, exact_size a_i b_i,
       is assinged to a member of s. *)
    list_rmem i s = exact_size a_i b_i /\
    (* The number of subintervals in each domain interval,
       subintervals a_i b_i c, is assinged to a member of p. *)
    list_rmem i p = subintervals a_i b_i c /\
    (* Volume, v, is the length of the range interval, [v_a,v_b]. *)
    v = exact_size v_a v_b /\
    (* Countable n-volume, v_c, is the number of subintervals
       (infinitesimals) in the range interval, [v_a,v_b]. *)
    v_c = subintervals v_a v_b c /\
    (* The definition of countable n-volume as the Cartesian product
       of the number of members in each countable domain set. *)
    v_c = cartesian_product p ->
    v = cartesian_product s.
Proof.
  intros. intros.
  decompose [and] countable_volume_measure. decompose [and] H.
  decompose [and] H0.
  (* Show that each domain interval length, s_i = |b_i - a_i|,
     corresponds to a set of p_i number of size c subintervals. *)
  apply mult_list_spec with (l := p)
      (a := subintervals a_i b_i c) (r := c) in H19.
  rewrite <- subintervals_times_c_eq_measure in H19.
  rewrite -> limit_c_0_M_eq_exact_size with
      (a := a_i) (b := b_i) (c := c) (Lim1 := Lim1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (Lim2 := exact_size a_i b_i) (f := M) in H19.
  rewrite <- H18 in H19.
  (* Show that the list, s, of domain interval lengths corresponds
     to the list, p, of the number of size c subintervals. *)
  apply eq_list_R_cons with  (l1 := mult_list p c) (l2 := s) in H19.
  apply eq_list_R_is_eq in H19.
  (* Show that the Cartesian product of the number of size c
     subintervals equals the product of interval lengths. *)
  assert (cartesian_product (mult_list p c) = cartesian_product s).
  rewrite -> H19.
  reflexivity.
  (* Show that multiplying both sides of countable distance
     by c^{n}, maintains the equivalence relation. *)
  assert (v_c * (Rpow c n) = (cartesian_product p) * (Rpow c n)).
  rewrite <- H23.
  reflexivity.
  (* Show that (cartesian_product p) * Rpow c n =
     cartesian_product s *)
  assert ((cartesian_product p) * Rpow c n =
          cartesian_product (mult_list p c)).
  apply pow_distributes_over_cartesian_product.
  symmetry. assumption.
  rewrite -> H22 in H25.
  (* Show that v_c * Rpow c n = cartesian_product s *)
  rewrite <- H24 in H25.
  (* Show that lim c->0 (v_c * Rpow c n) = lim c->0 (v_c * c) *)
  assert (Rpow c n = c).
  apply lim_c_to_n_eq_lim_c with (c := c) (Lim1 := Lim1)
      (Lim2 := Lim2) (g := g) (delta := delta)
      (epsilon := epsilon) (f := Rpow).
  split. assumption. split. reflexivity.
  split. assumption. split. assumption.
  split. assumption. split. assumption.
  split. assumption. split. assumption.
  split. assumption. assumption.
  rewrite -> H26 in H25.
  (* Show that lim c->0 v_c * c = v *)
  rewrite -> H21 in H25.
  rewrite <- subintervals_times_c_eq_measure in H25.
  rewrite -> limit_c_0_M_eq_exact_size with
      (a := v_a) (b := v_b) (c := c) (Lim1 := Lim1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (Lim2 := exact_size v_a v_b) (f := M) in H25.
  rewrite <- H20 in H25.
  assumption.
  (* Clean up hypothoses *)
  split. assumption. split. reflexivity.
  split. assumption. split. assumption.
  split. reflexivity. split. assumption. split. assumption.
  split. assumption. split. assumption.
  apply M_minus_exact_size_lt_epsilon with
    (a := v_a) (b := v_b) (c := c) 
    (delta := delta) (epsilon := epsilon).
  split. assumption. split. assumption. split. assumption.
  split. assumption. split.
  assert (Rabs (c - 0) = Rabs c).
  simple apply f_equal_R.
  simple apply Rminus_0_r.
  assert (Rabs c = c).
  apply Rabs_right. intuition.
  rewrite -> H27.
  rewrite -> H28.
  assumption.
  rewrite <- H8.
  assumption.
  assumption.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. assumption. split. assumption.
  assumption.
  assumption.
Qed.

(** ================================================================ *)

(** Variables used in the distance proofs. *)

(** List of the countable range sets (y_i in Y). *)
Variable list_y_i: list A.
(** List of countable image sets, Y = union(i=1 to n) list_y_i *)
Variable Y: list (list A).
(** Countable distance is cardinal of Y = union(y_i). *)
Variable d_c: nat.
(** The boundaries of the image (distance) interval, [d_0,d_m]. *)
Variables d_0 d_m: R.
(* The real-valued size of the distance interval [d_0,d_m]. *)
Variable d: R.

(** From the ruler measure, these are exact
    sizes of the domain and image intervals that the
    subintervals must be shown to converge to. *)
Hypothesis exact_d_sizes :
    list_rmem i s = exact_size a_i b_i /\
    d = exact_size d_0 d_m.

(** Definitions of domain and image subintervals that are
    used in Minkowski distance/Lp norm proofs. *)
Hypothesis ruler_d_subintervals :
    c > 0 /\
    subintervals a_i b_i c = INR (length list_x_i) /\
    list_rmem i p = subintervals a_i b_i c /\
    subintervals d_0 d_m c = INR d_c.

(**
  A countable n-volume is the sum of n-volumes.
*)
Hypothesis countable_n_volume :
    exists (m0 : nat),
    length p = m0 /\
    (i <= m0)%nat /\ length Y = m0 /\
    (* list_y_i is the i_th domain set in Y *)
    list_y_i = list_list_mem i Y /\
    list_rmem i p = INR (length list_y_i) /\
    Rpow (INR d_c) n = sum_list (pow_list p n).

(** For econvenience in the following proof steps, create the
    variable pow_d_c = Rsqr d_c. *)
Variable pow_d_c_n: R.
(** From the lemma, pow_d_c_eq_sum_squares, pow_d_c = Rsqr d_c =>
    pow_d_c = sum_list (sqr_list p). *)
Hypothesis pow_d_c_sum_powers :
    pow_d_c_n = sum_list (pow_list p n).

(** Multiply both sides Rsqr c and apply the ruler measure and
    covergence theorem. *)
Lemma d_c_measure :
    forall (Lim1 Lim2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - Lim1) < delta ->
    pow_d_c_n * Rpow c n = sum_list (pow_list s n).
Proof.
  intros. decompose [and] H.
  decompose [and] exact_d_sizes.
  decompose [and] ruler_d_subintervals.
  assert (pow_d_c_n * (Rpow c n) =
      sum_list (mult_list (pow_list p n) (Rpow c n))).
      rewrite <- mult_distributes_over_sum_list.
      apply Rmult_eq_compat_r with (r := Rpow c n)
          (r1 := pow_d_c_n)
          (r2 := sum_list (pow_list p n)).
      assumption.
  rewrite <- limit_c_0_M_eq_exact_size with
          (a := a_i) (b := b_i) (c := c)  (Lim1 := Lim1)
          (g := g) (delta := delta) (epsilon := epsilon)
          (Lim2 := exact_size a_i b_i) (f := M) in H8.
  unfold M in H8.
  assert (list_rmem i (pow_list s n) =
      Rpow (subintervals a_i b_i c * c) n).
      apply pow_list_spec with
          (l := s) (a := subintervals a_i b_i c * c).
      assumption.
  assert (list_rmem i (pow_list p n) =
        Rpow (subintervals a_i b_i c) n).
      apply pow_list_spec with
          (l := p) (a := subintervals a_i b_i c).
      assumption.
  apply mult_list_spec with (l := pow_list p n)
      (a := Rpow (subintervals a_i b_i c) n)
      (r := Rpow c n) in H17.
  rewrite -> pow_distributes in H17.
  rewrite <- H16 in H17.
  apply eq_list_R_cons in H17. apply eq_list_R_is_eq in H17.
  rewrite -> H17 in H14.
  assumption.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption.
  apply M_minus_exact_size_lt_epsilon with
    (a := a_i) (b := b_i) (c := c) 
    (delta := delta) (epsilon := epsilon).
    split. assumption. split. assumption. split. assumption.
    split. assumption.
    split. rewrite <- H3 at 2. assumption.
    rewrite <- H3. assumption.
Qed.

(** d_c = subintervals d_0 d_m c =>
          pow_d_c_n = (subintervals d_0 d_m c)^n *)
Hypothesis pow_d_c_n_eq_pow_image_subintervals :
    pow_d_c_n = Rpow (subintervals d_0 d_m c) n.

(** Multiply both sides by Rpow c n and
    apply the ruler measure and convergence theorem to get
    the distance measure. *)
Lemma pow_d_measure :
    forall (Lim1 Lim2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - Lim1) < delta ->
    Rpow d n = pow_d_c_n * Rpow c n.
Proof.
  intros. decompose [and] H.
  decompose [and] exact_d_sizes. decompose [and] ruler_d_subintervals.
  rewrite -> H10.
  rewrite <- limit_c_0_M_eq_exact_size with
      (a := d_0) (b := d_m) (c := c)  (Lim1 := Lim1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (Lim2 := exact_size d_0 d_m) (f := M).
  unfold M.
  rewrite -> pow_d_c_n_eq_pow_image_subintervals.
  rewrite <- pow_distributes.
  trivial.
  split. assumption. split. trivial. split. assumption.
  split. assumption. split. trivial. split. assumption.
  split. assumption. split. assumption. split. assumption.
  apply M_minus_exact_size_lt_epsilon with
    (a := d_0) (b := d_m) (c := c) 
    (delta := delta) (epsilon := epsilon).
    split. assumption. split. assumption. split. assumption.
    split. assumption.
    split. rewrite <- H3 at 2. assumption.
    rewrite <- H3. assumption.
Qed.

(** Combine the previous two lemmas to prove the
    Minkowski distance. *)
Theorem Minkowski_distance :
    forall (Lim1 Lim2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    Lim1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - Lim1) < delta ->
    Rpow d n = sum_list (pow_list s n).
Proof.
  intros. decompose [and] H.
  decompose [and] exact_d_sizes. decompose [and] ruler_d_subintervals.
  assert (pow_d_c_n * Rpow c n = sum_list (pow_list s n)).
      revert H.
      apply d_c_measure. assumption.
      rewrite <- H14.
  assert (Rpow d n = pow_d_c_n * Rpow c n).
      revert H.
      apply pow_d_measure. assumption.
  rewrite -> H16.
  trivial.
Qed.

(** ================================================================ *)

(** forall a >= 0, b >= 0 => a <= a + b. *)
Hypothesis R_le_plus_r :
    forall (a b: R), a >= 0 /\ b >= 0 -> a <= a + b.

(** forall a >= 0, b >= 0 => a + b >= 0. *)
Hypothesis Rsum_ge_0 :
    forall (a b: R), a >= 0 /\ b >= 0 -> a + b >= 0.

(** forall a >= 0, b >= 0 => a * b >= 0. *)
Hypothesis Rtimes_ge_0 :
    forall (a b: R), a >= 0 /\ b >= 0 -> a * b >= 0.

(** The distance inequality proof should be expressed as:
    forall v_a, v_b >= 0, n >= 1:
    (v_a + v_b)^{1/n) <= v_a^{1/n} + v_b^{1/n}.
    This inequality is used in deriving the metric space triangle
    inequality.
    But, the Coq definition for the type, R, is such that it is not
    possible to construct an n-th root function. For example, given,
    d^n = v <-> d = v^{1/n_, it is difficult to express and compute
    the value for d, where the values of v and n are known.
    Therefore, the inequality proof here stops at the step before
    taking the n-th root of both sides of the inequality. *)
Theorem distance_inequality :
    forall (d_a d_b: R),
    d_a = 0 /\ d_a > 0 /\ d_b = 0 /\ d_b > 0 ->
    Rpow d_a n + Rpow d_b n <= Rpow (d_a + d_b) n.
Proof.
  intros. decompose [and] H.
  rewrite -> binomial_eq.
  unfold binomial_expansion.
  rewrite -> binomial_expansion_equiv.
  assert (forall (a b: R), a >= 0 /\ b >= 0 -> a <= a + b).
    intros. decompose [and] H3.
    apply R_le_plus_r. assumption.
  apply H3 with (a := Rpow d_a n + Rpow d_b n)
(b := sum_list (binomial_term_list (rlist n 0) d_a d_b 1 (n - 1))).
  split.
  apply Rsum_ge_0 with (a := Rpow d_a n) (b := Rpow d_b n).
  split.
  apply Rpow_ge_0 with (x := d_a) (n := n). intuition.
  apply Rpow_ge_0 with (x := d_b) (n := n). intuition.
  apply lower_order_binomial_terms.
  split. assumption. split. assumption. split. assumption.
  assumption.
Qed.

(** Two lists of real values. *)
Variable p1 p2 p3: list R.

Theorem distance_sum_inequality :
    forall (d_a d_b: R),
    d_a = 0 /\ d_a > 0 /\ d_b = 0 /\ d_b > 0 /\
    d_a = sum_list (pow_list p1 n) /\
    d_b = sum_list (pow_list p2 n) ->
    Rpow (sum_list (pow_list p1 n)) n +
      Rpow (sum_list (pow_list p2 n)) n <=
    Rpow (sum_list (pow_list p1 n) + sum_list (pow_list p2 n)) n.
Proof.
  intros. decompose [and] H.
  rewrite <- H4.
  rewrite <- H6.
  apply distance_inequality.
  split. assumption. split. assumption.
  split. assumption. assumption.
Qed.

(** ================================================================ *)

(* Metric space properties *)

(* Points in the domain set of a metric space. *)
Variable u w: R.
(* Range set distances d(u,w), d(u,v), d(v,w) and
   d(w,w). *)
Variable d_u_w d_u_v d_v_w d_w_w d_w_v d_v_u: R.

(* Symmetry: d(v,w) = d(w,v).
   From the Euclidean (smallest) and Manhattan (largest)
   distance proofs, all d(x,y): d(x,y) = (x^n + y^n)^{1/n),
   where 1 <= n <= 2.
   Therefore, d(u,v)^n = u^n + y^n /\ d(v,u)^n = v^n + u^n,
   which implies that d(v,u) = d(u,v). *)
Theorem symmetry :
    Rpow d_u_v n = Rpow u n + Rpow v n /\
    Rpow d_v_u n = Rpow v n + Rpow u n
    -> d_u_v = d_v_u.
Proof.
  intros. decompose [and] H.
  assert (Rpow u n + Rpow v n = Rpow v n + Rpow u n).
    intuition.
  rewrite -> H2 in H0.
  rewrite <- H1 in H0.
  apply pow_eq_args in H0.
  assumption.
Qed.

(* Metric space triangle inequality,
   d(u,w) <= d(u,v) + d(v,w) <->
   d(u,w)^n <= (d(u,v) + d(v,w))^n. *)
Theorem riangle_inequality :
    u >= 0 /\ v >= 0 /\ w >= 0 /\
    d_u_w = 0 /\ d_u_w > 0 /\
    d_u_v = 0 /\ d_u_v > 0 /\ d_v_w = 0 /\ d_v_w > 0 ->
    Rpow d_u_v n = Rpow u n + Rpow v n /\
    Rpow d_v_w n = Rpow v n + Rpow w n /\
    Rpow d_u_w n = Rpow u n + Rpow w n ->
    d_u_w <= d_u_v + d_v_w.
Proof.
  intros. decompose [and] H.
  assert (Rpow u n + Rpow w n <=
            Rpow u n + Rpow w n + (Rpow v n + Rpow v n)).
    assert (forall (a b: R), a >= 0 /\ b >= 0 -> a <= a + b).
      intros. decompose [and] H9.
      apply R_le_plus_r. assumption.
    apply H9 with (a := Rpow u n + Rpow w n)
        (b := Rpow v n + Rpow v n).
  split. apply Rsum_ge_0 with (a := Rpow u n) (b := Rpow w n).
  split. apply Rpow_ge_0. assumption.
    apply Rpow_ge_0. assumption.
    apply Rsum_ge_0. split.
    apply Rpow_ge_0. assumption.
    apply Rpow_ge_0. assumption.
  assert (Rpow u n + Rpow w n + (Rpow v n + Rpow v n) =
    (Rpow u n + Rpow v n) + (Rpow v n + Rpow w n)).
    field.
  rewrite -> H11 in H9.
  decompose [and] H0.
  rewrite <- H12 in H9.
  rewrite <- H14 in H9.
  rewrite <- H15 in H9.
  assert (Rpow d_u_v n + Rpow d_v_w n <= Rpow (d_u_v + d_v_w) n).
  apply distance_inequality.
  split. assumption. split. assumption. split. assumption.
  assumption.
  assert (Rpow d_u_w n <= Rpow (d_u_v + d_v_w) n).
  apply Rle_trans with (r1 := Rpow d_u_w n)
    (r2 := Rpow d_u_v n + Rpow d_v_w n)
    (r3 := Rpow (d_u_v + d_v_w) n).
  assumption.
  assumption.
  apply pow_le_args in H16.
  assumption.
Qed.

(* Non-negativity: d(u,w) >= 0, where for all d(u,w) in R,
   there exists [v_a, v_b] such that d(u,w) = |v_a - v_b|. *)
Theorem non_negativity :
    d_u_w = exact_size v_a v_b ->
    d_u_w >= 0.
Proof.
  intros.
  rewrite -> H.
  unfold exact_size.
  apply Rle_ge with  (r1 := 0) (r2 := Rabs (v_b - v_a)).
  apply Rabs_pos.
Qed.

(* a_v = f(v) *)
Variable a_u a_v a_w: R.

(* f(x) = f(y) <=> x = y *)
Hypothesis exact_size_eq_exact_size :
exact_size a_u a_w = exact_size a_u a_v
-> a_w = a_v.

(* Identity of Indiscernibles: d(w,w) = 0, where for
   all d(u,w) in R, there exists [a_u,a_w] such that
   d(u,w) = |a_u - a_w|, a_u = f(u) and a_w = f(w).
   And so on for d(u,v) and d(v,w). *)
Theorem identity_of_indisceunibles :
  (* from the triange inequality proof: *)
    d_u_w = exact_size a_u a_w /\
    d_u_v = exact_size a_u a_v /\
    d_v_w = exact_size a_v a_w /\
    d_w_w = exact_size a_w a_w /\
    d_u_w < d_u_v + d_v_w /\
    d_u_w = d_u_v + d_v_w /\
    (* from the non-negativity proof, there exists: *)
    d_u_v = 0 /\ d_v_w = 0
    -> d_w_w = 0.
Proof.
  intros. decompose [and] H.
  assert (d_u_w = 0).
  rewrite -> H6 in H5.
  rewrite -> H8 in H5.
  rewrite Rplus_0_r with (r := 0) in H5.
  assumption.
  rewrite <- H6 in H7.
  rewrite -> H0 in H7.
  rewrite -> H2 in H7.
  apply exact_size_eq_exact_size in H7.
  rewrite <- H7 in H1.
  rewrite <- H1 in H3.
  rewrite -> H8 in H3.
  assumption.
Qed.

End EuclideanRelations.