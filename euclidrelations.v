(** Copyright (c) 2015-2017 George M. Van Treeck.
    Rights granted under the Creative Commons
    Attribution License.
    This software uses The Coq Proof Assistance,
    Copyright (c) 1999-2017  The Coq Development Team
    Rights granted under
    GNU Lesser General Public License Version 2.1. *)

Section EuclideanRelations.

(**
   This file contains defintions and proofs for set operations,
   list opertations, the ruler measure, operations on lists of
   real numbers, and finally sections with proofs of taxicab
   distance, Euclidean distance, and size (length/area/volume).
*)
(*
   The definitions, lemmas, and proofs of the set operations,
   lists, ruler measure, Euclidean distance and size (volume)
   are all in one file, because I wanted this file to be easy
   to use by just loading this one file and everything works
   without any special setup of load and import paths.
*)

Require Import Arith NPeano Omega Bool Sumbool List.

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

(** Sum the cardinal of a list of sets. *)
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
  omega.
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
          intros. omega.
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
Theorem inclusion_exclusion_principle_alt :
    forall (a: A) (l: list (list A)),
    list_lengths_summed l = length (duplicates l) + length (union l).
Proof.
  intros. rewrite <- cardinal_lists_appended_eq_list_lengths_summed.
  rewrite <- app_length.
  apply card_app_eq_card_union_plus_dups. assumption.
Qed.

(** Rearrangement of the inclusion_exclusion_principle_alt into
    a form similar to the Da Silva formula, where the set of
    duplicates can be defined to be those of the Da Silva
    formula intersections. *)
Theorem inclusion_exclusion_principle :
    forall (a: A) (l: list (list A)),
    length (union l) = list_lengths_summed l - length (duplicates l).
Proof.
  intros.
  rewrite -> inclusion_exclusion_principle_alt.
  omega. assumption.
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

(** ==================================================== *)
(** Start of definitions and proofs for the Ruler Measure *)

(** list_mem returns the ith list in list l. *)
Definition list_list_mem (i: nat) (l: list (list A)) :
    list A := nth i l nil.

Require Import Rdefinitions Raxioms RIneq Rfunctions R_Ifp.

Local Open Scope nat_scope.
Local Open Scope R_scope.
Local Open Scope list_scope.

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
Lemma floor_size_div_c_le_size : forall a b c: R,
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
    apply floor_size_div_c_le_size.
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
  assumption. auto with *.
  assert (c <> 0). auto with *.
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
    auto with *.
  rewrite -> H5 in H6.
  assert (Rabs(M a b c - exact_size a b) < Rabs c).
    apply abs_M_minus_s_lt_abs_c. assumption.
  rewrite H3 in H6. revert H6. revert H7.
  apply Rlt_trans with
    (r1 := Rabs (M a b c - exact_size a b))
    (r2 := Rabs c)
    (r3 := epsilon).
Qed.

(** Defintion of a Epsilon-delta proof. *)
Hypothesis limit_x_L1_f_x_eq_L2 :
    forall (a b x L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    0 < delta /\ 0 < epsilon /\ g delta = epsilon /\
    0 < Rabs (x - L1) < delta /\
    Rabs(f a b x - L2) < epsilon ->
    f a b x = L2.

(* The function relating delta to epsilon to prove convergence. *)
Definition delta_eq_epsilon(d: R) : R := d.

(** Epsilon-delta proof. limit c->0,
    0 < |x - 0| < delta, |M - s| < epsilon -> M = s. *)
Lemma limit_c_0_M_eq_exact_size :
    forall (a b c L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\ L2 = exact_size a b /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    M a b c = exact_size a b.
Proof.
  intros. decompose [and] H.
  rewrite <- H2. rewrite <- H4.
  apply limit_x_L1_f_x_eq_L2 with (L1 := L1) (delta := delta)
      (epsilon := epsilon) (g := g).
  split. assumption. split. assumption.
  split.
  rewrite -> H1. unfold delta_eq_epsilon. assumption.
  split. split. assumption. assumption.
  rewrite -> H2. rewrite -> H4.
  apply M_minus_exact_size_lt_epsilon with (delta := delta).
  split. assumption. split. assumption. split. assumption.
  split. assumption. split.
  rewrite <- H3 at 2. assumption.
  rewrite <- H3. assumption.
Qed.

(** End RulerMeasure. *)

(** ================================================================ *)
(** Start of generic operations and proofs for lists of real numbers *)

(** If two natural numbers are equal than they are also equal
    as real numbers *)
Lemma eq_INR : forall (m n: nat), (m = n)%nat -> INR m = INR n.
Proof.
  simple induction 1; intros; auto with real.
Qed.

(** Returns the element at position i in the list. *)
Fixpoint list_rmem (i:nat) (l:list R) {struct l} : R :=
    match i, l with
    | O, _ => 0
    | S m, Datatypes.nil => 0
    | S m, h::t => list_rmem m t
    end.

(** r1^2 * r2^2 = (r1 * r2)^2 *)
Lemma rsqr_distributes :
    forall r1 r2: R, (Rsqr r1) * (Rsqr r2) = Rsqr (r1 * r2).
Proof.
  intros. unfold Rsqr. field.
Qed.

(** Raise a real number, r, to the n-th power. *)
Fixpoint Rpow (r: R) (n: nat) : R :=
    match n with
        | 0%nat => 1
        | S n' =>(r * Rpow r n')
    end.

(** r1^n * r2^n = (r1 * r2)^n *)
Hypothesis pow_distributes : forall (r1 r2: R) (n: nat),
    (Rpow r1 n) * (Rpow r2 n) = Rpow (r1 * r2) n.

(** Assume that if real number, r, exists then that number is
    the square some other real number, r'. *)
Hypothesis sqrt_exists :
    forall r: R, exists (r': R), r = r' * r'.

(** Two sets are equal if all the elements at the same
    positions are also equal. *)
Inductive eq_list_R : list R -> list R -> Prop :=
  | eq_list_R_nil : eq_list_R Datatypes.nil Datatypes.nil
  | eq_list_R_cons : forall (i: nat) (l1 l2: list R),
      list_rmem i l1 = list_rmem i l2 -> eq_list_R l1 l2.

(** Lists with same members at same positions are equal. *)
Hypothesis eq_list_R_is_eq : forall (l1 l2: list R),
    eq_list_R l1 l2 -> l1 = l2.

(** reflexivity on real-valued lists *)
Lemma list_refl : forall (l1 l2: list R), l1 = l2 -> l2 = l1.
Proof. auto. Qed.

(** Sum a list of real numbers. *)
Fixpoint sum_list (l: list R) : R :=
    match l with
      | Datatypes.nil => 0
      | a::l' => a + (sum_list l')
    end.

(** The cartesian product of a list of numbers. *)
Fixpoint cartesian_product (l: list R) : R :=
    match l with
        | Datatypes.nil => 1
        | hd::tl => hd * cartesian_product tl
    end.

(** Square each member of a list of real numbers. *)
Fixpoint sqr_list (l: list R) : list R :=
  match l with
    | Datatypes.nil => Datatypes.nil
    | a::l' => (Rsqr a)::(sqr_list l')
  end.

(** Specification of sqr_list. *)
Hypothesis sqr_list_spec : forall (i: nat) (a: R) (l: list R),
    (list_rmem i l) = a <-> list_rmem i (sqr_list l) = Rsqr a.

(** Multiply a list of real numbers by a number. *)
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

(** r^n * (a1 * a2 * ... * an) = (a1*r) * (a2*r) * ... * (an*r). *)
Hypothesis pow_distributes_over_cartesian_product :
    forall (l: list R) (r: R) (n: nat), n = length l ->
    (cartesian_product l) * Rpow r n = cartesian_product (mult_list l r).

(** End of generic operations and proofs on lists of real numbers *)

(** ================================================================ *)
(**
  Now the definitions and theorems about distance.
*)

(** List of the countable domain sets (x_i in X). *)
Variable list_x_i: list A.
(** List of countable domain sets, X = list(i=1 to n) list_x_i *)
Variable X: list (list A).
(** Xpd = union(i=1 to n) list_x_i *)
Variable Xpd: list A.
(** List of the countable distance sets (y_i in Y). *)
Variable list_y_i: list A.
(** List of countable image sets, Y = union(i=1 to n) list_y_i *)
Variable Y: list (list A).
(** Countable distance is cardinal of Y = union(y_i). *)
Variable d_c: R.
(** Counters *)
Variables i n: nat.

(**
  The countable distance range is based on the defintion in
  the article, The Real Analysis and Combinatorics of Geometry.
*)
Hypothesis countable_distance_range :
    (* For each domain set, list_x_i in X, there exists a
       corresponding distance set, list_y_i in Y. *)
    (i <= n)%nat /\ length X = n /\ length Y = n /\
    (* list_x_i is the i_th domain set in X *)
    list_x_i = list_list_mem i X /\
    (* Disjoint domain sets *)
    length (union X) = length (lists_appended X) /\
    (* list_y_i is the i_th distance set in Y *)
    list_y_i = list_list_mem i Y /\
    (* The i_th domain set has the same number of elements as
       the i_th distance set. *)
    length list_x_i = length list_y_i /\
    (* The distance sets sometimes intersect expressed here as
       the sum of the union of distance set less than and
       equal to the size of sum distance set sizes. *)
    INR (length (union Y)) < INR (length (lists_appended Y)) /\
    INR (length (union Y)) = INR (length (lists_appended Y)) /\
    (* The countable distance, d_c, is the size of the
       union of the distance sets. *)
    d_c = INR (length (union Y)%nat).

(** Partition the domain intervals into sets (lists of
    elements). And save the cardinal (number of elements in
    each domain interval) in the list of cardinals, p. *)

(** The boundaries of a domain interval, [a_i,b_i},
   i in [1,n]). *)
Variables a_i b_i: R.
(** The list of the exact size of each interval,
    [a_i,b_i}, i in [1,n]). *)
Variable s: list R.
(** The boundaries of the image (distance) interval, [d_0,d_m]. *)
Variables d_0 d_m: R.
(* The real-valued size of the distance interval [d_0,d_m]. *)
Variable d: R.

(** From the ruler measure, these are exact
    sizes of the domain and image intervals that the
    subintervals must be shown to converge to. *)
Hypothesis exact_sizes :
    list_rmem i s = exact_size a_i b_i /\
    d = exact_size d_0 d_m.

(** The list of cardnals corresponding to each list_x_i (the
    number of elements in the intervals [a_i,b_i},
    i in [1,n]). *)
Variable p: list R.
(** The ruler interval size. *)
Variable c: R.

(** Step 3.1, 3.2 of taxicab distance proof are the first steps
    of the taxic distance proof in the article, The Real Analysis
    and Combinatorics of Geometry.
    Definitions of domain and image subintervals that are
    used in both taxicab (Manhattan) and Euclidean distance
    proofs. *)
Hypothesis ruler_subintervals :
    c > 0 /\
    subintervals a_i b_i c = INR (length list_x_i) /\
    list_rmem i p = subintervals a_i b_i c /\
    subintervals d_0 d_m c = d_c.

(** The following lemmas are steps in the proof of
   taxicab distance. *)

(** Step 3.3 of taxicab distance proof.
    From the countable_distance_range definition:
    d_c = sum(i=1,n) cardinal(y_i)
        = union(i=1,n) cardinal(y_i).*)
Hypothesis d_c_sum_disjoint :
    d_c = sum_list (p).

(** The next lemma is the first proof step of the
   taxicab and Euclidean distance proofs in the article,
   The Real Analysis and Combinatorics of Geometry. *)

(** Map the set-based cardinal relationship,
   |x_i| = |y_i| = p_i, into the list of
   partition counts, p. *)
Lemma mem_list_p_eq_list_yi :
    list_rmem i p = subintervals a_i b_i c.
Proof.
  intros.
  decompose [and] ruler_subintervals.
  assumption.
Qed.

(** Step 3.4 of taxicab distance proof:
    Multiply both sides of step 3.2 by c and
    apply the ruler measure and covergence theorem. *)
Lemma domain_d_measure :
    forall (L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    d_c * c = sum_list (s).
Proof.
  intros. decompose [and] H.
  decompose [and] exact_sizes. decompose [and] ruler_subintervals.
  apply mult_list_spec with (l := p)
      (a := subintervals a_i b_i c) (r := c) in H12.
  rewrite <- subintervals_times_c_eq_measure in H12.
  rewrite -> limit_c_0_M_eq_exact_size with
          (a := a_i) (b := b_i) (c := c)  (L1 := L1)
          (g := g) (delta := delta) (epsilon := epsilon)
          (L2 := exact_size a_i b_i) (f := M) in H12.
  rewrite <- H12 in H8.
  apply eq_list_R_cons in H8.
  apply eq_list_R_is_eq in H8.
  rewrite -> d_c_sum_disjoint.
  rewrite -> mult_distributes_over_sum_list with
      (l := p) (r := c).
  rewrite <- H8.
  reflexivity.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption. assumption. assumption. 
Qed.

(** Step 3.5 of taxicab distance proof:
    There is one overall set of Y, containing d_c
    number of subintervals. Therefore, the number of all
    y in Y, is (subintervals d_0 d_m c) = d_c. *)
Hypothesis d_c_eq_image_subintervals :
    d_c = subintervals d_0 d_m c.

(** Step 3.6 of taxicab distance proof:
    Multiply both sides of step 3.4 by c and apply the
    ruler measure and convergence theorem to get the
    distance measure. *)
Lemma d_measure :
    forall (L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    d = d_c * c.
Proof.
  intros. decompose [and] H.
  decompose [and] exact_sizes. decompose [and] ruler_subintervals.
  rewrite -> H10.
  rewrite <- limit_c_0_M_eq_exact_size with
      (a := d_0) (b := d_m) (c := c)  (L1 := L1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (L2 := exact_size d_0 d_m) (f := M).
  unfold M.
  rewrite <- d_c_eq_image_subintervals.
  reflexivity.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption. assumption.
Qed.

(** The final step in the taxicab distance proof.
    Step 3.7: Combine steps 3.6 and 3.4. *)
Theorem taxicab_distance :
    forall (L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    d = sum_list (s).
Proof.
  intros. decompose [and] H.
  decompose [and] exact_sizes. decompose [and] ruler_subintervals.
  assert (d_c * c = sum_list (s)).
      revert H.
      apply domain_d_measure. assumption.
  assert (d = d_c * c).
      revert H.
      apply d_measure. assumption.
  rewrite -> H14 in H16.
  assumption.
Qed.

(** The following lemmas are steps in the proof of
   Euclidean distance. *)

(** Step 3.8 is the first step of the Euclidean distance
    proof in the article, The Real Analysis and Combinatorics
    of Geometryand and is also the first step of the previous
    taxicab distance proof. This step is defined previously in
    the taxicab distance proof as:
    "Hypothesis ruler_subintervals" *)

(** Step 3.9 (second step) of the Euclidean distanc proof:
   Map the set-based cardinal relationship,
   |x_i|*|y_i| = p_i^2 = |y_i|^2, into the list of
   partition counts, p. *)
Lemma mem_sqr_list_p_eq_prod_list_yi_list_yi :
    list_rmem i (sqr_list p) = Rsqr (subintervals a_i b_i c).
Proof.
  intros.
  decompose [and] countable_distance_range.
  decompose [and] ruler_subintervals.
  rewrite -> sqr_list_spec in H10. assumption.
Qed.

(** Step 3.10 Cauchy-Schwartz inequality:
    sum(i=1,n) |y_i|^2 <= (sum(i=1,n) |y_i|)^2. *)
Hypothesis cauchy_schwartz_inequality :
    sum_list (sqr_list p) < Rsqr (sum_list (p)) /\
    sum_list (sqr_list p) = Rsqr (sum_list (p)).

(** Step 3.11: From the countable distance theorem,
    choose the equality case
    squaring both sides of the inequality:
    sum(i=1,n) |y_i| >= |union(i=1,n) y_i| = d_c =>
    (sum(i=1,n) |y_i|)^2 >= d_c^2.
    Choose the equality case and square each side:
    sum(i=1,n) |y_i|^2 >= d_c^2. *)
Lemma square_of_sum_eq_d_c :
    Rsqr d_c = Rsqr (sum_list (p)).
Proof.
  intros. rewrite <- d_c_sum_disjoint. reflexivity.
Qed.

(** Step 3.12: Combine 3.10 (equality case of the Cauchy-Schwartz
    inequality) and 3.11 (square of sum case).
    d_c^2 = sum(i=1,n) p_i^2. *)
Lemma sqr_d_c_eq_sum_squares :
    Rsqr d_c = sum_list (sqr_list p).
Proof.
  intros.
  decompose [and] cauchy_schwartz_inequality.
  symmetry.
  rewrite -> H0.
  symmetry.
  apply square_of_sum_eq_d_c.
Qed.

(** For econvenience in the following proof steps, create the
    variable sqr_d_c = Rsqr d_c. *)
Variable sqr_d_c: R.
(** From the lemma, sqr_d_c_eq_sum_squares, sqr_d_c = Rsqr d_c =>
    sqr_d_c = sum_list (sqr_list p). *)
Hypothesis sqr_d_c_sum_squares :
    sqr_d_c = sum_list (sqr_list p).

(** Step 3.13: Multiply both sides of step 3.12 by Rsqr c and
    apply the ruler measure and covergence theorem. *)
Lemma domain_d_c_measure :
    forall (L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    sqr_d_c * Rsqr c = sum_list (sqr_list s).
Proof.
  intros. decompose [and] H.
  decompose [and] exact_sizes. decompose [and] ruler_subintervals.
  assert (sqr_d_c * Rsqr c = sum_list (mult_list (sqr_list p) c²)).
      rewrite <- mult_distributes_over_sum_list.
      apply Rmult_eq_compat_r with (r := Rsqr (c))
          (r1 := sqr_d_c)
          (r2 := sum_list (sqr_list p)).
      assumption.
  rewrite <- limit_c_0_M_eq_exact_size with
          (a := a_i) (b := b_i) (c := c)  (L1 := L1)
          (g := g) (delta := delta) (epsilon := epsilon)
          (L2 := exact_size a_i b_i) (f := M) in H8.
  unfold M in H8.
  assert (list_rmem i (sqr_list s) = Rsqr (subintervals a_i b_i c * c)).
      apply sqr_list_spec with
          (l := s) (a := subintervals a_i b_i c * c).
      assumption.
  assert (list_rmem i (sqr_list p) = Rsqr (subintervals a_i b_i c)).
      apply sqr_list_spec with
          (l := p) (a := subintervals a_i b_i c).
      assumption.
  apply mult_list_spec with (l := sqr_list p)
      (a := Rsqr (subintervals a_i b_i c)) (r := Rsqr c) in H17.
  rewrite -> rsqr_distributes in H17.
  rewrite <- H16 in H17.
  apply eq_list_R_cons in H17. apply eq_list_R_is_eq in H17.
  rewrite -> H17 in H14.
  assumption.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption. assumption. 
Qed.

(** Step 3.14:
    d_c = subintervals d_0 d_m c =>
          sqr_d_c = Rsqr (subintervals d_0 d_m c) *)
Hypothesis sqr_d_c_eq_rsqr_image_subintervals :
    sqr_d_c = Rsqr (subintervals d_0 d_m c).

(** Step 3.15: Multiply both sides of step 3.13 by Rsqr c and
    apply the ruler measure and convergence theorem to get
    the distance measure. *)
Lemma rsqr_d_measure :
    forall (L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    Rsqr d = sqr_d_c * Rsqr c.
Proof.
  intros. decompose [and] H.
  decompose [and] exact_sizes. decompose [and] ruler_subintervals.
  rewrite -> H10.
  rewrite <- limit_c_0_M_eq_exact_size with
      (a := d_0) (b := d_m) (c := c)  (L1 := L1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (L2 := exact_size d_0 d_m) (f := M).
  unfold M.
  rewrite <- rsqr_distributes.
  apply Rmult_eq_compat_r with (r := Rsqr (c))
      (r1 := Rsqr (subintervals d_0 d_m c))
      (r2 := sqr_d_c).
  symmetry. apply sqr_d_c_eq_rsqr_image_subintervals.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption. assumption.
Qed.

(** Step 3.16: combine steps 3.15 and 3.13. *)
Theorem Euclidean_distance :
    forall (L1 L2 delta epsilon:R)
        (f: R->R->R->R) (g: R->R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    Rsqr d = sum_list (sqr_list s).
Proof.
  intros. decompose [and] H.
  decompose [and] exact_sizes. decompose [and] ruler_subintervals.
  assert (sqr_d_c * Rsqr c = sum_list (sqr_list s)).
      revert H.
      apply domain_d_c_measure. assumption.
  assert (Rsqr d = sqr_d_c * Rsqr c).
      revert H.
      apply rsqr_d_measure. assumption.
  rewrite -> H14 in H16.
  assumption.
Qed.

(** ======================================= *)

(** The countable size (length/area/volume) of a set of
    image elements. *)
Variable S_c: R.
(** The boundaries of the image (size) interval, [v_0,v_m]. *)
Variables v_0 v_m: R.

(**
  A countable size measure of a list of domain sets:
  forall i in [1,n], y'_i in ith set of Y in 
  intersection X = empty_set /\ intersection Y = exmpty_set /\
  cardinal of ith set of X = cardinal ith set of Y /\
  p_i = cardinal of ith set of Y ->
  size, S_c = |{(y'_1,...,y'_n)}|=|list_y_1|*...*|list_y_n|.
*)
Hypothesis countable_size_measure :
    (i <= n)%nat /\ length X = n /\ length Y = n /\
    duplicates X = empty_list /\
    S_c = cartesian_product p.

(** The Euclidean Size (length/area/volume) theorem:
    Sz, is the size of a interval, [y_{0},y_{m}],
    corresponding to a set of real-valued intervals:
    {[x_{0,1},x_{m,1}], [x_{0,2},x_{m,2}],...,[x_{0,n},x_{m,n}]},
    where:
    Sz = cartesian_product(i=1 to n) s_i /\
    Sz = v_{m} - v_{0} /\
    s_i = x_{m,i} - x_{0,i}. *)
Theorem Euclidean_size :
    forall (L1 L2 delta epsilon p_S Sz r r_0 r_m: R)
        (f: R->R->R->R) (g: R->R), exists (r': R),
    c > 0 /\
    f = M /\ g = delta_eq_epsilon /\
    L1 = 0 /\
    0 < delta /\ 0 < epsilon /\ delta = epsilon /\
    0 < Rabs (c - L1) < delta ->
    n = length s /\ length p = n /\
    list_rmem i s = exact_size a_i b_i /\
    list_rmem i p = subintervals a_i b_i c /\
    Sz = exact_size v_0 v_m /\
    Sz = Rpow r' n /\
    r = exact_size r_0 r_m /\
    p_S = subintervals r_0 r_m c /\
    Rpow p_S n = S_c ->
    Sz = cartesian_product s.
Proof.
  intros. exists (x := r). intros.
  decompose [and] countable_size_measure. decompose [and] H.
  decompose [and] H0.
  rewrite -> H6 in H24.
  assert (Rpow p_S n * Rpow c n = cartesian_product p * Rpow c n).
      rewrite <- H24. reflexivity.
  rewrite -> pow_distributes in H23.
  rewrite -> pow_distributes_over_cartesian_product in H23.
  rewrite -> H22 in H23.
  rewrite <- subintervals_times_c_eq_measure in H23.
  rewrite -> limit_c_0_M_eq_exact_size with
      (a := r_0) (b := r_m) (c := c) (L1 := L1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (L2 := exact_size r_0 r_m) (f := M) in H23.
  rewrite <- H21 in H23.
  rewrite <- H20 in H23.
  apply mult_list_spec with (l := p)
      (a := subintervals a_i b_i c) (r := c) in H18.
  rewrite <- subintervals_times_c_eq_measure in H18.
  rewrite -> limit_c_0_M_eq_exact_size with
      (a := a_i) (b := b_i) (c := c) (L1 := L1)
      (g := g) (delta := delta) (epsilon := epsilon)
      (L2 := exact_size a_i b_i) (f := M) in H18.
  rewrite <- H16 in H18.
  apply eq_list_R_cons with  (l1 := mult_list p c) (l2 := s) in H18.
  apply eq_list_R_is_eq in H18.
  rewrite -> H18 in H23.
  assumption.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption. assumption. assumption.
  split. assumption. split. reflexivity. split. assumption.
  split. assumption. split. reflexivity.
  split. assumption. split. assumption. split. assumption.
  split. assumption. assumption. 
  assumption.
  symmetry. assumption.
Qed.

End EuclideanRelations.