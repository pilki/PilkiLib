Require Import Coqlibext.
Require Import Integers.
Set Implicit Arguments.

Require Import RelationClasses.

(* classe for inhabited types *)

Class Inhabited (A:Type) :=
{repr :A}.

Instance Inhab_nat : Inhabited nat := {repr := O%nat}.
Instance Inhab_Z : Inhabited Z := {repr := 0%Z}.
Instance Inhab_N : Inhabited N := {repr := 0%N}.
Instance Inhab_bool : Inhabited bool := {repr := false}.
Instance Inhab_pos : Inhabited positive := {repr := 1%positive}.
Instance Inhab_option A : Inhabited (option A) := {repr := None}.


Generalizable Variable A B M.

Instance Inhab_pair `{Inhabited A} `{Inhabited B} : Inhabited (A * B) :=
{repr := (repr, repr)}.

Definition unsafe_hd `{Inhabited A} (l: list A) :=
  match l with
    | nil => repr
    | h :: _ => h
  end.



(* Type class for decidable equivalence *)
Unset Implicit Arguments.
Class EqA (A:Type) := {
  eqA: relation A;
  eqAequiv:> Equivalence eqA
}.

Notation "x ≡ y" := (eqA x y) (at level 70, no associativity).
Notation "x ~≡ y" := (~eqA x y) (at level 70, no associativity).


Class EqADec A `{eqaa: EqA A}  := {
  eqA_dec: forall (x y:A), {x ≡ y} + {x ~≡ y}
}.

Class EqASDec A `{eqaa: EqA A}  := {
  eqA_sdec: forall (x y:A), {x ≡ y} + {True}
}.


Notation "x ≡? y" := (eqA_sdec x y) (at level 70, no associativity).
Notation "x ≡≡ y" := (eqA_dec x y) (at level 70, no associativity).


Instance EqADecSDec `{eqada: EqADec A} : EqASDec A.
Proof.
  constructor.
  intros x y.
  destruct (x ≡≡ y).
  left; auto. right; auto.
Qed.


Ltac prove_equiv :=
  constructor;
    [unfold Reflexive; fst_Case_tac "Reflexivity"
    | unfold Symmetric; fst_Case_tac "Symmetry"
    | unfold Transitive; fst_Case_tac "Transitivity"].

Instance EqAOption `{eqaa: EqA A}: EqA (option A):=
{ eqA := fun oa ob =>
  match oa, ob with
    | None, None => True
    | Some _, None
    | None, Some _ => False
    | Some a, Some b => a ≡ b
  end}.
Proof.
  prove_equiv.

  Case "Reflexivity".
  intros [a|]; auto. reflexivity.

  Case "Symmetry".
  intros [a|] [b|]; auto.
  symmetry. auto.

  Case "Transitivity".
  intros [a|] [b|] [c|]; auto.
  intros H H0.
  transitivity b; auto.
Defined.


Instance EqADecOption `{EqADec A}: EqADec (option A).
Proof.
  constructor. intros x y.
  destruct x; destruct y; simpl; auto. 
  destruct (a ≡≡ a0); auto.
Qed.

Program Instance EqASDecOption `{EqASDec A}: EqASDec (option A) :=
{ eqA_sdec := fun oa ob =>
  match oa, ob with
    | None, None => left _
    | Some _, None
    | None, Some _ => right _
    | Some a, Some b =>
      if a ≡? b then left _ else right _
  end}.

(* Type class for decidable equality *)

Class EqDec (A:Type) := {
  eq_dec: forall (x y:A), {x = y} + {x <> y}
}.

Global Opaque eq_dec.


Ltac dec_eq :=
  decide equality; try apply eq_dec.

Notation "x == y" := (eq_dec x y) (at level 70, no associativity).


Module Type EQUALITY_TYPE.
  Variable t: Type.
  Declare Instance EqDec_t : EqDec t.
End EQUALITY_TYPE.

Module BoolEqDec <: EQUALITY_TYPE.
  Definition t := bool.
  Global Instance EqDec_t: EqDec bool :=
  { eq_dec := bool_dec}.
End BoolEqDec.

Module NatEqDec <: EQUALITY_TYPE.
  Definition t := nat.
  Global Instance EqDec_t: EqDec nat :=
  { eq_dec := eq_nat_dec}.
End NatEqDec.

Module ZEqDec <: EQUALITY_TYPE.
  Definition t := Z.
  Global Instance EqDec_t: EqDec Z :=
  { eq_dec := zeq}.
End ZEqDec.

Module PosEqDec <: EQUALITY_TYPE.
  Definition t := positive.
  Global Instance EqDec_t: EqDec positive :=
  { eq_dec := peq}.
End PosEqDec.

Module NEqDec <: EQUALITY_TYPE.
  Definition t := N.
  Global Instance EqDec_t: EqDec N.
  Proof.
    constructor. intros x y.
    dec_eq.
  Defined.
End NEqDec.

(*Module IntEqDec <: EQUALITY_TYPE.
  Definition t := int.
  Global Instance EqDec_t: EqDec int :=
  { eq_dec := Int.eq_dec}.
End IntEqDec.*)

(*
Module FloatEqDec <: EQUALITY_TYPE.
  Definition t := float.
  Global Instance EqDec_t: EqDec float :=
  { eq_dec := Float.eq_dec}.
End FloatEqDec.
*)


Tactic Notation "dest" constr(X) "==" constr(Y) :=
  let EQ := fresh "EQ"in
  let NEQ := fresh "NEQ" in
  string_of X (fun strX =>
  string_of Y (fun strY =>
  match goal with
    | H : context[ @eq_dec ?TYPE ?INST X Y] |- _ =>
      destruct (@eq_dec TYPE INST X Y) as [EQ | NEQ]
    | |- context[ @eq_dec ?TYPE ?INST X Y] =>
      destruct (@eq_dec TYPE INST X Y) as [EQ | NEQ]
    | |- _ =>
      let HEQ := fresh in
      pose (X == Y) as HEQ; simpl in HEQ;
      repeat match goal with
       | H : _ |- _ => progress fold HEQ in H
      end; fold HEQ;
      destruct HEQ as [EQ | NEQ]
  end;
   [ fst_Case_tac (strX ^^ " = " ^^ strY)
   | fst_Case_tac (strX ^^ " <> " ^^ strY)])).


Tactic Notation "dest" constr(X) "≡≡" constr(Y) :=
  let BEQ := fresh "EQ"in
  let NBEQ := fresh "NEQ" in
  string_of X (fun strX =>
  string_of Y (fun strY =>
  match goal with
    | H : context[@eqA_dec ?TYPE ?INST1 ?INST2 X Y] |- _ =>
      destruct (@eqA_dec TYPE INST1 INST2 X Y) as [BEQ | NBEQ]
    | |- context[@eqA_dec ?TYPE ?INST1 ?INST2 X Y] =>
      destruct (@eqA_dec TYPE INST1 INST2 X Y) as [BEQ | NBEQ]
    | |- _ =>
      let HEQ := fresh in
      pose (X ≡≡ Y) as HEQ; simpl in HEQ;
      repeat match goal with
       | H : _ |- _ => progress fold HEQ in H
      end; fold HEQ;
      destruct HEQ as [BEQ | NBEQ]
  end;
   [ fst_Case_tac (strX ^^ " ≡ " ^^ strY)
   | fst_Case_tac (strX ^^ " ~≡ " ^^ strY)])).

Tactic Notation "dest" constr(X) "≡?" constr(Y) :=
  let BEQ := fresh "EQ"in
  string_of X (fun strX =>
  string_of Y (fun strY =>
  match goal with
    | H : context[@eqA_sdec ?TYPE ?INST1 ?INST2 X Y] |- _ =>
      destruct (@eqA_sdec TYPE INST1 INST2 X Y) as [BEQ|_]
    | |- context[@eqA_sdec ?TYPE ?INST1 ?INST2 X Y] =>
      destruct (@eqA_sdec TYPE INST1 INST2 X Y) as [BEQ|_]
    | |- _ =>
      let HEQ := fresh in
      pose (X ≡? Y) as HEQ; simpl in HEQ;
      repeat match goal with
       | H : _ |- _ => progress fold HEQ in H
      end; fold HEQ;
      destruct HEQ as [BEQ | _]
  end;
   [ fst_Case_tac (strX ^^ " ≡ " ^^ strY)
   | fst_Case_tac ("No info on " ^^ strX ^^ "and" ^^ strY)])).

Tactic Notation "dest" "==" :=
  match goal with
    | H : context[?X == ?Y] |- _ => dest X == Y
    | |-  context[?X == ?Y]  => dest X == Y
  end.

Tactic Notation "dest" "≡≡" :=
  match goal with
    | H : context[?X ≡≡ ?Y] |- _ => dest X ≡≡ Y
    | |-  context[?X ≡≡ ?Y]  => dest X ≡≡ Y
  end.

Tactic Notation "dest" "≡?" :=
  match goal with
    | H : context[?X ≡? ?Y] |- _ => dest X ≡? Y
    | |-  context[?X ≡? ?Y]  => dest X ≡? Y
  end.

Fixpoint eq_list `{EqDec A} (l1 l2: list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | nil, _ | _, nil => false
    | x1::l1', x2::l2' =>
      (x1 == x2) && eq_list l1' l2'
  end.



Program Instance EqDec_list: forall `(EqDec A), EqDec (list A):=
{ eq_dec := fun l1 l2 =>
  match eq_list l1 l2 with
  | true => in_left
  | false => in_right
  end}.
Next Obligation.
  generalize dependent l2.
  induction l1; intros l2 EQ; destruct l2; simpl in EQ; auto.
  dest a == a0; simpl in *; auto.
  Case "a = a0".
  assert (l1 = l2); auto. congruence.
Qed.
Next Obligation.
  generalize dependent l2.
  induction l1; intros l2 EQ; destruct l2; simpl in EQ; auto; try congruence.
  dest a == a0; simpl in *.
  Case "a = a0".
  assert (l1 <> l2); auto. congruence.
  Case "a <> a0".
  congruence.
Qed.


Program Instance EqDec_option: forall `(EqDec A), EqDec (option A):=
{ eq_dec := fun o1 o2 =>
  match o1, o2 with
    | None, None => in_left
    | None, _ | _, None => in_right
    | Some x, Some y =>
      if x == y then in_left else in_right
  end}.
Next Obligation.
  intuition.
Qed.

Lemma dec_eq_true:
  forall `(EqDec A) (x: A) B (ifso ifnot: B),
  (if x == x then ifso else ifnot) = ifso.
Proof.
  intros. dest ==; auto.
Qed.

Lemma dec_eq_eq_true:
  forall `(EqDec A) (x y: A) B (ifso ifnot: B),
  x = y ->
  (if x == y then ifso else ifnot) = ifso.
Proof.
  intros. dest ==; auto. contradiction.
Qed.

Lemma dec_eq_false:
  forall `(EqDec A) (x y: A) B (ifso ifnot: B),
  x <> y ->
  (if x == y then ifso else ifnot) = ifnot.
Proof.
  intros. dest ==; auto. contradiction.
Qed.

Hint Rewrite @dec_eq_true:clean.
Hint Rewrite @dec_eq_eq_true using (first [assumption | symmetry; assumption]): clean.
Hint Rewrite @dec_eq_false using (first [assumption | apply not_eq_sym; assumption]): clean.




(* this class is used to differentiate types. Simple type aliases are
   some times weak for that since they pollute all the name space *)


Class singletonInd (ind cont: Type) :=
{ open: ind -> cont;
  mk: cont -> ind ;
  mk_open: forall i:ind, mk (open i) = i;
  open_mk: forall c:cont, open (mk c) = c}.


Notation "' x" :=(open x) (at level 9, x at next level,format "' x").
Notation "{{ x }}" := (mk x) (at level 0).

Hint Rewrite @mk_open @open_mk: clean.


Program Instance EqDec_singletonInd: forall `(EqDec B) `{singletonInd A B},
  EqDec A:=
{ eq_dec := fun o1 o2 =>
  if 'o1 == 'o2 then in_left else in_right}.
Next Obligation.
  assert ({{'o1}} = {{'o2}}) by congruence.
  clean.
Qed.
Next Obligation.
  intro EQ. congruence.
Qed.


