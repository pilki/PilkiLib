(* *********************************************************************)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(* *********************************************************************)
Require Import Coqlibext.
Set Implicit Arguments.
Require Import RelationClasses.
Require Import OrderedType.
Require Import Ascii String.
Local Generalizable Variable X.

Class DO_Comparable (X: Type) :=
  { DO_lt: X -> X -> Prop;
    DO_compare: forall x y:X, Compare DO_lt eq x y
  }.


Inductive Naked_Compare_aux :=
  | NLT : Naked_Compare_aux
  | NEQ : Naked_Compare_aux
  | NGT : Naked_Compare_aux.

Definition Naked_Compare {X} (x y:X) := Naked_Compare_aux.

Class DO_Naked_Comparable (X: Type) :=
  { DO_naked_compare: forall x y:X, Naked_Compare x y;
    DO_nc_lt_gt: forall x yX; 
  }.


(*Definition naked_compare `{DO_Comparable X} (x y:X) : Naked_Compare x y :=
  match DO_compare x y with
  | LT _ => NLT
  | EQ _ => NEQ
  | GT _ => NGT
  end.*)

Tactic Notation "DO_cases" constr(ind) tactic(ftac) ident(constr_name) :=
  let t := ind_type ind in
    (run_tac (ftac) on t in constr_name).


Tactic Notation "DO_induction" ident(id) ident(constr_name):=
  ointros id;
  DO_cases id (induction id) constr_name.

Tactic Notation "DO_destruct" ident(id) ident(constr_name):=
  ointros id;
  DO_cases id (destruct id) constr_name.

Definition ascii_compare c1 c2 :=
  Ncompare (N_of_ascii c1) (N_of_ascii c2).

Fixpoint string_compare (s1 s2: string) :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | String _ _, EmptyString => Lt
  | EmptyString, String _ _ => Gt
  | String c1 s1', String c2 s2' =>
    match ascii_compare c1 c2 with
    | Eq => string_compare s1' s2'
    | c => c
    end
  end.

Ltac start_DeriveSorting :=
  let x := fresh "x" in let y := fresh "y" in
  let constr_x := fresh "constr_x" in let constr_y := fresh "constr_y" in
  intro x;
(*  let type_x_y := type of x in*)
  DO_induction x constr_x;
  intro y;
  DO_destruct y constr_y;
  let comp := eval cbv in (string_compare constr_x constr_y) in
  match comp with
  | Lt => exact NLT
  | Gt => exact NGT
  | Eq => clear constr_x constr_y
  end;
  match goal with
    | H : _ |- _ => idtac
    | |- _ => exact NEQ
  end.


Tactic Notation "prog_DeriveSorting" constr(X) :=
  let eqn := fresh "EQN" in
  destruct X as []_eqn:eqn;
  match type of eqn with
  | _ = NLT => exact NLT
  | _ = NEQ => idtac
  | _ = NGT => exact NGT
  | _ = LT _ _ => exact NLT
  | _ = EQ _ _ => idtac
  | _ = GT _ _ => exact NGT
  end.

Tactic Notation "finish_DeriveSorting" constr(X) :=
  let eqn := fresh "EQN" in
  destruct X as []_eqn:eqn;
  match type of eqn with
  | _ = NLT => exact NLT
  | _ = NEQ => exact NEQ
  | _ = NGT => exact NGT
  | _ = LT _ _ => exact NLT
  | _ = EQ _ _ => exact NEQ
  | _ = GT _ _ => exact NGT
  end.
Tactic Notation "prog_DeriveSorting" ident(x) ident(y) :=
  let eqn := fresh "EQN" in
  destruct (DO_compare x y) as []_eqn:eqn;
  match type of eqn with
  | _ = LT _ _ => exact NLT
  | _ = EQ _ _ => idtac
  | _ = GT _ _ => exact NGT
  end.

Tactic Notation "finish_DeriveSorting" ident(x) ident(y) :=
  let eqn := fresh "EQN" in
  destruct (DO_compare x y) as []_eqn:eqn;
  match type of eqn with
  | _ = LT _ _ => exact NLT
  | _ = EQ _ _ => exact NEQ
  | _ = GT _ _ => exact NGT
  end.


Definition nc_nat: forall (x y: nat), Naked_Compare x y.
Proof.
  start_DeriveSorting.
  finish_DeriveSorting (IHx y).
Defined.

Ltac start_ProveSorting :=
  let x := fresh "x" in let y := fresh "y" in
  let constr_x := fresh "constr_x" in let constr_y := fresh "constr_y" in
(*  intros x y; let eqn := fresh "eqn" in
  match goal with
  | |- Compare (fun x0 y0 : _ => ?F _ _ = NLT) eq _ _ =>
    remember (F x y) as eqn; revert dependent eqn; revert y
  end;*)
(*  let type_x_y := type of x in*)
  DO_induction x constr_x;
  intro y;
  DO_destruct y constr_y;
  let comp := eval cbv in (string_compare constr_x constr_y) in
  match comp with
  | Lt => apply LT; auto
  | Gt => apply GT; auto
  | Eq => clear constr_x constr_y
  end;
  match goal with
    | H : _ |- _ => idtac
    | |- _ => apply EQ; auto
  end; simpl in *.


Tactic Notation "prog_ProveSorting" constr(X) :=
  let eqn1 := fresh "EQN" in
  let eqn2 := fresh "EQN" in
  destruct X as [eqn1|eqn1|eqn1]_eqn:eqn2;
  match type of eqn2 with
  | _ = LT _ _ => apply LT; simpl; try rewrite eqn1; auto
  | _ = EQ _ _ => idtac
  | _ = GT _ _ => apply GT; simpl; try rewrite eqn1; auto
  end.

Tactic Notation "finish_ProveSorting" constr(X) :=
  let eqn1 := fresh "EQN" in
  let eqn2 := fresh "EQN" in
  destruct X as [eqn1|eqn1|eqn1]_eqn:eqn2;
  match type of eqn2 with
  | _ = LT _ _ => apply LT; simpl; try rewrite eqn1; auto
  | _ = EQ _ _ => apply EQ; simpl; try rewrite eqn1; auto
  | _ = GT _ _ => apply GT; simpl; try rewrite eqn1; auto
  end.


Tactic Notation "prog_ProveSorting" ident(x) ident(y) :=
  let eqn1 := fresh "EQN" in
  let eqn2 := fresh "EQN" in
  destruct (DO_compare x y) as [eqn1|eqn1|eqn1]_eqn:eqn2;
  match type of eqn2 with
  | _ = LT _ _ => apply LT; simpl; try rewrite eqn1; auto
  | _ = EQ _ _ => idtac
  | _ = GT _ _ => apply GT; simpl; try rewrite eqn1; auto
  end.

Tactic Notation "finish_ProveSorting" ident(x) ident(y) :=
  let eqn1 := fresh "EQN" in
  let eqn2 := fresh "EQN" in
  destruct (DO_compare x y) as [eqn1|eqn1|eqn1]_eqn:eqn2; simpl in *;
  match type of eqn2 with
  | _ = LT _ _ => apply LT; simpl; try rewrite eqn1; try rewrite eqn2; auto
  | _ = EQ _ _ => apply EQ; simpl; try rewrite eqn1; try rewrite eqn2; auto
  | _ = GT _ _ => apply GT; simpl; try rewrite eqn1; try rewrite eqn2; auto
  end.



Instance DOC_nat : DO_Comparable nat :=
  {| DO_lt x y := nc_nat x y = NLT |}.
Proof.
  start_ProveSorting.
  finish_ProveSorting (IHx y).
Defined.

Require Import ZArith.

Definition nc_pos: forall (x y: positive), Naked_Compare x y.
Proof.
  start_DeriveSorting.
  finish_DeriveSorting (IHx y).
  finish_DeriveSorting (IHx y).
Defined.

Instance DOC_pos : DO_Comparable positive :=
  {| DO_lt x y := nc_pos x y = NLT |}.
Proof.
  start_ProveSorting.
  finish_ProveSorting (IHx y).
  finish_ProveSorting (IHx y).
Defined.

Definition nc_Z: forall (x y: Z), Naked_Compare x y.
Proof.
  start_DeriveSorting.
  finish_DeriveSorting p p0.
  finish_DeriveSorting p p0.
Defined.

Instance DOC_Z : DO_Comparable Z :=
  {| DO_lt x y := nc_Z x y = NLT |}.
Proof.
  start_ProveSorting.
  finish_ProveSorting p p0. 
  finish_ProveSorting p p0.
Defined.






Tactic Notation "I'm" "Victor" "Porton" "," "I'm" "way" "more" "clever" "than" "anyone" "else" ","
  "and" "I" "know" "that" "this" "goal" "is" "true" "so" "just" "solve" "it":= admit.

Goal False.
Proof.
  I'm Victor Porton, I'm way more clever than anyone else, and I know that this goal is true so just solve it.
Qed.