Require Export Coqlib_compcert.
Require Import RelationClasses.
Require Export Case_Tactics.
Require Export Program.
Create HintDb clean.
Generalizable Variable A B.

(*Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].*)


Set Implicit Arguments.

Ltac inv H := inversion H; try subst; try clear H.

Definition Decidable (P:Prop) := {P} + {~P}.
Hint Unfold Decidable: autounfold.

(** the hint base autounfold allows to register definition that should
   often be automatically unfolded*)

Tactic Notation "unfold*" := autounfold with autounfold in *.


(** [list_forall P [x1 ... xN] holds iff [P xi] holds for all [i]. *)
Section FORALL.
  Variable A: Type.
  Variable P: A -> Prop.

  Inductive list_forall: list A -> Prop :=
  | list_forall_nil: list_forall nil
  | list_forall_cons: forall a al, P a -> list_forall al -> list_forall (a::al).

  (* if the property holds for all elements In the list, then
  list_forall holds*)

  Lemma forall_list_forall: forall l,
    (forall a, In a l -> P a) -> list_forall l.
  Proof.
    intros. induction l; simpl in *; constructor; auto.
  Qed.


  (* if list_forall holds, the property holds for all elements In the
  list.*)

  Lemma list_forall_forall: forall l,
    list_forall l -> (forall a, In a l -> P a).
  Proof.
    induction l; intros. inv H0.
    simpl in H0. destruct H0. inv H; auto. inv H. auto.
  Qed.
  Variables l1 l2: list A.

  Lemma list_forall_app_list_forall_l: list_forall (l1 ++ l2) -> list_forall l1.
  Proof.
    induction l1; simpl.

    intros; constructor; auto.
    intros. inv H. constructor; auto.
  Qed.

  Lemma list_forall_app_list_forall_r: list_forall (l1 ++ l2) -> list_forall l2.
  Proof.
    induction l1; simpl.

    intros; auto.
    intros. inv H; auto.
  Qed.

  Lemma list_forall_list_forall_app: list_forall l1 -> list_forall l2 -> list_forall (l1 ++ l2).
  Proof.
    intros LFA1 LFA2.
    induction l1; simpl; auto.
    inv LFA1.
    constructor; auto.
  Qed.

End FORALL.


Fixpoint list_forallb {A:Type} f (l: list A) : bool:=
  match l with
    | nil => true
    | x :: l' =>
      (f x) && (list_forallb f l')
  end.

Lemma list_forallb_list_forall: forall A f (P: A -> Prop) (l: list A),
  (forall a, f a = true -> P a) ->
  list_forallb f l = true -> list_forall P l.
Proof.
  intros A f P l H H0. 
  induction l; simpl in *; constructor.
  apply H. destruct (f a); auto.
  apply IHl. destruct (list_forallb f l); auto.
  destruct (f a); auto.
Qed.

Lemma list_forall_list_forallb: forall A f (P: A -> Prop) (l: list A),
  (forall a, P a -> f a = true) ->
  list_forall P l -> list_forallb f l = true.
Proof.
  intros A f P l Ptrue LF.
  induction' l.
  Case "@nil".
    reflexivity.
  Case "cons".
    inv LF.
    simpl. rewrite andb_true_iff. auto.
Qed.


Lemma list_forall_imply: forall (A:Type) (P Q: A -> Prop) (l: list A),
  (forall a, P a -> Q a) -> list_forall P l -> list_forall Q l.
Proof.
  intros A P Q l H H0.
  induction H0; auto using list_forall_cons, list_forall_nil.
Qed.

Lemma list_forall_map_list_forall {A B} (l:list A) (f: A -> B) (P: A -> Prop) (Q: B -> Prop):
  (forall a, Q (f a) -> P a) ->
  list_forall Q (map f l) -> list_forall P l.
Proof.
 intro IMP. induction l; simpl; intro H; inv H; constructor; auto.
Qed.

Lemma list_forall_list_forall_map {A B} (l:list A) (f: A -> B) (P: A -> Prop) (Q: B -> Prop):
  (forall a, P a -> Q (f a)) -> list_forall P l  ->
  list_forall Q (map f l).
Proof.
 intro IMP. induction l; simpl; intro H; inv H; constructor; auto.
Qed.

Hint Constructors list_forall.

Program Definition list_forall_semi_dec A P Q (f: forall a:A, {P a} + {Q a}) l :
  {list_forall P l} + {True} :=
  match list_forallb f l with
    | true => left _
    | false => right _
  end.
Next Obligation.
  apply list_forallb_list_forall with (f := f); auto.
  intros. destruct (f a); simpl in *; auto. inv H.
Qed.

(* inverse a number of common pattern matching of options *)
Ltac inv_opt :=
 repeat
   (match goal with
    | H : match ?X with
            | Some y => Some _
            | None => None
          end = Some _ |- _ =>
    let Xeqn := fresh X "eqn" in
    destruct X as [y|] _eqn:Xeqn;
    inv H; auto
   end);
 repeat
   (match goal with
    | H : match ?X with
            | Some y => Some _
            | None => None
          end = None |- _ =>
    let Xeqn := fresh X "eqn" in
    destruct X as [y|] _eqn:Xeqn;
    inv H; auto
  end);
 repeat
   (match goal with
    | H : match ?X with
            | Some _ => _
            | None => False
          end |- _ =>
    let Xeqn := fresh X "eqn" in
    destruct X as [y|] _eqn:Xeqn; auto
  end).



(* a type to do rewriting only in the environement *)
Inductive imp_rewrite (P1 P2: Prop) : Prop:=
  | imp_rewrite_intro : (P1 -> P2) -> imp_rewrite P1 P2.
Hint Constructors imp_rewrite.

Notation " A '-r>' B" := (imp_rewrite A B) (at level 90).

Lemma ir_refl: forall A, A -r> A.
Proof.
  auto.
Qed.

Lemma ir_trans: forall A B C, (A -r> B) -> (B -r> C) -> (A -r> C).
Proof.
  intuition.
Qed.

Add Relation Prop imp_rewrite
  reflexivity proved by ir_refl
  transitivity proved by ir_trans
  as imp_rewriteSetoid.

Instance imp_rewrite_sub: subrelation imp_rewrite impl.
Proof.
  compute.
  intuition.
Qed.


Inductive is_some {A:Type}: (option A)-> Prop :=
| is_some_intro: forall a:A, is_some (Some a).

Hint Constructors is_some.


(* is_some on a Some is useless *)
Lemma is_some_Some {A:Type} (a:A):
  is_some (Some a) -r> True.
Proof. intuition. Qed.

(* is_some on a None is false *)
Lemma is_some_None {A:Type}:
  is_some (@None A) -r> False.
Proof. intuition. inversion H. Qed.


Lemma remove_Some: forall A (a b:A), Some a = Some b -r> a = b.
Proof.
  intuition. inv H. reflexivity.
Qed.
Hint Rewrite @is_some_Some @is_some_None remove_Some: clean.

(** the clean database must be used for rewrite lemmas that simplifies
   the hypothethis *)

Ltac solve_is_some :=
  intros;
  match goal with
    | H : is_some None |- _ => inv H
    | |- is_some (Some ?x) => apply is_some_intro
    | H : ?X = Some ?Y |- is_some ?X =>
      rewrite H; apply is_some_intro
    | H : Some ?Y = ?X |- is_some ?X =>
      rewrite <- H; apply is_some_intro
  end; fail.




(* the aliases hint db is used for aliases like ident := positive *)
Tactic Notation "unalias" := autounfold with aliases.
Tactic Notation "unalias" "in" constr(H) := autounfold with aliases in H.
Tactic Notation "unalias" "in" "*" := autounfold with aliases in *.
Tactic Notation "unalias" "*" := autounfold with aliases in *.



Notation "'nosimpl' t" := (let '(tt) := tt in t) (at level 10).


Ltac option_on_right :=
  repeat
    match goal with
      | H : _ |- _ =>
        match type of H with
          | _ = None => fail 1
          | _ = Some _ => fail 1
          | Some _ = _ => symmetry in H
          | None = _ => symmetry in H
        end
    end.
Local Notation "¬ x" := (x -r> False) (at level 75, only parsing).
Lemma refl_True {A:Type} (a:A): a = a -r> True.
Proof.
  intuition.
Qed.  
Lemma diff_False {A:Type} (a:A): ¬a <> a.
Proof.
  intuition.
Qed.

Lemma S_not_O: forall n, ¬S n = O.
Proof. intuition. Qed.
Lemma O_not_S: forall n, ¬O = S n.
Proof. intuition. Qed.
Lemma Some_not_None: forall `(a:A),
  ¬Some a = None.
Proof. intuition. inv H. Qed.
Lemma None_not_Some: forall `(a:A),
  ¬None = Some a.
Proof. intuition. inv H. Qed.
Lemma true_not_false : ¬true = false.
Proof. intuition. Qed.
Lemma false_not_true: ¬false = true.
Proof. intuition. Qed.
Lemma left_not_right: forall (A B:Prop) (a:A) (b:B),
  ¬left B a=right A b.
Proof. intros. constructor. intro. inv H. Qed.
Lemma right_not_left: forall (A B:Prop) (a:A) (b:B),
  ¬right A b = left B a.
Proof. intros. constructor. intro. inv H. Qed.


Hint Rewrite @refl_True @diff_False S_not_O O_not_S @Some_not_None @None_not_Some
  true_not_false false_not_true left_not_right right_not_left: clean.

Ltac solve_contradiction :=
  intros;
  match goal with
    | H : _ |- _ =>
      simpl in H;
      autorewrite with clean in H;
      match type of H with
        | False => destruct H
      end
  end.

Hint Extern 5 => solve_is_some.
Hint Extern 5 => solve_contradiction.


Create HintDb optional_inv.
(* tag an hypothethis, saying it should be inverted, and its inversion
   can only produce one new subgoal*)
Definition TAG_INV {P} (p:P) := p.
Notation "'tag_to_inv' ( X )" := (X -r> TAG_INV ( X )%type) (at level 0, only parsing).

(* allows several subgoals to be produced *)
Definition TAG_INV_MULTI {P} (p:P) := p.
Notation "'tag_to_inv_multi' ( X )" := (X -r> TAG_INV_MULTI ( X )%type) (at level 0, only parsing).

Ltac optional_inv_aux H :=
  progress (autorewrite with optional_inv in H);
  match type of H with
    | TAG_INV _ => inv H; [idtac] (* ensures only one subgoal has been produced *)
    | TAG_INV_MULTI _ => inv H
  end.

Tactic Notation "optional_inv" hyp(H) :=
  try (optional_inv_aux H).
Tactic Notation "optional_inv" "*" :=
  repeat
  match goal with
    | H : _ |- _ => optional_inv_aux H
  end.


Tactic Notation "clean" "in" hyp(H) :=
  repeat (progress (autorewrite with clean in H; optional_inv H)).
Tactic Notation "clean" "in" "*" :=
  repeat (progress (autorewrite with clean in *; optional_inv *)).

Tactic Notation "clean" "in" "*" "|-" :=
  repeat (progress (autorewrite with clean in * |-; optional_inv *)).

Tactic Notation "clean" "in" "|-" "*" :=
  autorewrite with clean in |- *.

Ltac revert_all_of_type A :=
  repeat match goal with
    | H : A |- _ => revert dependent H
  end.


(* a mark to put in the goal, to know up to where to intro *)
Inductive _MARK_:Prop := MARK.

Ltac pose_mark :=
  generalize MARK.

Ltac intros_until_mark :=
  repeat
  (match goal with
     | H : _MARK_ |- _ => fail 1 (* if a mark has been introduced, stop *)
     | _ => idtac (* else continue to introduce *)
   end; intro);
  (match goal with
     | H : _MARK_ |- _ => clear H
     | _ => idtac
   end)
  .


Lemma type_of_JMeq_eq: forall A B (a:A) (b:B), a ~=b -> A = B.
Proof.
  intros. inv H. reflexivity.
Qed.

Lemma inj_pairT2_rewrite :
  forall U (P:U -> Type) (p:U) (x y:P p),
    existT P p x = existT P p y -r> x = y.
Proof.
  constructor.
  apply inj_pairT2.
Qed.


Lemma inj_pairT2_hetero:
  forall U (P:U -> Type) (p1 p2:U) (x:P p1) (y: P p2),
    p1 = p2 ->
    existT P p1 x = existT P p2 y -r> x ~= y.
Proof.
  intros * EQ.
  subst. constructor.
  intro. apply inj_pairT2 in H. subst. constructor.
Qed.



Hint Rewrite inj_pairT2_hetero using (auto; congruence): clean.
Hint Rewrite inj_pairT2_rewrite: clean.


Ltac normalize_env_aux :=
  repeat
    match goal with
      | H : True |- _ => clear H
      | H : (_, _) = (_, _) |- _ => inversion H; try clear H
      | H : @JMeq ?A ?a ?A ?b |- _ => apply JMeq_eq in H
      | H : @JMeq ?A ?a ?B ?b |- _ =>
        pose proof (type_of_JMeq_eq H);
        pose_mark;
        revert_all_of_type A;
        subst; intros_until_mark; apply JMeq_eq in H
    end.

Ltac normalize_env :=
  clean in * |-; normalize_env_aux.

Tactic Notation "clean" :=
  repeat (progress (
  clean in *;
  normalize_env_aux;
  option_on_right;
  try solve_contradiction;
  subst; auto)).

Tactic Notation "clean" "no" "auto" :=
  repeat (progress (
  clean in *;
  normalize_env_aux;
  option_on_right;
  try solve_contradiction;
  subst)).


Ltac prog_match_option :=
  match goal with
    | H : context[match ?X with |Some x => _ | None =>  _ end] |- _ =>
      destruct X as [x|] _eqn
    | |- context[match ?X with |Some x => _ | None =>  _ end] =>
      destruct X as [x|] _eqn
  end.

Tactic Notation "dest_if_aux" constr(TERM) "as" simple_intropattern(pat):=
  match TERM with
    | context[if ?EXP then _ else _] =>
      destruct EXP as pat _eqn
  end.

Tactic Notation "dest_if_aux" constr(TERM) :=
  dest_if_aux TERM as [].


(* destruct if in a given hypothethis*)
Tactic Notation "dest_if" "in" hyp(H) "as" simple_intropattern(pat) :=
  let TERM := type of H in
   dest_if_aux TERM as pat.

Tactic Notation "dest_if" "in" hyp(H) :=
  dest_if in H as [].

(* destruct an in in any hypothethis *)
Tactic Notation "dest_if" "as" simple_intropattern(pat) :=
  match goal with
    | H : ?TERM |- _ => dest_if_aux TERM as pat
  end.
Tactic Notation "dest_if" := dest_if as [].


(* destruct an if in the goal *)
Tactic Notation "dest_if_goal" "as" simple_intropattern(pat) :=
  match goal with
    | |- ?TERM => dest_if_aux TERM as pat
  end.
Tactic Notation "dest_if_goal" := dest_if_goal as [].



Tactic Notation "inv_clean" hyp(H) := inv H; clean.

(* this one often doesn't work because inv generate a number of
   subgoals that is different from the number of constructors of H*)
Tactic Notation "inv'" hyp(H) := cases H (inv H).
Tactic Notation "inv_clean'" hyp(H) := inv' H; clean.




Definition unsafe_tail `(l:list A) :=
  match l with
    | nil => nil
    | _ :: t => t
  end.

Fixpoint last `(l: list A) :=
  match l with
    | nil => None
    | [x] => Some x
    | _ :: l' => last l'
  end.

Lemma last_is_some `(l: list A): length l <> O -> is_some (last l).
Proof.
  induction' l; intros NOTNIL; simpl in *; auto.
  Case "cons".
  destruct l; auto.
Qed.

Lemma last_is_last `(l: list A) x: last l = Some x -> exists l', l = l' ++ [x].
Proof.
  induction' l; simpl; intros; auto.
  Case "cons".
  destruct l. clean.
  exists (@nil A); simpl. reflexivity.
  specialize (IHl H).
  destruct IHl as [l' EQ].
  rewrite EQ.
  exists (a::l'). simpl. auto.
Qed.




(* Not empty lists *)
Definition not_empty_list A := (A * list A)%type.
Definition not_empty_map {A B} (f: A -> B) (nel:not_empty_list A) : not_empty_list B:=
  let (a, l) := nel in
  (f a, map f l).


Fixpoint list_take {A} n (l: list A) :=
  match n, l with
    | O, _ 
    | _, nil => nil
    | S n', h :: t => h :: (list_take n' t)
  end.

Lemma list_take_drop: forall A n (l:list A), list_take n l ++ list_drop n l = l.
Proof.
  induction' n as [| n']; intros.
  Case "O".
    simpl. reflexivity.
  Case "S n'".
    destruct' l.
    SCase "@nil".
      simpl. reflexivity.
    SCase "cons".
      simpl. congruence.
Qed.

Lemma list_take_app: forall A (l1 l2: list A),
  list_take (length l1) (l1 ++ l2) = l1.
Proof.
  induction' l1 as [|a l1']; intros.
  Case "@nil".
    reflexivity.
  Case "cons a l1'".
    simpl. congruence.
Qed.


Lemma list_drop_app: forall A (l1 l2: list A),
  list_drop (length l1) (l1 ++ l2) = l2.
Proof.
  induction' l1 as [|a l1']; intros.
  Case "@nil".
    reflexivity.
  Case "cons a l1'".
    simpl. congruence.
Qed.




(*
Hint Extern 5 => solve_is_some: crunch.
Hint Extern 5 => solve_contradiction : crunch.

Tactic Notation "crunch" := auto with crunch.
Tactic Notation "ecrunch" := eauto with crunch.

Tactic Notation "crunch" "with" ident(X) := auto with crunch X.
Tactic Notation "ecrunch" "with" ident(X) := eauto with crunch X.
Tactic Notation "crunch" "using" ident(X) := auto using X with crunch.
Tactic Notation "ecrunch" "using" ident(X) := eauto using X with crunch.
Tactic Notation "crunch" "using" ident(X) "with" ident(Y) := auto using X with crunch Y.
Tactic Notation "ecrunch" "using" ident(X) "with" ident(Y):= eauto using X with crunch Y.
*)

