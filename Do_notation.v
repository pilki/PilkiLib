
Require Export Coqlibext.
Require Import Morphisms.
Set Implicit Arguments.


(** Introduction of  "do" notations *)

(* we use type classes to avoid definition of notation for each use *)

Class Functor (F:Type -> Type) :=
  fmap: forall {A B :Type}, (A -> B) -> F A -> F B.


(* for a "do" notation in monads, you don't need a return, just
   bind. Hence this "almost monad" class*)

Class Monadish (M:Type -> Type) :=
  bind: forall {A B :Type}, M A -> (A -> M B) -> M B.

Class Pointed (M:Type -> Type) :=
  point: forall {A: Type}, A -> M A.

Class Monad (M:Type -> Type) := {
  Monad_Monadish :> Monadish M;
  Monad_Pointed :> Pointed M
}.

Generalizable Variables A B C D M.
(*Instance Monad_Return `{Monad M}: Pointed M :=
{ point := fun A a => mreturn a }.

Instance Monad_Ish `{Monad M}: Monadish M :=
{ bind := fun A B ma f => mbind ma f}.
*)

(*Instance Build_Monaad `{Monadish M} `{Pointed M} : Monad M.*)

(* what level should that be ? *)

Infix ">>=" := bind (at level 80).
Notation "x >> y" := (x >>= (fun _ => y)) (at level 80).
Infix "<$>" := fmap (at level 60).


Definition blocked_do_bind `{Monadish M} {A B} (f: A -> M B) (x: M A):= 
  nosimpl (x >>= f).


(* the corresponding "do" notation *)

Notation "'do' '_' '<-' A ; B" :=
  (blocked_do_bind (fun _ => B) (A))
   (at level 200, A at level 100, B at level 200, format
   "'[v' 'do'  '_'  <-  A ;  '/' B ']'").

(*Notation "'do' A ; B" :=
  (blocked_do_bind (fun _ => B) A)
   (at level 200, A at level 100, B at level 200, format
   "'[v' 'do'  A ;  '/' B ']'").*)


Notation "'do' X '<-' A ; B" :=
  (blocked_do_bind (fun X => B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  X  '<-'  A ;  '/' B ']'").

Notation "'do' ( X : T ) <- A ; B" :=
  (blocked_do_bind (fun (X: T) => B) A)
   (at level 200, X ident, A at level 100,
    T at level 100, B at level 200, only parsing).

Notation "'do' ( '_' : T ) <- A ; B" :=
  (blocked_do_bind (fun (_: T) => B) A)
   (at level 200, A at level 100, T at level 100, B at level 200, only parsing).


Notation "'do_f' X <- A ; B" :=
  (let f__ := fun X => B in
    f__ <$> (A))
   (at level 200, X ident, A at level 100, B at level 200).



Notation "'do' ( X , Y ) <- A ; B" :=
  (blocked_do_bind (fun _XY_ => let '(X, Y) := _XY_ in  B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y )  '<-'  A ;  '/' B ']'").
Notation "'do' X , Y  <- A ; B" :=
  (blocked_do_bind (fun _XY_ => let '(X, Y) := _XY_ in  B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, only parsing).


Notation "'do' ( '_' , Y ) <- A ; B" :=
  (blocked_do_bind (fun _XY_ => let '(_, Y) := _XY_ in  B) A)
   (at level 200, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y )  '<-'  A ;  '/' B ']'").
Notation "'do' ( X , '_' ) <- A ; B" :=
  (blocked_do_bind (fun _XY_ => let '(X, _) := _XY_ in  B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' )  '<-'  A ;  '/' B ']'").



Notation "'do' ( X , Y , Z ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y ,  Z )  '<-'  A ;  '/' B ']'").

Notation "'do'  X , Y , Z  <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200, only parsing).

Notation "'do' ( '_' , Y , Z ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(_, Y, Z) := _XYZ_ in B) A)
   (at level 200,  Y ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y ,  Z )  '<-'  A ;  '/' B ']'").

Notation "'do' ( X , '_' , Z ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, _, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' ,  Z )  '<-'  A ;  '/' B ']'").


Notation "'do' ( X , Y , '_' ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, _) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( X , '_' , '_' ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, _, _) := _XYZ_ in B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y , '_' ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , '_' , Z ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(_, _, Z) := _XYZ_ in B) A)
   (at level 200, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  '_' ,  Z )  '<-'  A ;  '/' B ']'").




Notation "; A ; B" :=
  (blocked_do_bind (fun _ => B) A)
   (at level 200, A at level 100, B at level 200, only parsing): monad_scope.

Notation "; ( X : T ) <- A ; B" :=
  (blocked_do_bind (fun (X: T) => B) A)
   (at level 200, X ident, A at level 100,
    T at level 100, B at level 200, only parsing).

Notation "; X '<-' A ; B" :=
  (blocked_do_bind (fun X => B) A)
   (at level 200, X ident, A at level 100, B at level 200, only parsing): monad_scope.

Notation "; ( X , Y ) <- A ; B" :=
  (blocked_do_bind (fun _XY_ => let '(X, Y) := _XY_ in  B) A)
   (at level 200, X ident, Y ident, A at level 100,
     B at level 200, only parsing): monad_scope.

Notation ";  X , Y  <- A ; B" :=
  (blocked_do_bind (fun _XY_ => let '(X, Y) := _XY_ in  B) A)
   (at level 200, X ident, Y ident, A at level 100,
     B at level 200, only parsing): monad_scope.

Notation "; ( X , Y , Z ) <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200,
   only parsing): monad_scope.

Notation "; X , Y , Z <- A ; B" :=
  (blocked_do_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200,
   only parsing): monad_scope.
Delimit Scope monad_scope with monad.


Notation "'do{'  A }" :=
  ((A)%monad) (at level 200, A at level 200, only parsing).


Create HintDb simpl_do.
Hint Rewrite Zegal_left using (first [assumption | symmetry ; assumption]): simpl_do.

Tactic Notation "simpl_do" :=
  autounfold with simpl_do; autorewrite with simpl_do; try unfold point; simpl.

Tactic Notation "simpl_do" "in" hyp(H):=
  autounfold with simpl_do in H; autorewrite with simpl_do in H; try unfold point in H; simpl in H.

Tactic Notation "simpl_do" "in" "*":=
  autounfold with simpl_do in *; autorewrite with simpl_do in *; try unfold point in *; simpl in *.


Ltac find_do_and_prog TERM :=
  let Heq_do := fresh "Heq_do" in
  match TERM with
    | context[
      (blocked_do_bind
        (fun _XYZ_ : _ * _ * _ =>
          match _XYZ_  with
            | pair _PAT_ z =>
              match _PAT_ with
                | pair x y => _
              end
          end
        ) ?X)] =>
      (  destruct X as [[x y] z] _eqn:Heq_do
      || destruct X as [[[x y] z]|[[x y] z]] _eqn:Heq_do
      || destruct X as [[[x y] z]|[[x y] z]|[[x y] z]] _eqn:Heq_do)
    | context[do ( x , y ) <- ?X; _]  =>
      (  destruct X as [[x y]] _eqn:Heq_do
      || destruct X as [[x y]|[x y]] _eqn:Heq_do
      || destruct X as [[x y]|[x y]|[x y]] _eqn:Heq_do)
    | context[do x <- ?X; _] =>
      let x := fresh x in
      (  destruct X as [x] _eqn:Heq_do
      || destruct X as [x|x] _eqn:Heq_do
      || destruct X as [x|x|x] _eqn:Heq_do)
    | context[do (x:_) <- ?X; _] =>
      let x := fresh x in
      (  destruct X as [x] _eqn:Heq_do
      || destruct X as [x|x] _eqn:Heq_do
      || destruct X as [x|x|x] _eqn:Heq_do)
    | context[do _ <- ?X; _] =>
      (  destruct X as [?] _eqn:Heq_do
      || destruct X as [?|?] _eqn:Heq_do
      || destruct X as [?|?|?] _eqn:Heq_do)
  end; clean in Heq_do.

Ltac prog_do :=
  match goal with
    | H : ?TERM |- _ => find_do_and_prog TERM; simpl_do in H
    | |- ?TERM => find_do_and_prog TERM; simpl_do
  end; auto.

Create HintDb monadInv.

Ltac monadInv_aux H :=
  (* we try to use "ad hoc" rewriting for this specific monad *)
  ((progress (autorewrite with monadInv in H);
    repeat match type of H with
      | exists X, _ =>
        let X := fresh X in
        destruct H as [X H]; simpl_do in H; clean in H
      | ?P /\ _ =>
        let H1 :=
        match P with
          | _ = _ => fresh "EQ"
          | _ => fresh "H"
        end in
        destruct H as [H1 H];
        simpl_do in H1; simpl_do in H; clean in H1; clean in H
    end) ||
  match type of H with
    | ?TERM => find_do_and_prog TERM; simpl_do in H; clean in H
  end); auto; subst.

Ltac unfold_head H :=
  let aux F :=
    match F with
      | @blocked_do_bind => fail 1
      | _ => unfold F in H
    end in
  match type of H with
    | (?F _ _ _ _ _ _ _ _) = _ =>
      aux F
    | (?F _ _ _ _ _ _ _) = _ =>
      aux F
    | (?F _ _ _ _ _ _) = _ =>
      aux F
    | (?F _ _ _ _ _) = _ =>
      aux F
    | (?F _ _ _ _) = _ =>
      aux F
    | (?F _ _ _) = _ =>
      aux F
    | (?F _ _) = _ =>
      aux F
    | (?F _) = _ =>
      aux F
  end.


Tactic Notation "monadInv" hyp(H) :=
  ((progress simpl in H) || unfold_head H || idtac);
  progress (simpl_do in H; optional_inv H; try (clean in H);
    repeat monadInv_aux H; subst; try contradiction).


Ltac monadInvGoal_aux :=
  match goal with
    | |- ?TERM => find_do_and_prog TERM; simpl_do; clean in |- *
  end; auto; subst.

Tactic Notation "monadInv" :=
  autounfold with monadInv; repeat monadInvGoal_aux.


Ltac prog_dos := repeat (prog_do; clean).







(* some typical instances *)

Instance F_option: Functor option :=
{ fmap:= fun _ _ f oa =>
  match oa with
    | None => None
    | Some a => Some (f a)
  end}.

Instance F_pair: forall B, Functor (fun A => (A * B)%type) :=
  { fmap := fun _ _ f p =>
    let (p1, p2) := p in
      (f p1, p2)
      }.



Instance Monad_option: Monad option :=
{
  Monad_Monadish := fun _ _ oa f =>
    match oa with
      | None => None
      | Some a => f a
    end;
  Monad_Pointed := @Some
}.

Instance Monadish_option: Monadish option.
Proof.
  eauto with typeclass_instances.
Defined.


Lemma prog_do_monad_some: forall A B (f: A -> option B) c,
  blocked_do_bind f (Some c) = f c.
Proof.
  auto.
Qed.

Lemma prog_do_monad_none: forall A B (f: A -> option B),
  blocked_do_bind f None = None.
Proof.
  auto.
Qed.

Lemma remove_some: forall A (x y: A), Some x = Some y -r> x = y.
Proof.
  split; congruence. 
Qed.


Hint Rewrite prog_do_monad_none prog_do_monad_some: simpl_do.

Hint Rewrite remove_some: clean.

Goal (do (a, b, c) <- Some (true, false, true); Some (a && b && c)) = Some true -> False.
intro. monadInv H.
Qed.


(* [FPair B _ _ A] means : I return an [A] and carry silently a [B]
   [oconb] is used to combined values to build a bind
   [oneutral] is for point

   [A] is at the end so the typeclass mechanism works
 *)

Unset Implicit Arguments.
Inductive FPair (B:Type) (ocomb: option (B -> B -> B)) (oneutral: option B)
  (A:Type): Type:=
  fpair : forall (a:A) (b:B), FPair B ocomb oneutral A.

Implicit Arguments fpair [[B] [ocomb] [oneutral] [A]].

Set Implicit Arguments.

Notation "( x ,> y )" := (fpair x y) (at level 0).

Instance Functor_FPair: forall B oc on, Functor (FPair B oc on) :=
{fmap:= fun _ _ f p =>
  match p with
    (a ,> b) => ((f a),> b)
  end}.


Instance Monadish_FPair: forall B comb on,
  Monadish (FPair B (Some comb) on) :=
  { bind := fun _ _ p f =>
    match p with
      | (a ,> b) =>
    match f a with
      | (c ,> b') => (c ,> (comb b b'))
    end
    end}.

Instance Pointed_FPair B oc neutral:
  Pointed (FPair B oc (Some neutral)) :=
  { point := fun A (a:A) => (a,> neutral) }.



Inductive changed (A:Type) :=
  | Unchanged
  | Changed (a:A).
Implicit Arguments Unchanged [[A]].


Instance F_changed: Functor changed :=
{ fmap:= fun _ _ f ca =>
  match ca with
    | Unchanged => Unchanged
    | Changed a => Changed (f a)
  end}.


Instance Monad_changed: Monad changed :=
{ Monad_Monadish := fun _ _ ca f =>
  match ca with
    | Unchanged => Unchanged
    | Changed a => f a
  end;
  Monad_Pointed := fun _ a => Changed a}.

Instance Monadish_changed: Monadish changed.
Proof.
  eauto with typeclass_instances.
Defined.


(* this should expect a monad, but because of the bug in 8.3, we split it *)
Fixpoint mmap {M} {MON:Monad M} (*{PTD:Pointed M}*) {A B: Type} (f: A -> M B) (l: list A) : M (list B) :=
  match l with
    | nil => point nil
    | a :: l' =>
      do b <- f a;
      do l'' <- mmap f l';
      point (b :: l'')
  end.

  (* I don't know how to prove a general property on mmap *)
Lemma mmap_option {C D} (f: C -> option D) l1 l2:
  mmap f l1 = Some l2 ->
  list_forall2 (fun b ob => Some b = ob) l2 (map f l1).
Proof.
  revert l2. induction l1; intros l2 MMAP; simpl in *.
  clean. constructor.

  monadInv MMAP.
  constructor; auto.
Qed.

Definition not_empty_mmap {M} {MON:Monad M} (*{PTD:Pointed M}*) {A B: Type} (f: A -> M B) (l: not_empty_list A)
  : M (not_empty_list B) :=
  let (hd, tl) := l in
  do{;
    nhd <- f hd;;
    ntl <- mmap f tl;
    point (nhd, ntl)
  }.


Goal (
  do x <- Some 1;
  do y, z <- (Some (3, 4));
  do (a, b, c) <- Some (3, 4, 5);
  point (z  + b + c)) = Some 13.
Proof.
  simpl_do.
  reflexivity.
Qed.


Notation "; 'let' X ':=' A ; B" :=
  (let X := A in B)
   (at level 200, X ident, A at level 100, B at level 200,
     only parsing): monad_scope.


Goal(
do{;
  x <- Some 3;;
  let os := Some 4;;
  _ <- os;;
  (y, z) <- Some (5, 6);;
  (a, b) <- Some (7, 8);
  (Some (y + b))
}) = Some 13 -> True.
Proof.
  intro. monadInv H.
  simpl_do in H. constructor.
Qed.



