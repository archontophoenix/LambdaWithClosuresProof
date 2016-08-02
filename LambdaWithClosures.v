(*******************************************************************************
Beta-reduction in the untyped lambda calculus is usually presented as rewriting
the body of the applied of the applied function to replace each occurrence of
the function's variable with the corresponding argument. However, most
call-by-value programming language implementations do not follow quite this rule
at execution time; instead, when the body of an applied function is itself a
function, they just record the value the argument in a data structure called a
closure, and defer any substitution until a closure whose body is *not* a
function is applied to an argument. This strategy of recording substitutions to
be performed later is called "explicit substitutions" in the literature
(closures are a particular instance of explicit substitutions; there are many
variations on the concept of explicit substitutions, with different properties).

(Note that because we are interested in call-by-value semantics on closed
programs here, every term substituted into another in a correct  program will be
a closed term, so that alpha-conversion is never necessary to avoid variable
capture.)

The goal here is to come up with a machine-checked proof that a call-by-value
untyped lambda calculus with closures is equivalent to one with term rewriting.
*******************************************************************************)

Require Import Coq.Vectors.Vector.

Definition Vec (A: Type) (n: nat): Type := VectorDef.t A n.
Definition Fin (n: nat): Set := Fin.t n.
Notation "[]" := (nil _).
Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(* Basic definitions **********************************************************)

(* The structure of an expression, the input format for both strategies. *)
Inductive Exp: Set :=
  (* A variable *)
  | Var: nat -> Exp
  (* A function *)
  | Lam: nat -> Exp -> Exp
  (* An application of the first Exp (function) to the second (argument) *)
  | App: Exp -> Exp -> Exp.

(* Where is this in the standard library under 8.4? Grrr. *)
Fixpoint beq_nat (n m: nat): bool :=
  match n, m with
  | 0, 0 => true
  | 0, S _ => false
  | S _, 0 => false
  | S n', S m' => beq_nat n' m'
  end.

(* Contexts *******************************************************************)

(* A context (used in checking for closedness and deBruijnizing) is a stack of
   the variable names for the enclosing lambdas. *)
Definition Ctx (len: nat) := Vec nat len.

Fixpoint lookUp {len: nat} (n: nat) (ctx: Ctx len): option (Fin len) :=
  match ctx with
  | [] =>
      None
  | h :: t =>
      if beq_nat h n then Some Fin.F1 else option_map Fin.FS (lookUp n t)
  end.

Example lookUp2Nil: lookUp 2 [] = None.
Proof. reflexivity. Qed.
Example lookUp2123: lookUp 2 (1 :: 2 :: 3 :: []) = Some (Fin.FS Fin.F1).
Proof. reflexivity. Qed.
Example lookUp21232: lookUp 2 (1 :: 2 :: 3 :: 2 :: []) = Some (Fin.FS Fin.F1).
Proof. reflexivity. Qed.

(* Closed terms ***************************************************************)

(* Whether a program is closed in a given context -- that is, has no unbound
   variables *)
Inductive Closed (len: nat): Ctx len -> Exp -> Prop :=
  | CVar {n: nat} {pos: Fin len} {ctx: Ctx len}:
      lookUp n ctx = Some pos ->
      Closed len ctx (Var n)
  | CLam {n: nat} {body: Exp} {ctx: Ctx len}:
      Closed (S len) (n :: ctx) body ->
      Closed len ctx (Lam n body)
  | CApp {fnc arg: Exp} {ctx: Ctx len}:
      Closed len ctx fnc -> Closed len ctx arg ->
      Closed len ctx (App fnc arg).

Definition ClosedTerm (e: Exp) := Closed 0 [] e.

Example closedVar: Closed 2 (1 :: 2 :: []) (Var 2).
Proof.
  assert (H: lookUp 2 (1 :: 2 :: []) = Some (Fin.FS Fin.F1)). { reflexivity. }
  eapply CVar. apply H.
Qed.
Example closedId: ClosedTerm (Lam 1 (Var 1)).
Proof.
  unfold ClosedTerm. constructor.
  assert (H: lookUp 1 (1 :: []) = Some (Fin.F1)). { reflexivity. }
  eapply CVar. apply H.
Qed.
Example notClosed: ~ ClosedTerm (Lam 1 (Var 2)).
Proof.
  intros Contra. inversion Contra. inversion H1. inversion H5.
Qed.

(* Symbolic exeuction *********************************************************)

(* Substitution of term e for variable x *)
Inductive Subst (e: Exp) (x: nat): Exp -> Exp -> Prop :=
  | SVarEq:
      Subst e x (Var x) e
  | SVarNeq {y: nat}:
      x <> y ->
      Subst e x (Var y) (Var y)
  | SAbsEq {body: Exp}:
      Subst e x (Lam x body) (Lam x body)
  | SAbsNeq {y: nat} {body sBody: Exp}:
      x <> y -> Subst e x body sBody ->
      Subst e x (Lam y body) (Lam y sBody)
  | SApp {fnc arg sFnc sArg: Exp}:
      Subst e x fnc sFnc -> Subst e x arg sArg ->
      Subst e x (App fnc arg) (App sFnc sArg).

Example substEx:
  Subst (Lam 9 (Var 9)) 0 (App (Var 0) (Lam 9 (Var 9)))
    (App (Lam 9 (Var 9)) (Lam 9 (Var 9))).
Proof.
  constructor. constructor. constructor. intros Contra; inversion Contra.
  constructor. intros Contra; inversion Contra.
Qed.

(* Big-step symbolic reduction. *)
Inductive SymReduce: Exp -> Exp -> Prop :=
  | SRLam {n: nat} {body: Exp}:  (* functions are fully reduced values *)
      SymReduce (Lam n body) (Lam n body)
  | SRApp {f a: nat} {fnc arg fBody aBody result: Exp}:
      SymReduce fnc (Lam f fBody) -> SymReduce arg (Lam a aBody) ->
      Subst (Lam a aBody) f fBody result ->
      SymReduce (App fnc arg) result.

Example symReduceId:
  SymReduce (App (Lam 0 (Var 0)) (Lam 1 (Var 1))) (Lam 1 (Var 1)).
Proof.
  eapply SRApp.
  - constructor.
  - constructor.
  - constructor.
Qed.
Example notReduceVar:
  ~ exists p, SymReduce (Var 0) p.
Proof.
  intros Contra. inversion Contra. inversion H.
Qed.

(* Execution with explicit substitutions and de Bruijn indices ****************)

(* DeBruijnized expression, with context depth at each point *)
Inductive Dxp (depth: nat): Set :=
  | DVar (index: Fin depth): Dxp depth
  | DLam (body: Dxp (S depth)): Dxp depth
  | DApp (fnc arg: Dxp depth): Dxp depth.

(* DeBruijnization: compiling a term to a de Bruijn-indexed form *)
Inductive DeBruijnize (len: nat) (ctx: Ctx len): Exp -> Dxp len -> Prop :=
  | DBVar {n: nat} {pos: Fin len}:
      lookUp n ctx = Some pos ->
      DeBruijnize len ctx (Var n) (DVar len pos)
  | DBLam {n: nat} {body: Exp} {dBody: Dxp (S len)}:
      DeBruijnize (S len) (n :: ctx) body dBody ->
      DeBruijnize len ctx (Lam n body) (DLam len dBody)
  | DBApp {fnc arg: Exp} {dFnc dArg: Dxp len}:
      DeBruijnize len ctx fnc dFnc -> DeBruijnize len ctx arg dArg ->
      DeBruijnize len ctx (App fnc arg) (DApp len dFnc dArg).

Example dbId: DeBruijnize 0 [] (Lam 0 (Var 0)) (DLam 0 (DVar 1 Fin.F1)).
Proof.
  constructor. constructor. reflexivity.
Qed.
Example dbAppIdId:
  DeBruijnize 0 []
    (App (Lam 0 (Var 0)) (Lam 1 (Var 1)))
    (DApp 0 (DLam 0 (DVar 1 Fin.F1)) (DLam 0 (DVar 1 Fin.F1))).
Proof.
  constructor.
  - constructor. constructor. reflexivity.
  - constructor. constructor. reflexivity.
Qed.

(* A closure: a term and and environment of closure values in which to evaluate
   the term. The term is always a function body expecting one more arugment, so
   the body has depth one greater than the environment provided *)
Inductive Clo: Type :=
  | EClo (depth: nat) (body: Dxp (S depth)) (env: Vec Clo depth): Clo.

(* An environment of closure values *)
Definition Env (depth: nat): Type := Vec Clo depth.

(* Big-step reduction with closures *)
Inductive CloReduce (depth: nat) (env: Env depth): Dxp depth -> Clo -> Prop :=
  | CloVar {index: Fin depth}:
      CloReduce depth env (DVar depth index) (nth env index)
  | CloLam {body: Dxp (S depth)}:
      CloReduce depth env (DLam depth body) (EClo depth body env)
  | CloApp {fnc arg: Dxp depth}
      {fDepth: nat} {fBody: Dxp (S fDepth)} {fEnv: Env fDepth}
      {rArg result: Clo}:
      CloReduce depth env fnc (EClo fDepth fBody fEnv) ->
      CloReduce depth env arg rArg ->
      CloReduce (S fDepth) (rArg :: fEnv) fBody result ->
      CloReduce depth env (DApp depth fnc arg) result.

Example cloRedId: CloReduce 0 []
  (DLam 0 (DVar 1 Fin.F1))
  (EClo 0 (DVar 1 Fin.F1) []).
Proof.
  constructor.
Qed.
Example cloRedIdId: CloReduce 0 []
  (DApp 0 (DLam 0 (DVar 1 Fin.F1)) (DLam 0 (DVar 1 Fin.F1)))
  (EClo 0 (DVar 1 Fin.F1) []).
Proof.
  eapply CloApp.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma debruijnizable: forall (e: Exp) (ct: ClosedTerm e),
  {d: Dxp 0 | DeBruijnize 0 [] e d}.
Admitted.

Definition deBruijnized (e: Exp) (ct: ClosedTerm e): Dxp 0 :=
  match debruijnizable e ct with
  | exist d _ => d
  end.

(* One possible notion of equivalence: symbolic and closure-based reduction each
   converge when the other does. *)
Theorem ClosuresReduceWhenSymbolicExecutionReduces:
  forall (e e': Exp) (ct: ClosedTerm e) (clo: Clo),
    SymReduce e e' <-> CloReduce 0 [] (deBruijnized e ct) clo.
Admitted.

(* A stronger statement that deBruijnizing the result of symbolic execution gets the
   same result as executing the original term with closures. *)
Theorem ClosuresReduceToTheSameThingAsSymbolicExecution:
  forall (e e': Exp) (ct: ClosedTerm e) (clo clo': Clo),
    SymReduce e e' -> CloReduce 0 [] (deBruijnized e ct) clo ->
    {d': Dxp 0 | DeBruijnize 0 [] e' d' & CloReduce 0 [] d' clo}.
Admitted.