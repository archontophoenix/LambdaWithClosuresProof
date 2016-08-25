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

The small-step implementation of the closure-valued calculus used here is in the
style of an SECD machine, a technique originally described by Peter Landin in
1963 (more details appear at the start of the SECD section below). That means
that the goal is, more precisely, a proof that an SECD machine implements the
semantics of the term-rewriting call-by-value lambda calculus.

The interesting proofs below use small-step inductive type definitions for both
the term-rewriting calculus and the SECD machines, but this file also includes
the corresponding big-step definitions. The latter are generally more concise
than the small-step definitions, and so may be easier for a human reader to
understand, but are far less tractable in proofs, which often need to refer to
intermediate reduction steps that a big-step definition provides no way to
construct.
*******************************************************************************)

(* Imports from the standard library for Coq 8.4p16 *)

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.

Definition Vec (A: Type) (n: nat): Type := VectorDef.t A n.
Definition Fin (n: nat): Set := Fin.t n.
Notation "[]" := (VectorDef.nil _).
Notation "[+]" := (List.nil).
Notation "h :: t" :=
  (VectorDef.cons _ h _ t) (at level 60, right associativity).
Notation "h +: t" := (List.cons h t) (at level 60, right associativity).

Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Program.Equality.

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

(* Relations and multistep relations (see Software Foundations, Smallstep.v) **)

Definition relation (X: Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition finalState {X: Type} (R: relation X) (x: X) :=
  ~ exists x', R x x'.
                     
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R: forall (X: Type) (R: relation X) (x y: X),
  R x y -> multi R x y.
Proof.
  intros. eapply multi_step.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans: forall (X: Type) (R: relation X) (x y z: X),
  multi R x y -> multi R y z -> multi R x z.
Proof.
  intros. induction H.
  - assumption.
  - apply IHmulti in H0. eapply multi_step.
    + apply H.
    + assumption.
Qed.

Theorem multi_step': forall (X: Type) (R: relation X) (x y z: X),
  multi R x y -> R y z -> multi R x z.
Proof.
  intros. induction H.
  - eapply multi_step.
    + apply H0.
    + apply multi_refl.
  - apply IHmulti in H0. eapply multi_step.
    + apply H.
    + assumption.
Qed.

Theorem first_step__last_step: forall (X: Type) (R: relation X) (x y z: X),
  R x y -> multi R y z -> exists y', multi R x y' /\ R y' z.
Proof.
  intros. generalize dependent x. induction H0.
  - intros. exists x0. split.
    + eapply multi_refl.
    + assumption.
  - intros. apply IHmulti in H. inversion H. inversion H2. exists x1. split.
    + eapply multi_step.
      * apply H1.
      * assumption.
    + assumption.
Qed.

Lemma deterministicStepOrdering1: forall (X: Type) (R: relation X) (x y z: X),
  deterministic R -> R x y -> multi R x z ->
    (z = x \/ multi R y z).
Proof.
  unfold deterministic. intros. induction H1.
  - left. reflexivity.
  - apply (H x y y0 H0) in H1. subst. induction H2.
    + right. apply multi_refl.
    + right. eapply multi_step.
      * apply H1.
      * assumption.
Qed.

Theorem deterministicStepOrdering: forall (X: Type) (R: relation X) (x y z: X),
  deterministic R -> multi R x y -> multi R x z ->
    (multi R y z \/ multi R z y).
Proof.
  intros. induction H0.
  - left. assumption.
  - apply (deterministicStepOrdering1 X R x y z H H0) in H1. inversion H1.
    + subst. right. eapply multi_step.
      * apply H0.
      * assumption.
    + apply IHmulti in H3. assumption.
Qed.

Lemma zeroLengthDeterministicLoop: forall (X: Type) (R: relation X) (x y: X),
  deterministic R -> R x x -> multi R x y -> y = x.
Proof.
  unfold deterministic. intros. induction H1.
  - apply (H x x x) in H0.
    + assumption.
    + assumption.
  - assert (XY: x = y). { apply (H x x y H0) in H1. assumption. }
    subst. apply IHmulti. assumption.
Qed.

Theorem deterministicLoopBack: forall (X: Type) (R: relation X) (x y z: X),
  deterministic R -> R x y -> multi R y x -> multi R x z ->
    multi R z x.
Proof.
  intros. generalize dependent y. induction H2.
  - intros. apply multi_refl.
  - intros.
    assert (y0 = y). {
      unfold deterministic in H. apply (H x y0 y H1) in H0. assumption.
    } subst.
    inversion H3; subst.
    + apply IHmulti in H1.
      * assumption.
      * apply multi_refl.
    + apply IHmulti in H4.
      * apply (multi_trans X R z y x H4 H3).
      * apply (multi_step' X R y0 x y H5 H1).
Qed.

Definition fullReduce {X: Type} (R: relation X) (startX endX: X) :=
  multi R startX endX /\ finalState R endX.

Theorem infiniteLoop: forall (X: Type) (R: relation X) (x y: X),
  deterministic R -> R x y -> multi R y x -> ~ exists endX, fullReduce R x endX.
Proof.
  intros. unfold fullReduce, finalState.
  intro Contra. inversion Contra. inversion H2.
  assert (Loop: multi R x0 x). {
    apply (deterministicLoopBack X R x y x0 H H0 H1) in H3. apply H3.
  }
  inversion Loop; subst.
  - assert (Y: exists z, R x z). { exists y. assumption. }
    apply H4 in Y. apply Y.
  - assert (Y0: exists z, R x0 z). { exists y0. assumption. }
    apply H4 in Y0. apply Y0.
Qed.

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
Inductive Closed (len: nat): Ctx len -> Exp -> Type :=
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
Example notClosed: ClosedTerm (Lam 1 (Var 2)) -> False.
Proof.
  intros Contra. inversion Contra. inversion X; subst. simpl in H4.
  inversion H4.
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

Lemma SubstDeterministic: forall (e targ res0 res1: Exp) (x: nat),
  Subst e x targ res0 -> Subst e x targ res1 -> res0 = res1.
Proof.
  assert (VarContra: forall n: nat, n <> n -> False). {
    intros n Contra. assert (H: n = n). { reflexivity. }
    apply Contra in H. assumption.
  }
  intros e targ res0 res1 x H0 H1. generalize dependent res1.
  induction H0; intros res1 H1; inversion H1; subst; try reflexivity.
  - apply VarContra in H0. contradiction.
  - apply VarContra in H. contradiction.
  - apply VarContra in H2. contradiction.
  - apply VarContra in H. contradiction.
  - apply IHSubst in H6; subst. reflexivity.
  - apply IHSubst1 in H2. apply IHSubst2 in H4. subst. reflexivity.
Qed.

(* Big-step symbolic reduction ************************************************)
(* Big-step reduction is hard to work with ************************************)
(* Instead, we'll use small-step version below ********************************)

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
Example notReduceInfinite:
  ~ (exists result,
      SymReduce
        (App (Lam 0 (App (Var 0) (Var 0))) (Lam 0 (App (Var 0) (Var 0))))
        result).
Abort. (* Can't figure out how to prove this with big-step reduction. *)

(* Small-step symbolic reduction **********************************************)

Reserved Notation " t '$=>' t' " (at level 40).

(* Lams are fully reduced values; only Apps are reducible (unbound Vars are
   illegal and cannot occur in a closed program) *)
Inductive SymStep: Exp -> Exp -> Prop :=
  | SSAppL {fncL argL eL' eR: Exp}:
      App fncL argL $=> eL' ->
      App (App fncL argL) eR $=> App eL' eR
  | SSAppR {n: nat} {body fncR argR eR'}:
      App fncR argR $=> eR' ->
      App (Lam n body) (App fncR argR) $=> App (Lam n body) eR'
  | SSSubst {r l: nat} {bodyR bodyL result: Exp}:
      Subst (Lam r bodyR) l bodyL result ->
      App (Lam l bodyL) (Lam r bodyR) $=> result

where " t '$=>' t' " := (SymStep t t').              

Example symStepId:
  App (Lam 0 (Var 0)) (Lam 1 (Var 1)) $=> Lam 1 (Var 1).
Proof.
  constructor. constructor.
Qed.
Example notStepVar:
  ~ exists p, Var 0 $=> p.
Proof.
  intros Contra. inversion Contra. inversion H.
Qed.

Theorem SymStepDeterministic: deterministic SymStep.
Proof.
  unfold deterministic. intros. generalize dependent y2.
  induction H; intros.
  - inversion H0; subst. apply IHSymStep in H5; subst. reflexivity.
  - inversion H0; subst. apply IHSymStep in H6; subst. reflexivity.
  - inversion H0; subst. eapply SubstDeterministic.
    + apply H.
    + apply H6.
Qed.

(* DeBruijnization: replacement of symbolic variable names with indices *******)

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

Lemma debruijnizable: forall (e: Exp) (ct: ClosedTerm e),
  {d: Dxp 0 | DeBruijnize 0 [] e d}.
Proof.
  unfold ClosedTerm. intros e C. induction C.
  - exists (DVar len pos). constructor. assumption.
  - inversion IHC. exists (DLam len x). constructor. assumption.
  - inversion IHC1. inversion IHC2.
    exists (DApp len x x0). constructor.
    + assumption.
    + assumption.
Qed.

Definition deBruijnized (e: Exp) (ct: ClosedTerm e): Dxp 0 :=
  match debruijnizable e ct with
  | exist d _ => d
  end.

(* Closures and environments **************************************************)

(* A closure: a term and and environment of closure values in which to evaluate
   the term. The term is always a function body expecting one more arugment, so
   the body has depth one greater than the environment provided *)
Inductive Clo: Type :=
  | EClo (depth: nat) (body: Dxp (S depth)) (env: Vec Clo depth): Clo.

(* An environment of closure values *)
Definition Env (depth: nat): Type := Vec Clo depth.

(* Big-step reduction of deBruijnized terms with closures *********************)
(* Big-step reduction is hard to work with ************************************)
(* Instead, we'll use small-step version below ********************************)

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

(* Small-step reduction of deBruijnized terms in SECD style *******************)

(*******************************************************************************
The SECD machine implementation here is loosely based on Olivier Danvy's "A
Rational Deconstruction of Landin's SECD Machine"
(http://ojs.statsbiblioteket.dk/index.php/brics/article/download/21801/19232).

The SECD machine is named for the four components of its state:

. Stack: a stack of temporary values, local to the current function. The
  elements of this stack are closures (Clo), because all values are closures.

. Environment: a stack of bindings (closures) for the variables (that is,
  parameters for enclosing functions) visible at this point in the program. The
  topmost binding is for the innermost enclosing function's parameter, with
  successive entries farther down the stack, so that entries in the environment
  are looked up by their deBruijn indices.

. Control: a stack of instructions for the current function. An instruction is
  either a lambda calculus term, or the special instruction Apply, which is used
  to keep track of which Stack values represent functions and which represent
  arguments. The next instruction to execute is the top element of Control.

. Dump: a stack of (Stack,Environment,Control) triples, used to save and restore
  the state when making a function call.

One might have wished for a better nomenclature. For example, why is one
state componenent called Stack, when they are all in fact stacks? Furthermore,
dispatch is based on the top element of Control -- wouldn't it read better if
Control were first, since that's what you look at first? Ah well, that's the
burden of tradition.

An SECD machine run in an empty environment on a closed program in our lambda
calculus can be in one of six states, mostly distinguished by the top element of
Control. Here are the states and the actions taken in each; unless otherwise
noted, each action first pops off the top instruction from Control:

. Var next: look up the variable in Environment and push the result on Stack.

. Lam next: wrap the lambda in a closure and push the result on Stack.

. App next: push (in reverse order) the function and argument parts of App and
  the special instruction Apply onto Control. This will (eventually, if
  evaluation terminates) cause the machine to evaluate the function and argument
  and push each onto Stack in preparation for a function call.

. Apply next: call the function whose closure is the next-to-top element of
  Stack; the function's argument is the top element of Stack. This entails
  pushing the current (Stack,Environment,Control) onto Dump, and setting
  Stack, Environment, and Control, respectively, to empty, the function argument
  pushed onto the environment part of the function closure, and the body of the
  function.

. Empty Control, nonempty Dump: return from the current function. There is a
  single item R (the function's return value) on Stack. Restore the old Stack,
  Environment, and Control from Dump, then push R onto Stack.

. Empty Control, empty Dump: this is the terminal state of a program. There is a
  single item, the program's result, on Stack. No step is possible from this
  state, which is why SECDStep below has only 5 constructors, not 6.
*******************************************************************************)

(* An instruction is a deBruijnized lambda calculus term or Apply *)
Inductive Instruction (depth: nat) :=
  | IDxp: Dxp depth -> Instruction depth
  | Apply: Instruction depth.

(* SECD state component definitions *)
Definition Stack := list Clo.
Definition Environment := Env.
Definition Control (depth: nat) := list (Instruction depth).
(* A (Stack,Environment,Control) triple. Can't be expressed as a simple product
   because of the dependency: the environment depths for the Environment and
   Control components must match  *)
Inductive SEC: Type :=
  | Sec {depth: nat}: Stack -> Env depth -> Control depth -> SEC.
Definition Dump := list SEC.

(* A complete SECD state is a (Stack,Environment,Control) triple plus Dump *)
Inductive SECD: Type :=
  | Secd: SEC -> Dump -> SECD.

Reserved Notation " t '%=>' t' " (at level 40).

(* A single step of the SECD machine *)
Inductive SECDStep: SECD -> SECD -> Prop :=
  (* Var next *)
  | LookUpVar {s: Stack} {depth: nat} {e: Env depth} {index: Fin depth}
        {clo: Clo} {c: Control depth} {d: Dump}:
      nth e index = clo ->
      Secd (Sec s e (IDxp depth (DVar depth index) +: c)) d %=>
        Secd (Sec (clo +: s) e c) d
  (* Lam next *)
  | LamToClosure {s: Stack} {depth: nat} {e: Env depth} {body: Dxp (S depth)}
        {c: Control depth} {d: Dump}:
      Secd (Sec s e (IDxp depth (DLam depth body) +: c)) d %=>
        Secd (Sec ((EClo depth body e) +: s) e c) d
  (* App next *)
  | AppToApply {s: Stack} {depth: nat} {e: Env depth} {fnc arg: Dxp depth}
        {c: Control depth} {d: Dump}:
      Secd (Sec s e (IDxp depth (DApp depth fnc arg) +: c)) d %=>
        Secd (Sec s e (IDxp depth fnc +: IDxp depth arg +: Apply depth +: c)) d
  (* Apply next *)
  | CallFunction {arg: Clo} {cloDepth depth: nat} {cloBody: Dxp (S cloDepth)}
        {cloEnv: Env cloDepth} {s: Stack} {e: Env depth} {c: Control depth}
        {d: Dump}:
      Secd
        (Sec (arg +: EClo cloDepth cloBody cloEnv +: s) e (Apply depth +: c))
        d
          %=>
      Secd
        (Sec [+] (arg :: cloEnv) (IDxp (S cloDepth) cloBody +: [+]))
        ((Sec s e c) +: d)
  (* Empty Control, nonempty Dump *)
  | ReturnFromFunction
        {rtnVal: Clo} {curDepth oldDepth: nat} {e: Env curDepth}
        {oldS: Stack} {oldE: Env oldDepth} {oldC: Control oldDepth}
        {oldD: Dump}:
      Secd (Sec (rtnVal +: [+]) e [+]) ((Sec oldS oldE oldC) +: oldD) %=>
        Secd (Sec (rtnVal +: oldS) oldE oldC) oldD
        
where " t '%=>' t' " := (SECDStep t t').

Definition idBody: Dxp 1 := DVar 1 Fin.F1. (* Body of identity function *)
Definition id: Dxp 0 := DLam 0 idBody. (* Identity function id *) 
Definition applyIdToId: Dxp 0 := DApp 0 id id. (* id id *)
Definition instrId: Instruction 0 := IDxp 0 id. (* id as instruction *)
Definition cloId: Clo := EClo 0 idBody []. (* id as closure *)
Example SECDStepIdId0:
  Secd (Sec [+] [] (IDxp 0 applyIdToId +: [+])) [+]
    %=>
  Secd (Sec [+] [] (instrId +: instrId +: Apply 0 +: [+])) [+].
Proof. apply AppToApply. Qed.
Example SECDStepIdId1:
  Secd (Sec [+] [] (instrId +: instrId +: Apply 0 +: [+])) [+]
    %=>
  Secd (Sec (cloId +: [+]) [] (instrId +: Apply 0 +: [+])) [+].
Proof. apply LamToClosure. Qed.
Example SECDStepIdId2:
  Secd (Sec (cloId +: [+]) [] (instrId +: Apply 0 +: [+])) [+]
    %=>
  Secd (Sec (cloId +: cloId +: [+]) [] (Apply 0 +: [+])) [+].
Proof. apply LamToClosure. Qed.
Example SECDStepIdId3:
  Secd (Sec (cloId +: cloId +: [+]) [] (Apply 0 +: [+])) [+]
    %=>
  Secd (Sec [+] (cloId :: []) (IDxp 1 idBody +: [+])) (Sec [+] [] [+] +: [+]).
Proof. apply CallFunction. Qed.
Example SECDStepIdId4:
  Secd (Sec [+] (cloId :: []) (IDxp 1 idBody +: [+])) (Sec [+] [] [+] +: [+])
    %=>
  Secd (Sec (cloId +: [+]) (cloId :: []) [+]) (Sec [+] [] [+] +: [+]).
Proof. apply LookUpVar. reflexivity. Qed.
Example SECDStepIdId5:
  Secd (Sec (cloId +: [+]) (cloId :: []) [+]) (Sec [+] [] [+] +: [+])
    %=>
  Secd (Sec (cloId +: [+]) [] [+]) [+].
Proof. apply ReturnFromFunction. Qed.
Example SECDStepIdIdDone:
  ~ exists x, Secd (Sec (cloId +: [+]) [] [+]) [+] %=> x.
Proof.
  intros Contra. inversion Contra. inversion H.
Qed.

(* Thanks to John Wiegley and John Major: *)
Lemma dependentSame: forall {A: Type} (P: A -> Type) (x: A) (p0 p1: P x),
  existT P x p0 = existT P x p1 -> p0 = p1.
Proof.
  intros. apply eq_sigT_eq_dep in H. dependent destruction H. reflexivity.
Qed.

Theorem SECDStepDeterministic: deterministic SECDStep.
Proof.
  unfold deterministic. intros. generalize dependent y2.
  induction H; intros; try (inversion H0; subst).
  - apply dependentSame in H4. apply dependentSame in H5.
    apply dependentSame in H6. subst. reflexivity.
  - apply dependentSame in H3. apply dependentSame in H4.
    apply dependentSame in H5. subst. reflexivity.
  - apply dependentSame in H3. apply dependentSame in H4.
    apply dependentSame in H5. apply dependentSame in H6.
    subst. reflexivity.
  - apply dependentSame in H4. apply dependentSame in H5.
    apply dependentSame in H7. apply dependentSame in H8.
    subst. reflexivity.
  - apply dependentSame in H3. apply dependentSame in H6.
    apply dependentSame in H7. subst. reflexivity.
Qed.

(* A closed deBruijnized lamba term in an empty environment, ready to run *)
Definition runnableProgram (e: Exp) (ct: ClosedTerm e): SECD :=
  Secd (Sec [+] [] (IDxp 0 (deBruijnized e ct) +: [+])) [+].

(* Fully reducing a closed term always yields a one-item Stack, empty Control,
   and empty Dump *)
Lemma SECDFinalState: forall {depth: nat}
    (e: Exp) (ct: ClosedTerm e) (st: Stack) (env: Env depth)
    (ctrl: Control depth) (dmp: Dump),
  fullReduce SECDStep (runnableProgram e ct) (Secd (Sec st env ctrl) dmp) ->
    (length st = 1 /\ ctrl = [+] /\ dmp = [+]).
Admitted.

(* The goal *******************************************************************)

(* Symbolic execution should terminate iff SECD execution terminates *)
Theorem termRewriteTerminatesIffSECDTerminates:
  forall (e: Exp) (ct: ClosedTerm e),
    (exists e', fullReduce SymStep e e') <->
      (exists secd', fullReduce SECDStep (runnableProgram e ct) secd').
Admitted.

(* If execution terminates, then running before deBruijnizing should yield the
   same result as deBruijnizing before running *)
Theorem termRewriteEquivSECD: forall {depth: nat}
    (e e': Exp) (ct: ClosedTerm e) (st: Stack) (env: Env depth)
    (ctrl: Control depth) (dmp: Dump) (body: Dxp 1),
  fullReduce SymStep e e' ->
  fullReduce SECDStep (runnableProgram e ct) (Secd (Sec st env ctrl) dmp) ->
  DeBruijnize 0 [] e' (DLam 0 body) -> (* TODO: show this always holds! *)
  st = (EClo 0 body []) +: [+].
Admitted.
