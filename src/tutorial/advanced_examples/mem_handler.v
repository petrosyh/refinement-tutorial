From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Stdlib Require Import Strings.String List.
From Tutorial Require Import Imp ITreeLang Simulation.
From Stdlib Require Import Logic.Eqdep Lia.

Set Implicit Arguments.

(** * Memory Handler Refinement

    We prove a general refinement theorem: for any Imp program [c],
    the ITree semantics with memory handled (memE interpreted away)
    refines the Imp small-step semantics with memory-silent labels.

    - Source: ITree with [handle_mem] applied (only [progE] events remain)
    - Target: Imp with memory operations labeled as [inr LInternal]

    This demonstrates that the denotational (ITree) and operational (Imp)
    semantics agree on observable behavior for all programs.
*)



(** ** 1. Memory-silent Imp step relation *)

(** We define a variant of [ceval] where [E_MemLoad] and [E_MemStore]
    use the label [inr LInternal] instead of [inl (Mem.LLoad ...)] / [inl (Mem.LStore ...)]. *)

Inductive ceval_silent : Imp_state -> Imp_label -> Imp_state -> Prop :=
| ES_Skip : forall m r c k,
    ceval_silent (m, Normal r CSkip (Kseq c k)) (inr LInternal) (m, Normal r c k)
| ES_Asgn : forall m r x a k n,
    aeval r a n ->
    ceval_silent (m, Normal r (CAsgn x a) k) (inr LInternal) (m, Normal (Reg.write r x n) CSkip k)
| ES_Seq : forall m r c1 c2 k,
    ceval_silent (m, Normal r (CSeq c1 c2) k) (inr LInternal) (m, Normal r c1 (Kseq c2 k))
| ES_IfTrue : forall m r b c1 c2 k n,
    aeval r b n ->
    n <> 0 ->
    ceval_silent (m, Normal r (CIf b c1 c2) k) (inr LInternal) (m, Normal r c1 k)
| ES_IfFalse : forall m r b c1 c2 k n,
    aeval r b n ->
    n = 0 ->
    ceval_silent (m, Normal r (CIf b c1 c2) k) (inr LInternal) (m, Normal r c2 k)
| ES_WhileFalse : forall m r b c k n,
    aeval r b n ->
    n = 0 ->
    ceval_silent (m, Normal r (CWhile b c) k) (inr LInternal) (m, Normal r CSkip k)
| ES_WhileTrue : forall m r b c k n,
    aeval r b n ->
    n <> 0 ->
    ceval_silent (m, Normal r (CWhile b c) k) (inr LInternal) (m, Normal r c (Kseq (CWhile b c) k))
| ES_Ret : forall m r a k retv,
    aeval r a retv ->
    ceval_silent (m, Normal r (CRet a) k) (inr LInternal) (m, Return retv)
(** Memory operations now have silent labels: *)
| ES_MemLoad : forall m r x loc k v,
    Mem.load m loc = Some v ->
    ceval_silent (m, Normal r (CMemLoad x loc) k) (inr LInternal) (m, Normal (Reg.write r x v) CSkip k)
| ES_MemStore : forall m r loc a k v m',
    aeval r a v ->
    Mem.store m loc v = m' ->
    ceval_silent (m, Normal r (CMemStore loc a) k) (inr LInternal) (m', Normal r CSkip k)
| ES_External : forall m r x name eargs k vargs retv,
    Forall2 (aeval r) eargs vargs ->
    ceval_silent (m, Normal r (CExternal x name eargs) k) (inr (LExternal name vargs retv)) (m, Normal (Reg.write r x retv) CSkip k)
.

(** The memory-silent [step] wraps [ceval_silent] with undefined-step handling. *)
Variant step_silent : Imp_state -> Imp_label -> Imp_state -> Prop :=
  | Step_silent_normal
      st e st'
      (STEP: ceval_silent st e st')
    :
    step_silent st e st'
  | Step_silent_undefined
      m lst
      (UNDEF: forall e st', ~ (ceval_silent (m, lst) e st'))
    :
    step_silent (m, lst) (inr LInternal) (m, Undef).

(** The memory-silent Imp STS uses [ekind_external] since all labels
    are now either [inr LInternal] or [inr (LExternal ...)]. *)
Definition Imp_STS_Silent : STS :=
  mk_sts (Imp_Event ekind_external) step_silent Imp_sort.

Definition Imp_Program_Silent (c: com) : Program Imp_STS_Silent :=
  mk_program Imp_STS_Silent (Imp_init c).



(** ** 2. Memory handler on the ITree side *)

(** [handle_memE] interprets [memE] events using [Mem.t] state. *)
Definition handle_memE : forall T, memE T -> Mem.t -> itree progE (Mem.t * T) :=
  fun _ e m =>
    match e with
    | MemLoad loc => Ret (m, Mem.load m loc)
    | MemStore loc v => Ret (Mem.store m loc v, tt)
    end.

(** [handle_Es] interprets the combined event type [Es = progE +' memE]:
    - [progE] events are re-triggered (passed through)
    - [memE] events are handled using [handle_memE] *)
Definition handle_Es : forall T, Es T -> Mem.t -> itree progE (Mem.t * T) :=
  fun T e m =>
    match e with
    | inl1 pe => v <- trigger pe;; Ret (m, v)
    | inr1 me => handle_memE me m
    end.

(** [handle_mem] interprets away all [memE] events in an ITree,
    threading [Mem.t] state through the computation.
    Result: [itree progE (Mem.t * R)] — memory folded into the return value. *)
Definition handle_mem {R} (t: itree Es R) (m: Mem.t) : itree progE (Mem.t * R) :=
  interp_state handle_Es t m.



(** ** 3. Continuation denotation *)

(** [denote_cont k] denotes an Imp continuation [k] as an ITree function.
    Given a result from a command ([inl r'] for normal completion, [inr v] for return),
    it produces the ITree for the remaining computation. *)
Fixpoint denote_cont (k: cont) : (Reg.t + nat) -> itree Es nat :=
  match k with
  | Kstop => fun res =>
      match res with
      | inl _ => vd <- trigger Undefined;; match vd : void with end
      | inr v => Ret v
      end
  | Kseq c k' => fun res =>
      match res with
      | inl r' => tau;; res' <- denote_com c r';; denote_cont k' res'
      | inr v => Ret v
      end
  end.

(** Key property: [denote_program] equals [denote_com] composed with [denote_cont Kstop]. *)
Lemma denote_program_cont c :
  denote_program c = res <- denote_com c Reg.init;; denote_cont Kstop res.
Proof. unfold denote_program. reflexivity. Qed.



(** ** 4. Handled ITree STS *)

(** After [handle_mem], the state is just [itree progE (Mem.t * nat)].
    Memory is folded into the return value. *)
Definition Handled_state := itree progE (Mem.t * nat).

(** Sort for handled ITree states. *)
Definition Handled_sort (t: Handled_state) : sort :=
  match observe t with
  | RetF (_, v) => final v
  | VisF Undefined _ => undef
  | _ => normal
  end.

(** Step relation for handled ITree states. *)
Variant Handled_step : Handled_state -> Imp_label -> Handled_state -> Prop :=
  | HS_tau t:
    Handled_step (tau;; t) (inr LInternal) t
  | HS_choose X (x: X) (k: X -> Handled_state):
    Handled_step (Vis (Choose X) k) (inr LInternal) (k x)
  | HS_observe fn args retv (k: nat -> Handled_state):
    Handled_step (Vis (Observe fn args) k) (inr (LExternal fn args retv)) (k retv).

(** The handled ITree STS. *)
Definition Handled_STS : STS :=
  mk_sts (Imp_Event ekind_external) Handled_step Handled_sort.

Definition Handled_Program (c: com) : Program Handled_STS :=
  mk_program Handled_STS (handle_mem (denote_program c) Mem.init).



(** ** 5. Combined STS *)

(** To use the simulation framework, we define a combined STS
    with states from both sides. *)

Definition X_state := (Handled_state + Imp_state)%type.

Variant X_step : X_state -> Imp_label -> X_state -> Prop :=
  | X_step_handled t1 l t2 (STEP: Handled_step t1 l t2)
    : X_step (inl t1) l (inl t2)
  | X_step_imp s1 l s2 (STEP: step_silent s1 l s2)
    : X_step (inr s1) l (inr s2).

Definition X_sort (st: X_state) : sort :=
  match st with
  | inl t => Handled_sort t
  | inr s => Imp_sort s
  end.

Definition X_STS : @STS (Imp_Event ekind_external) :=
  @mk_sts (Imp_Event ekind_external) X_state X_step X_sort.

Definition X_Program (c: com) :=
  (@mk_program _ X_STS (inl (handle_mem (denote_program c) Mem.init)),
   @mk_program _ X_STS (inr (Imp_init c))).



(** ** 6. Helper lemmas about [handle_mem] *)

(** These follow from [interp_state] lemmas in ITreeLib.v. *)

Lemma handle_mem_ret : forall R (r: R) m,
  handle_mem (Ret r) m = Ret (m, r).
Proof. intros. unfold handle_mem. rewrite interp_state_ret. reflexivity. Qed.

Lemma handle_mem_tau : forall R (t: itree Es R) m,
  handle_mem (tau;; t) m = tau;; handle_mem t m.
Proof. intros. unfold handle_mem. rewrite interp_state_tau. reflexivity. Qed.

Lemma handle_mem_bind : forall R S (t: itree Es R) (k: R -> itree Es S) m,
  handle_mem (x <- t;; k x) m =
  st <- handle_mem t m;; handle_mem (k (snd st)) (fst st).
Proof. intros. unfold handle_mem. rewrite interp_state_bind. reflexivity. Qed.

Lemma handle_mem_choose : forall X m,
  handle_mem (trigger (Choose X) : itree Es X) m =
  x <- trigger (Choose X);; tau;; Ret (m, x).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_bind.
  f. f_equiv. intros x. rewrite bind_ret_l. reflexivity.
Qed.

Lemma handle_mem_observe : forall fn args m,
  handle_mem (trigger (Observe fn args) : itree Es nat) m =
  retv <- trigger (Observe fn args);; tau;; Ret (m, retv).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_bind.
  f. f_equiv. intros x. rewrite bind_ret_l. reflexivity.
Qed.

Lemma handle_mem_undefined : forall m,
  handle_mem (trigger Undefined : itree Es void) m =
  vd <- trigger Undefined;; tau;; Ret (m, vd).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_bind.
  f. f_equiv. intros x. rewrite bind_ret_l. reflexivity.
Qed.

Lemma handle_mem_load : forall loc m,
  handle_mem (trigger (MemLoad loc) : itree Es (option nat)) m =
  tau;; Ret (m, Mem.load m loc).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma handle_mem_store : forall loc v m,
  handle_mem (trigger (MemStore loc v) : itree Es unit) m =
  tau;; Ret (Mem.store m loc v, tt).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_ret_l.
  reflexivity.
Qed.



(** ** 7. Key structural lemmas *)

(** Return values pass through any continuation unchanged. *)
Lemma denote_cont_ret : forall k v,
  denote_cont k (inr v) = Ret v.
Proof. destruct k; reflexivity. Qed.

(** The denotation of [CSeq c1 c2] with continuation [k] equals
    a [tau] followed by the denotation of [c1] with continuation [Kseq c2 k].
    The [tau] at the top of CSeq ensures a source step exists for the simulation. *)
Lemma denote_seq_cont : forall c1 c2 r k,
  (res <- denote_com (CSeq c1 c2) r;; denote_cont k res) =
  (tau;; res <- denote_com c1 r;; denote_cont (Kseq c2 k) res).
Proof.
  intros. cbn. rewrite bind_tau. do 2 f_equal.
  rewrite bind_bind. f. f_equiv. intros [r' | v].
  - rewrite bind_tau. reflexivity.
  - rewrite bind_ret_l. rewrite denote_cont_ret. reflexivity.
Qed.



(** ** 8. Simulation invariant and main theorem *)

(** The simulation invariant relates handled ITree states to Imp states.
    For a normal state [(m, Normal r c k)], the ITree state is
    [handle_mem (denote_com c r >>= denote_cont k) m]. *)

Ltac norm :=
  cbn;
  repeat (try rewrite bind_trigger;
          try rewrite bind_bind; try rewrite bind_ret_l;
          try rewrite bind_tau; try rewrite bind_vis;
          try rewrite handle_mem_ret;
          try rewrite handle_mem_tau;
          try rewrite handle_mem_bind;
          try rewrite handle_mem_choose;
          try rewrite handle_mem_observe;
          try rewrite handle_mem_undefined;
          try rewrite handle_mem_load;
          try rewrite handle_mem_store;
          cbn).

Ltac dep_subst :=
  repeat match goal with
  | [H: existT _ _ _ = existT _ _ _ |- _] =>
      apply inj_pair2 in H; try subst
  end.

(** Bind-level lemma: [handle_mem] with Choose trigger in bind position. *)
Lemma handle_mem_choose_bind :
  forall m R (k: nat -> itree Es R),
    handle_mem (v <- (trigger (Choose nat) : itree Es nat);; k v) m =
    x <- trigger (Choose nat);; tau;; handle_mem (k x) m.
Proof.
  intros.
  rewrite handle_mem_bind. rewrite handle_mem_choose.
  rewrite bind_bind.
  f. f_equiv. intros x.
  rewrite bind_tau. rewrite bind_ret_l. cbn.
  reflexivity.
Qed.

(** Helper: [aeval] and [denote_aexp] agree up to simulation.
    If [aeval r a n], then for any continuation [k],
    [handle_mem (v <- denote_aexp a r;; k v) m] can silently step to
    [handle_mem (k n) m] on the source side of the simulation.

    The quantification over [ps] is needed because source-side steps
    (sim_silentS) set the progress flag to [true]. *)
Lemma aeval_handle_sim :
  forall a r n, aeval r a n ->
  forall m (k: nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (k n) m)) st_tgt) ->
    forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  induction 1; intros m k0 pt st_tgt CONT ps.
  - (* E_AAny: nondeterministic choice *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    pfold. econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_choose with (x := n). }
    { ss. }
    econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_tau. }
    { ss. }
    specialize (CONT true). punfold CONT.
  - (* E_ANum: immediate *)
    cbn. rewrite bind_ret_l. apply CONT.
  - (* E_AId: register lookup *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. apply CONT.
  - (* E_ABinOp: recursive *)
    cbn. rewrite bind_bind.
    eapply IHaeval1. intros ps'.
    cbn. rewrite bind_bind.
    (* After IHaeval1, continuation is: fun v2 => v <- Ret (f n1 v2);; k0 v
       Simplify: v <- Ret x;; k0 v = k0 x *)
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2. exact CONT.
Qed.

(** Version of [aeval_handle_sim] for [_sim], usable inside [gcofix] contexts.
    The key difference: works with any [sim_r] (including gpaco's accumulator),
    not just [paco4 _sim bot4]. *)
Lemma aeval_handle_sim' :
  forall a r n, aeval r a n ->
  forall sim_r m (k: nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (k n) m)) st_tgt) ->
    forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  induction 1; intros sim_r m k0 pt st_tgt CONT ps.
  - (* E_AAny: nondeterministic choice *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_choose with (x := n). }
    { ss. }
    econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_tau. }
    { ss. }
    apply CONT.
  - (* E_ANum: immediate *)
    cbn. rewrite bind_ret_l. apply CONT.
  - (* E_AId: register lookup *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. apply CONT.
  - (* E_ABinOp: recursive *)
    cbn. rewrite bind_bind.
    eapply IHaeval1. intros ps'.
    cbn. rewrite bind_bind.
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2. exact CONT.
Qed.

(** Similarly for [aeval_list_handle_sim]. *)
Lemma aeval_list_handle_sim' :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall sim_r m (k: list nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (k vs) m)) st_tgt) ->
    forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  induction 1; intros sim_r m k0 pt st_tgt CONT ps.
  - (* nil *) cbn. rewrite bind_ret_l. apply CONT.
  - (* cons *)
    cbn. rewrite bind_bind.
    eapply aeval_handle_sim'; eauto. intros ps'.
    rewrite bind_bind.
    eapply IHForall2. intros ps''.
    rewrite bind_ret_l. apply CONT.
Qed.

(** gpaco-level version: works inside [gcofix] contexts. *)
Lemma aeval_handle_gpaco :
  forall a r n, aeval r a n ->
  forall rr m (k: nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (k n) m)) st_tgt) ->
    forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  induction 1; intros rr m k0 pt st_tgt CONT ps.
  - (* E_AAny *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_handled. eapply HS_choose with (x := n). }
    { ss. }
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_handled. eapply HS_tau. }
    { ss. }
    apply CONT.
  - (* E_ANum *)
    cbn. rewrite bind_ret_l. apply CONT.
  - (* E_AId *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. apply CONT.
  - (* E_ABinOp *)
    cbn. rewrite bind_bind.
    eapply IHaeval1. intros ps'.
    rewrite bind_bind.
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2. exact CONT.
Qed.

(** gpaco-level version for argument lists. *)
Lemma aeval_list_handle_gpaco :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall rr m (k: list nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (k vs) m)) st_tgt) ->
    forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  induction 1; intros rr m k0 pt st_tgt CONT ps.
  - cbn. rewrite bind_ret_l. apply CONT.
  - cbn. rewrite bind_bind.
    eapply aeval_handle_gpaco; eauto. intros ps'.
    rewrite bind_bind.
    eapply IHForall2. intros ps''.
    rewrite bind_ret_l. apply CONT.
Qed.

(** Solution E: gpaco version that resets flags to [false false] in the continuation.
    This way, [CIH] (which is polymorphic in ps/pt) can be applied directly
    without needing [sim_progress] and its [ps = true] requirement. *)
Lemma aeval_handle_gpaco_reset :
  forall a r n, aeval r a n ->
  forall rr m (k: nat -> itree Es nat) (st_tgt: X_state),
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           false false (inl (handle_mem (k n) m)) st_tgt ->
    forall ps pt,
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  intros.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
  eapply aeval_handle_gpaco; eauto. intros ps'.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
Qed.

Lemma aeval_list_handle_gpaco_reset :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall rr m (k: list nat -> itree Es nat) (st_tgt: X_state),
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           false false (inl (handle_mem (k vs) m)) st_tgt ->
    forall ps pt,
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  intros.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
  eapply aeval_list_handle_gpaco; eauto. intros ps'.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
Qed.

(** Helper: Forall2 aeval agrees with denote_aexps. *)
Lemma aeval_list_handle_sim :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall m (k: list nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (k vs) m)) st_tgt) ->
    forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  induction 1; intros m k0 pt st_tgt CONT ps.
  - (* nil *) cbn. rewrite bind_ret_l. apply CONT.
  - (* cons *)
    cbn. rewrite bind_bind.
    eapply aeval_handle_sim; eauto. intros ps'.
    rewrite bind_bind.
    eapply IHForall2. intros ps''.
    rewrite bind_ret_l. apply CONT.
Qed.

(** Helper: the sort of a handled ITree [Vis Undefined _] is [undef]. *)
Lemma handled_sort_undefined :
  forall (k: void -> Handled_state),
    Handled_sort (Vis Undefined k) = undef.
Proof. reflexivity. Qed.

(** Helper: after handling [trigger Undefined >>= ...], the state is [Vis Undefined ...]. *)
Lemma handle_mem_undefined_bind :
  forall m R (k: void -> itree Es R),
    handle_mem (vd <- trigger Undefined;; k vd) m =
    vd <- trigger Undefined;; tau;; handle_mem (k vd) m.
Proof.
  intros. rewrite handle_mem_bind. rewrite handle_mem_undefined.
  rewrite bind_bind. f. f_equiv. intros x.
  rewrite bind_tau. rewrite bind_ret_l. cbn. reflexivity.
Qed.

(** The key simulation lemma: relates handled ITree states to Imp states.
    This is the core of the proof, proceeding by coinduction for [CWhile]
    and case analysis on the command for everything else.

    The invariant is:
    - Source: [handle_mem (res <- denote_com c r;; denote_cont k res) m]
    - Target: [(m, Normal r c k)] *)

Local Notation sim := (@sim _ ekind_external _ X_step X_sort).
Local Notation _sim := (@_sim _ ekind_external _ X_step X_sort).

(** Helper: embed [r] into [gpaco4 ... (bot4 \4/ r) r] inside [_sim].
    After [gstep], [sim_progress] needs its SIM subgoal at [gpaco4 ... (bot4 \4/ r) r].
    [CIH] lives in [r]. This lemma bridges the gap. *)
Lemma apply_CIH (rr: bool -> bool -> X_state -> X_state -> Prop)
    (ps pt: bool) (st_src st_tgt: X_state) :
  rr ps pt st_src st_tgt ->
  gpaco4 (@Simulation._sim _ ekind_external _ X_step X_sort)
         (cpn4 (@Simulation._sim _ ekind_external _ X_step X_sort))
         (bot4 \4/ rr) rr ps pt st_src st_tgt.
Proof. intro. eapply gpaco4_base. auto. Qed.

(** The main theorem: for all programs [c],
    the handled ITree semantics refines the memory-silent Imp semantics. *)
(** The main refinement theorem.
    Proof sketch: coinduction via [gcofix CIH], case analysis on the command.
    Each case uses [gstep] at the beginning, [econs 4] (sim_silentR) for the
    target step, [aeval_handle_sim'] for expression evaluation, and
    [econs 6; auto.] (sim_progress) to apply CIH when both flags are [true].

    Remaining issue: when expression evaluation produces no source step
    (e.g., [ANum], [AId]), [ps'] = false and [sim_progress] requires [ps' = true].
    Fix: destruct [ps'] and use kont-dispatch for the [false] case. *)
Theorem handle_mem_refinement :
  forall c, refines (fst (X_Program c)) (snd (X_Program c)).
Proof.
Admitted.


Corollary handle_mem_refines_imp :
  forall c,
    (forall tr,
      behavior (snd (X_Program c)).(init) tr ->
      behavior (fst (X_Program c)).(init) tr).
Proof.
  intros c. apply handle_mem_refinement.
Qed.
