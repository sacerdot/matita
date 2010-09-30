(* GENERATED FILE, DO NOT EDIT. STAMP:Mon May 18 11:04:27 CEST 2009 *)
val absurd : term:Cic.term -> ProofEngineTypes.tactic
val apply : term:Cic.term -> ProofEngineTypes.tactic
val applyP : term:Cic.term -> ProofEngineTypes.tactic
val applyS :
  dbd:HSql.dbd ->
  term:Cic.term ->
  params:Auto.auto_params ->
  automation_cache:AutomationCache.cache -> ProofEngineTypes.tactic
val assumption : ProofEngineTypes.tactic
val auto :
  dbd:HSql.dbd ->
  params:Auto.auto_params ->
  automation_cache:AutomationCache.cache -> ProofEngineTypes.tactic
val cases_intros :
  ?howmany:int ->
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?pattern:ProofEngineTypes.lazy_pattern ->
  Cic.term -> ProofEngineTypes.tactic
val change :
  ?with_cast:bool ->
  pattern:ProofEngineTypes.lazy_pattern ->
  Cic.lazy_term -> ProofEngineTypes.tactic
val clear : hyps:string list -> ProofEngineTypes.tactic
val clearbody : hyp:string -> ProofEngineTypes.tactic
val constructor : n:int -> ProofEngineTypes.tactic
val contradiction : ProofEngineTypes.tactic
val cut :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  Cic.term -> ProofEngineTypes.tactic
val decompose :
  ?sorts:string list ->
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  unit -> ProofEngineTypes.tactic
val demodulate :
  dbd:HSql.dbd ->
  params:Auto.auto_params ->
  automation_cache:AutomationCache.cache -> ProofEngineTypes.tactic
val destruct : Cic.term list option -> ProofEngineTypes.tactic
val elim_intros :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?depth:int ->
  ?using:Cic.term ->
  ?pattern:ProofEngineTypes.lazy_pattern ->
  Cic.term -> ProofEngineTypes.tactic
val elim_intros_simpl :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?depth:int ->
  ?using:Cic.term ->
  ?pattern:ProofEngineTypes.lazy_pattern ->
  Cic.term -> ProofEngineTypes.tactic
val elim_type :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?depth:int -> ?using:Cic.term -> Cic.term -> ProofEngineTypes.tactic
val exact : term:Cic.term -> ProofEngineTypes.tactic
val exists : ProofEngineTypes.tactic
val fail : Tacticals.tactic
val fold :
  reduction:ProofEngineTypes.lazy_reduction ->
  term:Cic.lazy_term ->
  pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val fourier : ProofEngineTypes.tactic
val fwd_simpl :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  dbd:HSql.dbd -> string -> ProofEngineTypes.tactic
val generalize :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val id : Tacticals.tactic
val intros :
  ?howmany:int ->
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  unit -> ProofEngineTypes.tactic
val inversion : term:Cic.term -> ProofEngineTypes.tactic
val lapply :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?linear:bool ->
  ?how_many:int ->
  ?to_what:Cic.term list -> Cic.term -> ProofEngineTypes.tactic
val left : ProofEngineTypes.tactic
val letin :
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  Cic.term -> ProofEngineTypes.tactic
val normalize :
  pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val reflexivity : ProofEngineTypes.tactic
val replace :
  pattern:ProofEngineTypes.lazy_pattern ->
  with_what:Cic.lazy_term -> ProofEngineTypes.tactic
val rewrite :
  direction:[ `LeftToRight | `RightToLeft ] ->
  pattern:ProofEngineTypes.lazy_pattern ->
  Cic.term -> string list -> ProofEngineTypes.tactic
val rewrite_simpl :
  direction:[ `LeftToRight | `RightToLeft ] ->
  pattern:ProofEngineTypes.lazy_pattern ->
  Cic.term -> string list -> ProofEngineTypes.tactic
val right : ProofEngineTypes.tactic
val ring : ProofEngineTypes.tactic
val simpl : pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val split : ProofEngineTypes.tactic
val symmetry : ProofEngineTypes.tactic
val transitivity : term:Cic.term -> ProofEngineTypes.tactic
val unfold :
  Cic.lazy_term option ->
  pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val whd : pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val compose :
  ?howmany:int ->
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  int -> Cic.term -> Cic.term option -> ProofEngineTypes.tactic
