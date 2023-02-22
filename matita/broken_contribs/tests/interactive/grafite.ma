

(* commento *)
(** hint. *)

inductive pippo : Type \def
  | a : Type \to pippo
  | b : Prop \to pippo
  | c : Set \to pippo.

definition pollo : Set \to Set \def
  \lambda a:Set.a.

inductive paolo : Prop \def t:paolo.

theorem comeno : \forall p:pippo.pippo.
intros.assumption.
qed.

definition f : pippo \to paolo \def
  \lambda x:pippo.
  match x with 
  [ (a z) \Rightarrow t
  | (b z) \Rightarrow t
  | (c z) \Rightarrow t ].

record w : Type \def {
  mario : Prop;
  pippo : Set
}.

whelp locate pippo.

print "coercions".
