exception Impossible of int
exception NotWellTyped of string
exception WrongUriToConstant of string
exception WrongUriToVariable of string
exception WrongUriToMutualInductiveDefinitions of string
exception ListTooShort
exception RelToHiddenHypothesis

type types = {synthesized : Cic.term ; expected : Cic.term option};;

val pack_coercion : (Cic.metasenv -> Cic.context -> Cic.term -> Cic.term) ref;;

val double_type_of :
 Cic.metasenv -> Cic.context -> Cic.term -> Cic.term option ->
  types Cic.CicHash.t

(** Auxiliary functions **)

(* does_not_occur n te                              *)
(* returns [true] if [Rel n] does not occur in [te] *)
val does_not_occur : int -> Cic.term -> bool
