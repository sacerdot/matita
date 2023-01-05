(* The interface of this stub file is taken from the equally named module
   of the ocaml-http library *)

exception Http_error of (int * string)

val get:
 ?head_callback:(Http_types.status -> (string * string) list -> unit) ->
  string ->
    string

val get_iter:
 ?head_callback:(Http_types.status -> (string * string) list -> unit) ->
  (bytes -> unit) -> string ->
    unit

val head: string -> string
