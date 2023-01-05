(* The interface of this stub file is taken from the equally named module
   of the ocaml-http library *)

val send_basic_headers:
 ?version: Http_types.version -> code:Http_types.status_code ->
  out_channel ->
    unit

val send_headers:
 headers:(string * string) list -> out_channel -> unit

val send_CRLF:
  out_channel -> unit
