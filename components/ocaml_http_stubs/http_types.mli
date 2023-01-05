(* The interface of this stub file is taken from the equally named module
   of the ocaml-http library *)

type version
type status
type status_code = [ `Code of int | `Status of status ]
