
module type Format =
  sig
    type source_object
    type target_object
    val target_of : source_object -> target_object
    val string_of_source_object : source_object -> string
    val string_of_target_object : target_object -> string
    val build : source_object -> bool
    val mtime_of_source_object : source_object -> float option
    val mtime_of_target_object : target_object -> float option
  end

module Make :
  functor (F : Format) ->
    sig
      (* make [deps] [targets], targets = [] means make all *)
      val make : (F.source_object * F.source_object list) list ->
                 F.source_object list ->  unit
    end

val load_deps_file: string -> (string * string list) list
