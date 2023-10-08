type state
type goal

val get_goals : state -> goal list

exception Parse_error of Pos.pos * string

module Command : sig
 type t
 val get_loc : t -> Ploc.t
 val pos_of_loc : text:string -> Ploc.t -> Pos.pos
end

val initial_state : string -> state
val parse_text : state -> fname:string -> string -> Command.t list * state
val handle_command : state -> Command.t -> [`Ok of state list | `Ko of exn]
val rangemap : Command.t list -> unit
