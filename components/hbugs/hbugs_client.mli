
open Hbugs_types

exception Invalid_URL of string

  (*
    @param use_hint_callback is called when the user double click on a hint
    (default: do nothing)
    @param describe_hint_callback is called when the user click on a hint
    (default: do nothing)
  *)
class hbugsClient :
  ?use_hint_callback: (hint -> unit) ->
  ?describe_hint_callback: (hint -> unit) ->
  ?destroy_callback: (unit -> unit) ->
  unit ->
    object

      method show : unit -> unit
      method hide : unit -> unit

      method setUseHintCallback : (hint -> unit) -> unit
      method registerToBroker : unit -> unit
      method unregisterFromBroker : unit -> unit
      method subscribeAll : unit -> unit

      method stateChange : state option -> unit

        (** @return an hint by index *)
      method hint : int -> hint

    end

