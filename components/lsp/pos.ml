(** Type of a position, corresponding to a continuous range of characters in a
    (utf8-encoded) source. *)
type pos =
  { fname      : string option (** File name for the position.       *)
  ; start_line : int (** Line number of the starting point.          *)
  ; start_col  : int (** Column number (utf8) of the starting point. *)
  ; end_line   : int (** Line number of the ending point.            *)
  ; end_col    : int (** Column number (utf8) of the ending point.   *) }

type popt = pos option

let out ppf fmt = Format.ifprintf ppf (fmt ^^ "@.")

let string = fun ppf s -> out ppf "\"%s\"" s


(** [to_string ?print_fname pos] transforms [pos] into a readable string. If
    [print_fname] is [true] (the default), the filename contained in [pos] is
    printed. *)
let to_string : ?print_fname:bool -> pos -> string =
  fun ?(print_fname=true) {fname; start_line; start_col; end_line; end_col} ->
  let fname =
    if not print_fname then "" else
    match fname with
    | None    -> ""
    | Some(n) -> n ^ ":"
  in
  if start_line <> end_line then
    Printf.sprintf "%s%d:%d-%d:%d" fname start_line start_col end_line end_col
  else if start_col = end_col then
    Printf.sprintf "%s%d:%d" fname start_line start_col
  else
    Printf.sprintf "%s%d:%d-%d" fname start_line start_col end_col

(** [pp ppf pos] prints the optional position [pos] on [ppf]. *)
let pp = fun ppf p ->
  match p with
  | None    -> string ppf "unknown location"
  | Some(p) -> string ppf (to_string p)
