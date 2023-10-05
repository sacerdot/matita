module LIO = Lsp_io

type state = GrafiteTypes.status
type goal = int * NCic.conjecture

let get_goals (status : #GrafiteTypes.status) =
 let _,_,metasenv,_,_ = status#obj in
 metasenv

let initial_state : string -> state =
 fun _path ->
  let baseuri = "cic://foo" (*XXX*) in
  new MatitaEngine.status baseuri

module Command =
struct
  type t = GrafiteAst.statement

  let get_pos : t -> Pos.popt = fun _ -> None (*XXX*)
end

  (** raised when one of the script margins (top or bottom) is reached *)
exception Margin

let only_dust_RE = Pcre.regexp "^(\\s|\n|%%[^\n]*\n)*$"

let parse_text : state -> fname:string -> string -> Command.t list * state =
 fun status ~fname text ->
  let include_paths =
    MatitaEngine.read_include_paths ~include_paths:[] fname @
     Helm_registry.get_list Helm_registry.string "matita.includes" in (*XXX inefficient, precompute and store*)
  LIO.log_object "include_paths" (`String (String.concat "##" include_paths)) ;
  if Pcre.pmatch ~rex:only_dust_RE text then raise Margin;
  let strm =
   GrafiteParser.parsable_statement status
    (Sedlexing.Utf8.from_string text) in
  let ast = MatitaEngine.get_ast status include_paths strm in
  [ast], status

let handle_command : state -> Command.t -> [`Ok of state list | `Ko of exn] =
 fun status ast ->
  try
   match ast with
    | GrafiteAst.Executable (_loc, _ex) ->
       let include_paths =
        Helm_registry.get_list Helm_registry.string "matita.includes" in (*XXX only standard lib, inefficient, precompute and store*)
       LIO.log_object "include_paths" (`String (String.concat "##" include_paths)) ;
       let text = "" in (*XXX*)
       let prefix_len = 0 in (*XXX*)
       let status_aliases =
        try
         MatitaEngine.eval_ast ~include_paths
          ~do_heavy_checks:(Helm_registry.get_bool "matita.do_heavy_checks")
          status (text,prefix_len,ast)
        with
         | MatitaTypes.Cancel -> assert false (*XXX*)
         | GrafiteEngine.NMacro (_loc,_macro) -> assert false (*XXX*) in
       LIO.log_object "handle_command" (`String ("## OK " ^ string_of_int (List.length status_aliases))) ;
       `Ok (List.map fst status_aliases)
    | GrafiteAst.Comment _ -> assert false (*XXX*)
  with
   exn -> `Ko exn


let rangemap : Command.t list -> unit = fun _cmds -> ()

exception Parse_error of Pos.pos * string
