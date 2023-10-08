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

  let get_loc : t -> Ploc.t =
   function
    | GrafiteAst.Executable (loc, _)
    | GrafiteAst.Comment  (loc,_) -> loc

  let pos_of_loc : text:string -> Ploc.t -> Pos.pos =
   fun ~text loc ->
    let buf = Sedlexing.Utf8.from_string text in
    LIO.log_object "==> POS_OF_LOC" (`String (string_of_int (Ploc.first_pos loc) ^ ":" ^ string_of_int (Ploc.last_pos loc) ^ "\n##\n" ^ text)) ;
    let rec skip n =
     if n < 0 then ()
     else begin
      Sedlexing.start buf ;
      let s = Sedlexing.next buf in
      assert (s <> None) ;
      let len = Sedlexing.lexeme_length buf in
      LIO.log_object "== skip" (`String (string_of_int n ^ ":" ^ string_of_int (Uchar.to_int (Stdlib.Option.get s)) ^ ":" ^ string_of_int len)) ;
      assert (len > 0) ;
      skip (n - len)
     end in
    skip (Ploc.first_pos loc) ;
    LIO.log_object "<== skip1" (`String "skip1") ;
    Sedlexing.start buf ;
    let posi,_ = Sedlexing.lexing_positions buf in
    skip (Ploc.last_pos loc - Ploc.first_pos loc - 1) ; (*CSC: why -1? unclear*)
    Sedlexing.start buf ;
    let pose,_ = Sedlexing.lexing_positions buf in
    LIO.log_object "<== done" (`String (Printf.sprintf "%d:%d - %d:%d" posi.Lexing.pos_lnum (posi.Lexing.pos_cnum - posi.Lexing.pos_bol) pose.Lexing.pos_lnum (pose.Lexing.pos_cnum - pose.Lexing.pos_bol))) ;
    {Pos.fname = Some (Ploc.file_name loc) ;
     start_line = posi.Lexing.pos_lnum ;
     start_col = posi.Lexing.pos_cnum - posi.Lexing.pos_bol;
     end_line = pose.Lexing.pos_lnum ;
     end_col = pose.Lexing.pos_cnum - pose.Lexing.pos_bol}
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
  let strm = GrafiteParser.parsable_statement status (Sedlexing.Utf8.from_string text) in
  LIO.log_object "YYY PARSED " (`String "##") ;
  try
   let ast = MatitaEngine.get_ast status include_paths strm in
   LIO.log_object "XXX PARSED " (`String "##") ;
   [ast], status
  with
   | HExtlib.Localized _ as exn -> raise exn
   | exn ->
      let strm = GrafiteParser.parsable_statement status (Sedlexing.Utf8.from_string text) in
      let ast = GrafiteParser.parse_statement status strm in
      match ast with
       | GrafiteAst.Executable (loc,_)
       | GrafiteAst.Comment (loc,_) -> raise (HExtlib.Localized(loc,exn))

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
   | HExtlib.Localized _ as exn -> `Ko exn
   | exn -> `Ko (HExtlib.Localized (Command.get_loc ast,exn))


let rangemap : Command.t list -> unit = fun _cmds -> ()

exception Parse_error of Pos.pos * string
