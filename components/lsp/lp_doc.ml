(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant                            *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization arguments                                    *)
(* Copyright 2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(*
open Common
open Lplib
*)

module LSP = Lsp_base
module LIO = Lsp_io

(* Buffer for storing the log messages *)
let lp_logger = Buffer.create 100

(* exception NoPosition of string *)

type doc_node =
  { ast   : Pure.Command.t
  ; pos   : Pos.pos
  ; exec  : bool
  ; goals : (Pure.goal list * Pos.popt) list
  }

(* Private. A doc is a list of nodes for now. The first element in
   the list is assumed to be the tip of the document. The initial
   document is the empty list.
*)
type t = {
  uri : string;
  version: int;
  text : string;
  mutable root  : Pure.state; (* Only mutated after parsing. *)
  mutable final : Pure.state; (* Only mutated after parsing. *)
  nodes : doc_node list;
  (* severity is same as LSP specifications : https://git.io/JiGAB *)
  logs : ((int * string) * Pos.popt) list; (*((severity, message), location)*)
  map : unit (*XXX*)(*Core.Term.qident RangeMap.t;*)
}

(*
let option_default o1 d =
  match o1 with | None -> d | Some x -> x
  *)

let mk_error ~doc pos msg =
  LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None]

let buf_get_and_clear buf =
  let res = Buffer.contents buf in
  Buffer.clear buf; res

  (*
let process_pstep (pstate,diags,logs) tac nb_subproofs =
  let open Pure in
  let tac_loc = Tactic.get_pos tac in
  let hndl_tac_res = handle_tactic pstate tac nb_subproofs in
  let logs = ((3, buf_get_and_clear lp_logger), tac_loc) :: logs in
  match hndl_tac_res with
  | Tac_OK (pstate, qres) ->
    let goals = Some (current_goals pstate) in
    let qres = match qres with None -> "OK" | Some x -> x in
    pstate, (tac_loc, 4, qres, goals) :: diags, logs
  | Tac_Error(loc,msg) ->
    let loc = option_default loc tac_loc in
    pstate, (loc, 1, msg, None) :: diags, ((1, msg), loc) :: logs

let process_proof pstate tacs logs =
  Pure.ProofTree.fold process_pstep (pstate,[],logs) tacs
*)

(*
let get_goals dg_proof =
  let rec get_goals_aux goals dg_proof =
    match dg_proof with
    | [] -> goals
    | (loc,_,_, Some goalsList)::s ->
        let g = (goals @ [goalsList, loc]) in get_goals_aux g s
    | (loc,_,_,None)::s ->
        let goals = (goals @ [[], loc]) in get_goals_aux goals s
  in get_goals_aux [] dg_proof
*)

(* XXX: Imperative problem *)
let process_cmd text _file (nodes,status,dg,logs) ast =
  (*XXXX*)
  (*
    let cmd_loc = None in
    let qres = "OK" in
    let nodes = { ast; exec = true; goals = [] } :: nodes in
    let ok_diag = cmd_loc, 4, qres, None in
    nodes, status, ok_diag :: dg, logs
  *)
  (*/XXX*)
  let open Pure in
  (* let open Timed in *)
  (* XXX: Capture output *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  let cmd_loc = Command.pos_of_loc text (Command.get_loc ast) in
  let hndl_cmd_res = handle_command status ast in
  let logs = ((3, buf_get_and_clear lp_logger), Some cmd_loc) :: logs in
  match hndl_cmd_res with
    `Ok [status] ->
     let qres = "OK" in (*XXX match qres with None -> "OK" | Some x -> x in *)
     let goals = Pure.get_goals status in
     let goals = [goals, Some cmd_loc] in (*XXX ?? Some cmd_loc ?? *)
     LIO.log_object "GOALS" (`Int (List.length goals)) ;
     let nodes = { ast; pos = cmd_loc; exec = true; goals } :: nodes in
     let ok_diag = Some cmd_loc, 4, qres, None in
     `Ok, nodes, status, ok_diag :: dg, logs
  | `Ko exn ->
    let _,msg = MatitaExcPp.to_string exn in
    let nodes = { ast; pos = cmd_loc; exec = false; goals = [] } :: nodes in
    `Ko, nodes, status, (Some cmd_loc, 1, msg, None) :: dg, ((1, msg), Some cmd_loc) :: logs
  | _ -> assert false (*XXX*)
  (*
  | Cmd_OK (st, qres) ->
    let qres = match qres with None -> "OK" | Some x -> x in
    let nodes = { ast; exec = true; goals = [] } :: nodes in
    let ok_diag = cmd_loc, 4, qres, None in
    nodes, st, ok_diag :: dg, logs
  | Cmd_Proof (pst, tlist, thm_loc, qed_loc) ->
    let start_goals = current_goals pst in
    let pst, dg_proof, logs = process_proof pst tlist logs in
    let dg_proof = (thm_loc, 4, "OK", Some start_goals) :: dg_proof in
    let goals = get_goals dg_proof in
    let nodes = { ast; exec = true; goals } :: nodes in
    let st, dg_proof, logs =
      match end_proof pst with
      | Cmd_OK (st, qres)   ->
        let qres = match qres with None -> "OK" | Some x -> x in
        let pg = qed_loc, 4, qres, None in
        st, pg :: dg_proof, logs
      | Cmd_Error(_loc,msg) ->
        let pg = qed_loc, 1, msg, None in
        st, pg :: dg_proof, ((1, msg), qed_loc) :: logs
      | Cmd_Proof _ ->
        Lsp_io.log_error "process_cmd" "closing proof is nested";
        assert false
    in
    nodes, st, dg_proof @ dg, logs

  | Cmd_Error(loc, msg) ->
    let nodes = { ast; exec = false; goals = [] } :: nodes in
    let loc = option_default loc Command.(get_pos ast) in
    nodes, st, (loc, 1, msg, None) :: dg, ((1, msg), loc) :: logs
  *)

let new_doc ~uri ~version ~text =
  let root =
    (* We remove the ["file://"] prefix. *)
    assert(String.is_prefix "file://" uri);
    let path = String.sub uri 7 (String.length uri - 7) in
    Pure.initial_state path
  in
  { uri;
    text;
    version;
    root;
    final = root;
    nodes = [];
    logs = [];
    map = () (*XXX*)(*RangeMap.empty;*)
  }

(*
(* XXX: Save on close. *)
let close_doc _modname = ()

let dummy_loc =
  Lazy.from_val
    Pos.{ fname = None
        ; start_line = 1
        ; start_col = 1
        ; end_line = 2
        ; end_col = 2
        }
*)

let check_text ~doc =
  (*debug: LIO.log_object "CSC check_text" (`String doc.text) ;*)
  Pure.time_travel doc.root ;
  let uri, version = doc.uri, doc.version in
  try
   let status,parse = Pure.mk_parse_text doc.root ~fname:uri doc.text in
   doc.final <- status ;
   let rec aux ((nodes,final,diag,logs,map) as res) =
    (*debug: LIO.log_object "AUX" (`String " ") ;*)
    try
     let (final, cmd) = parse final in
     doc.final <- final;
     (* compute rangemap *)
     let map = Pure.rangemap map cmd in
     let continue, nodes', final, diag', logs' = process_cmd doc.text uri ([],doc.final,[],[]) cmd in
     match continue with
      | `Ok -> aux (nodes'@nodes,final,diag'@diag,logs'@logs,map)
      | `Ko -> nodes',final,diag',logs',map
    with
     | End_of_file -> res in
   let nodes,final,diag,logs,map= aux ([],doc.root,[],[],()) in
   let logs = List.rev logs in
   let doc = { doc with nodes; final; map; logs } in
   doc,
   LSP.mk_diagnostics ~uri ~version @@
   List.fold_left (fun acc (pos,lvl,msg,goal) ->
       match pos with
       | None     -> acc
       | Some pos -> (pos,lvl,msg,goal) :: acc
     ) [] diag
  with
  | Pure.Parse_error(loc, msg) ->
    let logs = [((1, msg), Some loc)] in
    {doc with logs}, mk_error ~doc loc msg
  | HExtlib.Localized (loc, exn) ->
    let aaa = Ploc.string_of_location loc in
    LIO.log_object "BEFORE POS_OF_LOC" (`String ".") ;
    let loc = Pure.Command.pos_of_loc doc.text loc in (*XXX*)
    LIO.log_object "AFTER POS_OF_LOC" (`String ".") ;
    let _,msg = MatitaExcPp.to_string exn in
    LIO.log_object "CSC error localized" (`String (aaa ^ " :: " ^ msg)) ;
    let logs = [((0, msg), Some loc)] in
    {doc with logs}, mk_error ~doc loc msg
  | exn ->
    let loc = (*XXX*)
     { Pos.fname = None ; start_line = 1 ; start_col = 3 ; end_line = 2 ; end_col = 10 } in
    let _,msg = MatitaExcPp.to_string exn in
    LIO.log_object "CSC error NOT localized" (`String msg) ;
    let logs = [((0, msg), Some loc)] in
    {doc with logs}, mk_error ~doc loc msg
