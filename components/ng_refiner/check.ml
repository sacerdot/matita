(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id$ *)

let debug = true
let ignore_exc = false
let rank_all_dependencies = false
let trust_environment = false
let print_object = false

let indent = ref 0;;

let load_graph, get_graph =
 let oldg = ref CicUniv.empty_ugraph in
  (function uri -> 
    let _,g = CicEnvironment.get_obj !oldg uri in
     oldg := g),
  (function _ -> !oldg)
;;

let logger =
    let do_indent () = String.make !indent ' ' in  
    (function 
      | `Start_type_checking s ->
          if debug then
           prerr_endline (do_indent () ^ "Start: " ^ NUri.string_of_uri s); 
          incr indent
      | `Type_checking_completed s ->
          decr indent;
          if debug then
           prerr_endline (do_indent () ^ "End: " ^ NUri.string_of_uri s)
      | `Type_checking_interrupted s ->
          decr indent;
          if debug then
           prerr_endline (do_indent () ^ "Break: " ^ NUri.string_of_uri s)
      | `Type_checking_failed s ->
          decr indent;
          if debug then
           prerr_endline (do_indent () ^ "Fail: " ^ NUri.string_of_uri s)
      | `Trust_obj s ->
          if debug then
           prerr_endline (do_indent () ^ "Trust: " ^ NUri.string_of_uri s))
;;

let mk_type n = 
  if n = 0 then
     [`Type, NUri.uri_of_string ("cic:/matita/pts/Type.univ")]
  else
     [`Type, NUri.uri_of_string ("cic:/matita/pts/Type"^string_of_int n^".univ")]
;;
let mk_cprop n = 
  if n = 0 then 
    [`CProp, NUri.uri_of_string ("cic:/matita/pts/Type.univ")]
  else
    [`CProp, NUri.uri_of_string ("cic:/matita/pts/Type"^string_of_int n^".univ")]
;;


let _ =
  Sys.catch_break true;
  let do_old_logging = ref true in
  HelmLogger.register_log_callback
   (fun ?append_NL html_msg ->
     if !do_old_logging then
      prerr_endline (HelmLogger.string_of_html_msg html_msg));
  CicParser.impredicative_set := false;
  NCicTypeChecker.set_logger logger;
  Helm_registry.load_from "conf.xml";
  let alluris = 
    try
      let s = Sys.argv.(1) in
      if s = "-alluris" then
       begin
        let uri_re = Str.regexp ".*\\(ind\\|con\\)$" in
        let uris = Http_getter.getalluris () in
        let alluris = List.filter (fun u -> Str.string_match uri_re u 0) uris in
        let oc = open_out "alluris.txt" in
        List.iter (fun s -> output_string oc (s^"\n")) alluris;
        close_out oc; 
        []
       end
      else [s]
    with Invalid_argument _ -> 
      let r = ref [] in
      let ic = open_in "alluris.txt" in
      try while true do r := input_line ic :: !r; done; []
      with _ -> List.rev !r
  in
  let alluris = 
    HExtlib.filter_map
      (fun u -> try Some (UriManager.uri_of_string u) with _ -> None) alluris 
  in
  (* brutal *)
  prerr_endline "computing graphs to load...";
  let roots_alluris = 
   if not rank_all_dependencies then
    alluris
   else (
    let dbd = HSql.quick_connect (LibraryDb.parse_dbd_conf ()) in
     MetadataTypes.ownerize_tables (Helm_registry.get "matita.owner");
    let uniq l = 
     HExtlib.list_uniq (List.sort UriManager.compare l) in
    let who_uses u = 
     uniq (List.map (fun (uri,_) -> UriManager.strip_xpointer uri)
      (MetadataDeps.inverse_deps ~dbd u)) in
    let rec fix acc l = 
     let acc, todo = 
      List.fold_left (fun (acc,todo) x ->
        let w = who_uses x in
        if w = [] then (x::acc,todo) else (acc,uniq (todo@w)))
      (acc,[]) l
     in
     if todo = [] then uniq acc else fix acc todo
    in
     fix [] alluris)
  in
  prerr_endline "generating Coq graphs...";
  CicEnvironment.set_trust (fun _ -> trust_environment);
  List.iter
   (fun u ->
     prerr_endline (" - " ^ UriManager.string_of_uri u);
     try
       ignore(CicTypeChecker.typecheck u);
     with 
     | CicTypeChecker.AssertFailure s
     | CicTypeChecker.TypeCheckerFailure s ->
        prerr_endline (Lazy.force s);
        assert false
    ) roots_alluris;
  prerr_endline "loading...";
  List.iter 
    (fun u -> 
       prerr_endline ("  - "^UriManager.string_of_uri u);
       try load_graph u with exn -> ())
    roots_alluris;
  prerr_endline "finished....";
  let lll, uuu =(CicUniv.do_rank (get_graph ())) in
  let lll = List.sort compare lll in
  List.iter (fun k -> 
    prerr_endline (CicUniv.string_of_universe k ^ " = " ^ string_of_int (CicUniv.get_rank k))) uuu;
  let _ = 
    try
    let rec aux = function
      | a::(b::_ as tl) ->
         NCicEnvironment.add_lt_constraint (mk_type a) (mk_type b);
         NCicEnvironment.add_lt_constraint (mk_cprop a) (mk_cprop b);
         aux tl
      | _ -> ()
    in
       aux lll
    with NCicEnvironment.BadConstraint s as e ->
      prerr_endline (Lazy.force s); raise e
  in
  prerr_endline "ranked....";
  prerr_endline (NCicEnvironment.pp_constraints ());
(*
  let [_,type0_uri] = mk_type 0 in
  let [_,type1_uri] = mk_type 1 in
  let [_,type2_uri] = mk_type 2 in
  prerr_endline 
   ("Min:" ^ 
   (match NCicEnvironment.sup [true,type0_uri;true,type2_uri] with
       | None -> "NO SUP"
       | Some t -> NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] 
          (NCic.Sort (NCic.Type t))));
*)
  HExtlib.profiling_enabled := false;
  List.iter (fun uu ->
    let uu= OCic2NCic.nuri_of_ouri uu in
    indent := 0;
    let o = NCicLibrary.get_obj uu in
    if print_object then prerr_endline (NCicPp.ppobj o); 
    try 
      NCicEnvironment.check_and_add_obj o
    with 
    | NCicTypeChecker.AssertFailure s 
    | NCicTypeChecker.TypeCheckerFailure s
    | NCicEnvironment.ObjectNotFound s
    | NCicEnvironment.BadConstraint s
    | NCicEnvironment.BadDependency (s,_) as e -> 
       prerr_endline ("######### " ^ Lazy.force s);
       if not ignore_exc then raise e
    )
    alluris;
  NCicEnvironment.invalidate ();
  Gc.compact ();
  HExtlib.profiling_enabled := true;
  NCicTypeChecker.set_logger (fun _ -> ());
  do_old_logging := false;
  prerr_endline "typechecking, first with the new and then with the old kernel";
  List.iter 
    (fun u ->
      let u = OCic2NCic.nuri_of_ouri u in
      indent := 0;
      match NCicLibrary.get_obj u with
      | _,_,_,_,NCic.Constant (_,_,Some bo, ty, _) ->
          let rec intros = function
            | NCic.Prod (name, s, t) ->
                let ctx, t = intros t in
                ctx @ [(name, (NCic.Decl s))] , t
            | t -> [], t
          in
          let rec perforate ctx metasenv = function
            | NCic.Appl (NCic.Const (NReference.Ref (u,_))::ty::_)
              when NUri.string_of_uri u = "cic:/matita/tests/hole.con" ->
                let metasenv, ty =  perforate ctx metasenv ty in
                let a,_,b,_ = 
                  NCicMetaSubst.mk_meta metasenv ctx (`WithType ty) in a,b
            | t -> 
                NCicUntrusted.map_term_fold_a
                 (fun e ctx -> e::ctx) ctx perforate metasenv t
          in
          let rec curryfy ctx = function
            | NCic.Lambda (name, (NCic.Sort _ as s), tgt) ->
                NCic.Lambda (name, s, curryfy ((name,NCic.Decl s) :: ctx) tgt)
            | NCic.Lambda (name, s, tgt) ->
                let tgt = curryfy ((name,NCic.Decl s) :: ctx) tgt in
                NCic.Lambda (name, NCic.Implicit `Type, tgt)
            | t -> 
                NCicUtils.map
                 (fun e ctx -> e::ctx) ctx curryfy t
          in
(*
          let ctx, pty = intros ty in
          let metasenv, pty = perforate ctx [] pty in
*)
(*
          let sty, metasenv, _ = 
            NCicMetaSubst.saturate ~delta:max_int [] ctx ty 0
          in
*)
(*           let ctx, ty = intros ty in *)
(*
          let left, right = 
            match  NCicReduction.whd ~delta:max_int ctx pty with
            | NCic.Appl [eq;t;a;b] -> a, b
            | _-> assert false
          in
*)             

(*
          let whd ty =
            match ty with
            | NCic.Appl [eq;t;a;b] ->
               NCic.Appl [eq;t;NCicReduction.whd ~delta:0 ctx a;b]
            | t -> NCicReduction.whd ~delta:0 ctx t
          in
*)
(*
                prerr_endline 
                 (Printf.sprintf "%s == %s"
                 (NCicPp.ppterm ~metasenv:metasenv ~subst:[] ~context:ctx ity)
                 (NCicPp.ppterm ~metasenv:metasenv ~subst:[] ~context:ctx sty));
*)
          prerr_endline ("start: " ^ NUri.string_of_uri u);
          let bo = curryfy [] bo in
          (try 
            let rdb = new NRstatus.status in
            let metasenv, subst, bo, infty = 
              NCicRefiner.typeof rdb [] [] [] bo None
            in
            let metasenv, subst = 
              try 
                NCicUnification.unify rdb metasenv subst [] infty ty
              with
              | NCicUnification.Uncertain msg 
              | NCicUnification.UnificationFailure msg 
              | NCicMetaSubst.MetaSubstFailure msg ->
                  prerr_endline (Lazy.force msg); 
                  metasenv, subst
              | Sys.Break -> metasenv, subst
            in
            if (NCicReduction.are_convertible ~metasenv ~subst [] infty ty)
            then
              prerr_endline ("OK: " ^ NUri.string_of_uri u)
            else
              (
            let ctx = [] in
            let right = infty in
            let left = ty in
                      
                      prerr_endline ("FAIL: " ^ NUri.string_of_uri u);
                  prerr_endline 
                   (Printf.sprintf 
                     ("\t\tRESULT OF UNIF\n\nsubst:\n%s\nmetasenv:\n%s\n" ^^ 
                     "context:\n%s\nTERMS NO SUBST:\n%s\n==\n%s\n"^^
                     "TERMS:\n%s\n==\n%s\n")
                   (NCicPp.ppsubst ~metasenv subst)
                   (NCicPp.ppmetasenv ~subst metasenv)
                   (NCicPp.ppcontext ~metasenv ~subst ctx)
                   (NCicPp.ppterm ~metasenv ~subst:[] ~context:ctx left)
                   (NCicPp.ppterm ~metasenv ~subst:[] ~context:ctx right)
                   (NCicPp.ppterm ~metasenv ~subst ~context:ctx left)
                   (NCicPp.ppterm ~metasenv ~subst ~context:ctx right) ))
            (*let inferred_ty = 
              NCicTypeChecker.typeof ~subst:[] ~metasenv:[] [] bo
            in*)
          with
          | Sys.Break -> ()
          | NCicRefiner.RefineFailure msg 
          | NCicRefiner.Uncertain msg ->
             let _, msg = Lazy.force msg in
             prerr_endline msg;
             prerr_endline ("FAIL: " ^ NUri.string_of_uri u)
          | e -> 
             prerr_endline (Printexc.to_string e); 
             prerr_endline ("FAIL: " ^ NUri.string_of_uri u)
             )
      | _ -> ())
    alluris;
;;
