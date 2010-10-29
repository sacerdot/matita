(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

exception Drop
(* mo file name, ma file name *)
exception NMacro of GrafiteAst.loc * GrafiteAst.nmacro

type 'a disambiguator_input = string * int * 'a

type options = { 
  do_heavy_checks: bool ; 
}

let basic_eval_unification_hint (t,n) status =
 NCicUnifHint.add_user_provided_hint status t n
;;

let inject_unification_hint =
 let basic_eval_unification_hint (t,n) 
   ~refresh_uri_in_universe 
   ~refresh_uri_in_term
 =
  let t = refresh_uri_in_term t in basic_eval_unification_hint (t,n)
 in
  GrafiteTypes.Serializer.register#run "unification_hints"
   basic_eval_unification_hint
;;

let eval_unification_hint status t n = 
 let metasenv,subst,status,t =
  GrafiteDisambiguate.disambiguate_nterm None status [] [] [] ("",0,t) in
 assert (metasenv=[]);
 let t = NCicUntrusted.apply_subst subst [] t in
 let status = basic_eval_unification_hint (t,n) status in
 let dump = inject_unification_hint (t,n)::status#dump in
 let status = status#set_dump dump in
  status,[]
;;

let basic_index_obj l status =
  status#set_auto_cache 
    (List.fold_left
      (fun t (ks,v) -> 
         List.fold_left (fun t k ->
           NDiscriminationTree.DiscriminationTree.index t k v)
          t ks) 
    status#auto_cache l) 
;;     

let record_index_obj = 
 let aux l 
   ~refresh_uri_in_universe 
   ~refresh_uri_in_term
 =
    basic_index_obj
      (List.map 
        (fun ks,v -> List.map refresh_uri_in_term ks, refresh_uri_in_term v) 
      l)
 in
  GrafiteTypes.Serializer.register#run "index_obj" aux
;;

let compute_keys status uri height kind = 
 let mk_item ty spec =
   let orig_ty = NTacStatus.mk_cic_term [] ty in
   let status,keys = NnAuto.keys_of_type status orig_ty in
   let keys =  
     List.map 
       (fun t -> 
	  snd (NTacStatus.term_of_cic_term status t (NTacStatus.ctx_of t)))
       keys
   in
   keys,NCic.Const(NReference.reference_of_spec uri spec)
 in
 let data = 
  match kind with
  | NCic.Fixpoint (ind,ifl,_) -> 
     HExtlib.list_mapi 
       (fun (_,_,rno,ty,_) i -> 
          if ind then mk_item ty (NReference.Fix (i,rno,height)) 
          else mk_item ty (NReference.CoFix height)) ifl
  | NCic.Inductive (b,lno,itl,_) -> 
     HExtlib.list_mapi 
       (fun (_,_,ty,_) i -> mk_item ty (NReference.Ind (b,i,lno))) itl 
     @
     List.map (fun ((_,_,ty),i,j) -> mk_item ty (NReference.Con (i,j+1,lno)))
       (List.flatten (HExtlib.list_mapi 
         (fun (_,_,_,cl) i -> HExtlib.list_mapi (fun x j-> x,i,j) cl)
         itl))
  | NCic.Constant (_,_,Some _, ty, _) -> 
     [ mk_item ty (NReference.Def height) ]
  | NCic.Constant (_,_,None, ty, _) ->
     [ mk_item ty NReference.Decl ]
 in
  HExtlib.filter_map
   (fun (keys, t) ->
     let keys = List.filter
       (function 
         | (NCic.Meta _) 
         | (NCic.Appl (NCic.Meta _::_)) -> false 
         | _ -> true) 
       keys
     in
     if keys <> [] then 
      begin
        HLog.debug ("Indexing:" ^ 
          NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] t);
        HLog.debug ("With keys:" ^ String.concat "\n" (List.map (fun t ->
          NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] t) keys));
        Some (keys,t) 
      end
     else 
      begin
        HLog.debug ("Not indexing:" ^ 
          NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] t);
        None
      end)
    data
;;

let index_obj_for_auto status (uri, height, _, _, kind) = 
 (*prerr_endline (string_of_int height);*)
  let data = compute_keys status uri height kind in
  let status = basic_index_obj data status in
  let dump = record_index_obj data :: status#dump in   
  status#set_dump dump
;; 

let index_eq uri status =
  let eq_status = status#eq_cache in
  let eq_status1 = NCicParamod.index_obj eq_status uri in
    status#set_eq_cache eq_status1
;;

let record_index_eq =
 let basic_index_eq uri
   ~refresh_uri_in_universe 
   ~refresh_uri_in_term 
   = index_eq (NCicLibrary.refresh_uri uri) 
 in
  GrafiteTypes.Serializer.register#run "index_eq" basic_index_eq
;;

let index_eq_for_auto status uri =
 if NnAuto.is_a_fact_obj status uri then
   let newstatus = index_eq uri status in
     if newstatus#eq_cache == status#eq_cache then status 
     else
       ((*prerr_endline ("recording " ^ (NUri.string_of_uri uri));*)
	let dump = record_index_eq uri :: newstatus#dump 
	in newstatus#set_dump dump)
 else 
   ((*prerr_endline "Not a fact";*)
   status)
;; 

let basic_eval_add_constraint (u1,u2) status =
 NCicLibrary.add_constraint status u1 u2
;;

let inject_constraint =
 let basic_eval_add_constraint (u1,u2) 
       ~refresh_uri_in_universe 
       ~refresh_uri_in_term
 =
  let u1 = refresh_uri_in_universe u1 in 
  let u2 = refresh_uri_in_universe u2 in 
  basic_eval_add_constraint (u1,u2)
 in
  GrafiteTypes.Serializer.register#run "constraints" basic_eval_add_constraint 
;;

let eval_add_constraint status u1 u2 = 
 let status = basic_eval_add_constraint (u1,u2) status in
 let dump = inject_constraint (u1,u2)::status#dump in
 let status = status#set_dump dump in
  status,[]
;;

let eval_ng_tac tac =
 let rec aux f (text, prefix_len, tac) =
  match tac with
  | GrafiteAst.NApply (_loc, t) -> NTactics.apply_tac (text,prefix_len,t) 
  | GrafiteAst.NSmartApply (_loc, t) -> 
      NnAuto.smart_apply_tac (text,prefix_len,t) 
  | GrafiteAst.NAssert (_loc, seqs) ->
     NTactics.assert_tac
      ((List.map
        (function (hyps,concl) ->
          List.map
           (function
              (id,`Decl t) -> id,`Decl (text,prefix_len,t)
             |(id,`Def (b,t))->id,`Def((text,prefix_len,b),(text,prefix_len,t))
           ) hyps,
          (text,prefix_len,concl))
       ) seqs)
  | GrafiteAst.NAuto (_loc, (None,a)) -> 
      NnAuto.auto_tac ~params:(None,a) ?trace_ref:None
  | GrafiteAst.NAuto (_loc, (Some l,a)) ->
      NnAuto.auto_tac
	~params:(Some List.map (fun x -> "",0,x) l,a) ?trace_ref:None
  | GrafiteAst.NBranch _ -> NTactics.branch_tac ~force:false
  | GrafiteAst.NCases (_loc, what, where) ->
      NTactics.cases_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NCase1 (_loc,n) -> NTactics.case1_tac n
  | GrafiteAst.NChange (_loc, pat, ww) -> 
      NTactics.change_tac 
       ~where:(text,prefix_len,pat) ~with_what:(text,prefix_len,ww) 
  | GrafiteAst.NConstructor (_loc,num,args) -> 
     NTactics.constructor_tac 
       ?num ~args:(List.map (fun x -> text,prefix_len,x) args)
  | GrafiteAst.NCut (_loc, t) -> NTactics.cut_tac (text,prefix_len,t) 
(*| GrafiteAst.NDiscriminate (_,what) -> NDestructTac.discriminate_tac ~what:(text,prefix_len,what)
  | GrafiteAst.NSubst (_,what) -> NDestructTac.subst_tac ~what:(text,prefix_len,what)*)
  | GrafiteAst.NDestruct (_,dom,skip) -> NDestructTac.destruct_tac dom skip
  | GrafiteAst.NDot _ -> NTactics.dot_tac 
  | GrafiteAst.NElim (_loc, what, where) ->
      NTactics.elim_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NFocus (_,l) -> NTactics.focus_tac l
  | GrafiteAst.NGeneralize (_loc, where) -> 
      NTactics.generalize_tac ~where:(text,prefix_len,where)
  | GrafiteAst.NId _ -> (fun x -> x)
  | GrafiteAst.NIntro (_loc,n) -> NTactics.intro_tac n
  | GrafiteAst.NIntros (_loc,ns) -> NTactics.intros_tac ns
  | GrafiteAst.NInversion (_loc, what, where) ->
      NTactics.inversion_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NLApply (_loc, t) -> NTactics.lapply_tac (text,prefix_len,t) 
  | GrafiteAst.NLetIn (_loc,where,what,name) ->
      NTactics.letin_tac ~where:(text,prefix_len,where) 
        ~what:(text,prefix_len,what) name
  | GrafiteAst.NMerge _ -> NTactics.merge_tac 
  | GrafiteAst.NPos (_,l) -> NTactics.pos_tac l
  | GrafiteAst.NPosbyname (_,s) -> NTactics.case_tac s
  | GrafiteAst.NReduce (_loc, reduction, where) ->
      NTactics.reduce_tac ~reduction ~where:(text,prefix_len,where)
  | GrafiteAst.NRewrite (_loc,dir,what,where) ->
     NTactics.rewrite_tac ~dir ~what:(text,prefix_len,what)
      ~where:(text,prefix_len,where)
  | GrafiteAst.NSemicolon _ -> fun x -> x
  | GrafiteAst.NShift _ -> NTactics.shift_tac 
  | GrafiteAst.NSkip _ -> NTactics.skip_tac
  | GrafiteAst.NUnfocus _ -> NTactics.unfocus_tac
  | GrafiteAst.NWildcard _ -> NTactics.wildcard_tac 
  | GrafiteAst.NTry (_,tac) -> NTactics.try_tac
      (aux f (text, prefix_len, tac))
  | GrafiteAst.NAssumption _ -> NTactics.assumption_tac
  | GrafiteAst.NBlock (_,l) -> 
      NTactics.block_tac (List.map (fun x -> aux f (text,prefix_len,x)) l)
  |GrafiteAst.NRepeat (_,tac) ->
      NTactics.repeat_tac (f f (text, prefix_len, tac))
 in
  aux aux tac (* trick for non uniform recursion call *)
;;
      
let subst_metasenv_and_fix_names status =
  let u,h,metasenv, subst,o = status#obj in
  let o = 
    NCicUntrusted.map_obj_kind ~skip_body:true 
     (NCicUntrusted.apply_subst subst []) o
  in
   status#set_obj(u,h,NCicUntrusted.apply_subst_metasenv subst metasenv,subst,o)
;;


let rec eval_ncommand opts status (text,prefix_len,cmd) =
  match cmd with
  | GrafiteAst.UnificationHint (loc, t, n) -> eval_unification_hint status t n
  | GrafiteAst.NCoercion (loc, name, t, ty, source, target) ->
      NCicCoercDeclaration.eval_ncoercion status name t ty source target
  | GrafiteAst.NQed loc ->
     if status#ng_mode <> `ProofMode then
      raise (GrafiteTypes.Command_error "Not in proof mode")
     else
      let uri,height,menv,subst,obj_kind = status#obj in
       if menv <> [] then
        raise
         (GrafiteTypes.Command_error"You can't Qed an incomplete theorem")
       else
        let obj_kind =
         NCicUntrusted.map_obj_kind 
          (NCicUntrusted.apply_subst subst []) obj_kind in
        let height = NCicTypeChecker.height_of_obj_kind uri [] obj_kind in
        (* fix the height inside the object *)
        let rec fix () = function 
          | NCic.Const (NReference.Ref (u,spec)) when NUri.eq u uri -> 
             NCic.Const (NReference.reference_of_spec u
              (match spec with
              | NReference.Def _ -> NReference.Def height
              | NReference.Fix (i,j,_) -> NReference.Fix(i,j,height)
              | NReference.CoFix _ -> NReference.CoFix height
              | NReference.Ind _ | NReference.Con _
              | NReference.Decl as s -> s))
          | t -> NCicUtils.map (fun _ () -> ()) () fix t
        in
        let obj_kind = 
          match obj_kind with
          | NCic.Fixpoint _ -> 
              NCicUntrusted.map_obj_kind (fix ()) obj_kind 
          | _ -> obj_kind
        in
        let obj = uri,height,[],[],obj_kind in
        let old_status = status in
        let status = NCicLibrary.add_obj status obj in
        let index_obj =
         match obj_kind with
            NCic.Constant (_,_,_,_,(_,`Example,_))
          | NCic.Fixpoint (_,_,(_,`Example,_)) -> false
          | _ -> true
        in
        let status =
         if index_obj then
          let status = index_obj_for_auto status obj in
           (try index_eq_for_auto status uri
           with _ -> status)
         else
          status in
(*
	  try 
	    index_eq uri status
	  with _ -> prerr_endline "got an exception"; status
	in *)
(*         prerr_endline (NCicPp.ppobj obj); *)
        HLog.message ("New object: " ^ NUri.string_of_uri uri);
         (try
       (*prerr_endline (NCicPp.ppobj obj);*)
           let boxml = NCicElim.mk_elims obj in
           let boxml = boxml @ NCicElim.mk_projections obj in
(*
           let objs = [] in
           let timestamp,uris_rev =
             List.fold_left
              (fun (status,uris_rev) (uri,_,_,_,_) as obj ->
                let status = NCicLibrary.add_obj status obj in
                 status,uri::uris_rev
              ) (status,[]) objs in
           let uris = uri::List.rev uris_rev in
*)
           let status = status#set_ng_mode `CommandMode in
           let status = LexiconSync.add_aliases_for_objs status [uri] in
           let status,uris =
            List.fold_left
             (fun (status,uris) boxml ->
               try
                let nstatus,nuris =
                 eval_ncommand opts status
                  ("",0,GrafiteAst.NObj (HExtlib.dummy_floc,boxml))
                in
                if nstatus#ng_mode <> `CommandMode then
                  begin
                    (*HLog.warn "error in generating projection/eliminator";*)
                    assert(status#ng_mode = `CommandMode);
                    status, uris
                  end
                else
                  nstatus, uris@nuris
               with
               | MultiPassDisambiguator.DisambiguationError _
               | NCicTypeChecker.TypeCheckerFailure _ ->
                  (*HLog.warn "error in generating projection/eliminator";*)
                  status,uris
             ) (status,[] (* uris *)) boxml in             
           let _,_,_,_,nobj = obj in 
           let status = match nobj with
               NCic.Inductive (is_ind,leftno,[it],_) ->
                 let _,ind_name,ty,cl = it in
                 List.fold_left 
                   (fun status outsort ->
                      let status = status#set_ng_mode `ProofMode in
                      try
                       (let status,invobj =
                         NInversion.mk_inverter 
                          (ind_name ^ "_inv_" ^
                            (snd (NCicElim.ast_of_sort outsort)))
                          is_ind it leftno outsort status status#baseuri in
                       let _,_,menv,_,_ = invobj in
                       fst (match menv with
                             [] -> eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
                           | _ -> status,[]))
                       (* XXX *)
                      with _ -> (*HLog.warn "error in generating inversion principle"; *)
                                let status = status#set_ng_mode `CommandMode in status)
                  status
                  (NCic.Prop::
                    List.map (fun s -> NCic.Type s) (NCicEnvironment.get_universes ()))
              | _ -> status
           in
           let coercions =
            match obj with
              _,_,_,_,NCic.Inductive
               (true,leftno,[_,_,_,[_,_,_]],(_,`Record fields))
               ->
                HExtlib.filter_map
                 (fun (name,is_coercion,arity) ->
                   if is_coercion then Some(name,leftno,arity) else None) fields
            | _ -> [] in
           let status,uris =
            List.fold_left
             (fun (status,uris) (name,cpos,arity) ->
               try
                 let metasenv,subst,status,t =
                  GrafiteDisambiguate.disambiguate_nterm None status [] [] []
                   ("",0,NotationPt.Ident (name,None)) in
                 assert (metasenv = [] && subst = []);
                 let status, nuris = 
                   NCicCoercDeclaration.
                     basic_eval_and_record_ncoercion_from_t_cpos_arity 
                      status (name,t,cpos,arity)
                 in
                 let uris = nuris@uris in
                 status, uris
               with MultiPassDisambiguator.DisambiguationError _-> 
                 HLog.warn ("error in generating coercion: "^name);
                 status, uris) 
             (status,uris) coercions
           in
            status,uris
          with
           exn ->
            NCicLibrary.time_travel old_status;
            raise exn)
  | GrafiteAst.NCopy (log,tgt,src_uri, map) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
       let tgt_uri_ext, old_ok = 
         match NCicEnvironment.get_checked_obj src_uri with
         | _,_,[],[], (NCic.Inductive _ as ok) -> ".ind", ok
         | _,_,[],[], (NCic.Fixpoint _ as ok) -> ".con", ok
         | _,_,[],[], (NCic.Constant _ as ok) -> ".con", ok
         | _ -> assert false
       in
       let tgt_uri = NUri.uri_of_string (status#baseuri^"/"^tgt^tgt_uri_ext) in
       let map = (src_uri, tgt_uri) :: map in
       let ok = 
         let rec subst () = function
           | NCic.Meta _ -> assert false
           | NCic.Const (NReference.Ref (u,spec)) as t ->
               (try NCic.Const 
                 (NReference.reference_of_spec (List.assoc u map)spec)
               with Not_found -> t)
           | t -> NCicUtils.map (fun _ _ -> ()) () subst t
         in
         NCicUntrusted.map_obj_kind ~skip_body:false (subst ()) old_ok
       in
       let ninitial_stack = Continuationals.Stack.of_nmetasenv [] in
       let status = status#set_obj (tgt_uri,0,[],[],ok) in
       (*prerr_endline (NCicPp.ppobj (tgt_uri,0,[],[],ok));*)
       let status = status#set_stack ninitial_stack in
       let status = subst_metasenv_and_fix_names status in
       let status = status#set_ng_mode `ProofMode in
       eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
  | GrafiteAst.NObj (loc,obj) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
      let status,obj =
       GrafiteDisambiguate.disambiguate_nobj status
        ~baseuri:status#baseuri (text,prefix_len,obj) in
      let uri,height,nmenv,nsubst,nobj = obj in
      let ninitial_stack = Continuationals.Stack.of_nmetasenv nmenv in
      let status = status#set_obj obj in
      let status = status#set_stack ninitial_stack in
      let status = subst_metasenv_and_fix_names status in
      let status = status#set_ng_mode `ProofMode in
      (match nmenv with
          [] ->
           eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
        | _ -> status,[])
  | GrafiteAst.NDiscriminator (_,_) -> assert false (*(loc, indty) ->
      if status#ng_mode <> `CommandMode then
        raise (GrafiteTypes.Command_error "Not in command mode")
      else
        let status = status#set_ng_mode `ProofMode in
        let metasenv,subst,status,indty =
          GrafiteDisambiguate.disambiguate_nterm None status [] [] [] (text,prefix_len,indty) in
        let indtyno, (_,_,tys,_,_) = match indty with
            NCic.Const ((NReference.Ref (_,NReference.Ind (_,indtyno,_))) as r) ->
              indtyno, NCicEnvironment.get_checked_indtys r
          | _ -> prerr_endline ("engine: indty expected... (fix this error message)"); assert false in
        let it = List.nth tys indtyno in
        let status,obj =  NDestructTac.mk_discriminator it status in
        let _,_,menv,_,_ = obj in
          (match menv with
               [] -> eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
             | _ -> prerr_endline ("Discriminator: non empty metasenv");
                    status, []) *)
  | GrafiteAst.NInverter (loc, name, indty, selection, sort) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
      let metasenv,subst,status,sort = match sort with
        | None -> [],[],status,NCic.Sort NCic.Prop
        | Some s -> GrafiteDisambiguate.disambiguate_nterm None status [] [] []
                      (text,prefix_len,s) 
      in
      assert (metasenv = []);
      let sort = NCicReduction.whd ~subst [] sort in
      let sort = match sort with 
          NCic.Sort s -> s
        | _ ->  raise (Invalid_argument (Printf.sprintf "ninverter: found target %s, which is not a sort" 
                                           (NCicPp.ppterm ~metasenv ~subst ~context:[] sort)))
      in
      let status = status#set_ng_mode `ProofMode in
      let metasenv,subst,status,indty =
       GrafiteDisambiguate.disambiguate_nterm None status [] [] subst (text,prefix_len,indty) in
      let indtyno,(_,leftno,tys,_,_) = match indty with
          NCic.Const ((NReference.Ref (_,NReference.Ind (_,indtyno,_))) as r) -> 
            indtyno, NCicEnvironment.get_checked_indtys r
        | _ -> prerr_endline ("engine: indty ="  ^ NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] indty) ; assert false in
      let it = List.nth tys indtyno in
     let status,obj = NInversion.mk_inverter name true it leftno ?selection sort 
                        status status#baseuri in
     let _,_,menv,_,_ = obj in
     (match menv with
        [] ->
          eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
      | _ -> assert false)
  | GrafiteAst.NUnivConstraint (loc,u1,u2) ->
      eval_add_constraint status [`Type,u1] [`Type,u2]
;;

let eval_comment ~disambiguate_command opts status (text,prefix_len,c) =
 status, []

let rec eval_command ~disambiguate_command opts status (text,prefix_len,cmd) =
 let status,cmd = disambiguate_command status (text,prefix_len,cmd) in
 let status,uris =
  match cmd with
  | GrafiteAst.Include (loc, baseuri) ->
     let status,obj =
       GrafiteTypes.Serializer.require ~baseuri:(NUri.uri_of_string baseuri)
        status in
     let status = status#set_dump (obj::status#dump) in
       status,[]
  | GrafiteAst.Print (_,_) -> status,[]
  | GrafiteAst.Set (loc, name, value) -> status, []
 in
  status,uris

and eval_executable ~disambiguate_command opts status (text,prefix_len,ex) =
  match ex with
  | GrafiteAst.NTactic (_(*loc*), tacl) ->
      if status#ng_mode <> `ProofMode then
       raise (GrafiteTypes.Command_error "Not in proof mode")
      else
       let status =
        List.fold_left 
          (fun status tac ->
            let status = eval_ng_tac (text,prefix_len,tac) status in
            subst_metasenv_and_fix_names status)
          status tacl
       in
        status,[]
  | GrafiteAst.Command (_, cmd) ->
      eval_command ~disambiguate_command opts status (text,prefix_len,cmd)
  | GrafiteAst.NCommand (_, cmd) ->
      eval_ncommand opts status (text,prefix_len,cmd)
  | GrafiteAst.NMacro (loc, macro) ->
     raise (NMacro (loc,macro))

and eval_ast ~disambiguate_command ?(do_heavy_checks=false) status
(text,prefix_len,st)
=
  let opts = { do_heavy_checks = do_heavy_checks ; } in
  match st with
  | GrafiteAst.Executable (_,ex) ->
     eval_executable ~disambiguate_command opts status (text,prefix_len,ex)
  | GrafiteAst.Comment (_,c) -> 
      eval_comment ~disambiguate_command opts status (text,prefix_len,c) 
;;
