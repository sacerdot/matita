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

exception LibraryOutOfSync of string Lazy.t

let magic = 2;;

let refresh_uri uri = NUri.uri_of_string (NUri.string_of_uri uri);;

let refresh_uri_in_universe =
 List.map (fun (x,u) -> x, refresh_uri u)
;;

let rec refresh_uri_in_term =
 function
  | NCic.Meta (i,(n,NCic.Ctx l)) ->
     NCic.Meta (i,(n,NCic.Ctx (List.map refresh_uri_in_term l)))
  | NCic.Meta _ as t -> t
  | NCic.Const (NReference.Ref (u,spec)) ->
     NCic.Const (NReference.reference_of_spec (refresh_uri u) spec)
  | NCic.Sort (NCic.Type l) -> NCic.Sort (NCic.Type (refresh_uri_in_universe l))
  | NCic.Match (NReference.Ref (uri,spec),outtype,term,pl) ->
     let r = NReference.reference_of_spec (refresh_uri uri) spec in
     let outtype = refresh_uri_in_term outtype in
     let term = refresh_uri_in_term term in
     let pl = List.map refresh_uri_in_term pl in
      NCic.Match (r,outtype,term,pl)
  | t -> NCicUtils.map (fun _ _ -> ()) () (fun _ -> refresh_uri_in_term) t
;;

let refresh_uri_in_obj (uri,height,metasenv,subst,obj_kind) =
 assert (metasenv = []);
 assert (subst = []);
 refresh_uri uri,height,metasenv,subst,
  NCicUntrusted.map_obj_kind refresh_uri_in_term obj_kind
;;

let path_of_baseuri ?(no_suffix=false) baseuri =
 let uri = NUri.string_of_uri baseuri in
 let path = String.sub uri 4 (String.length uri - 4) in
 let path = Helm_registry.get "matita.basedir" ^ path in
 let dirname = Filename.dirname path in
  HExtlib.mkdir dirname;
  if no_suffix then
   path
  else
   path ^ ".ng"
;;

let require_path path =
 let ch = open_in path in
 let mmagic,dump = Marshal.from_channel ch in
  close_in ch;
  if mmagic <> magic then
   raise (LibraryOutOfSync (lazy "The library is out of sync with the implementation. Please recompile the library."))
  else
   dump
;;

let require0 ~baseuri = require_path (path_of_baseuri baseuri);;

let db_path () = Helm_registry.get "matita.basedir" ^ "/ng_db.ng";;


type timestamp =
 [ `Obj of NUri.uri * NCic.obj 
 | `Constr of NCic.universe * NCic.universe] list *
 (NUri.uri * string * NReference.reference) list *
 NCic.obj NUri.UriMap.t *
 NUri.uri list
;;

let time0 = [],[],NUri.UriMap.empty,[];;
let storage = ref [];;
let local_aliases = ref [];;
let cache = ref NUri.UriMap.empty;;
let includes = ref [];;

let load_db,set_global_aliases,get_global_aliases,add_deps,get_deps,remove_deps=
 let global_aliases = ref [] in
 let rev_includes_map = ref NUri.UriMap.empty in
 let store_db () =
  let ch = open_out (db_path ()) in
  Marshal.to_channel ch (magic,(!global_aliases,!rev_includes_map)) [];
  close_out ch in
 let load_db () =
  HExtlib.mkdir (Helm_registry.get "matita.basedir");
  try
   let ga,im = require_path (db_path ()) in
   let ga =
    List.map
     (fun (uri,name,NReference.Ref (uri2,spec)) ->
       refresh_uri uri,name,NReference.reference_of_spec (refresh_uri uri2) spec
     ) ga in
   let im =
    NUri.UriMap.fold
     (fun u l im -> NUri.UriMap.add (refresh_uri u) (List.map refresh_uri l) im
     ) im NUri.UriMap.empty
   in
    global_aliases := ga;
    rev_includes_map := im
  with
   Sys_error _ -> () in
 let get_deps u =
  let get_deps_one_step u =
    try NUri.UriMap.find u !rev_includes_map with Not_found -> [] in
  let rec aux res =
   function
      [] -> res
    | he::tl ->
       if List.mem he res then
        aux res tl
       else
        aux (he::res) (get_deps_one_step he @ tl)
  in
   aux [] [u] in
 let remove_deps u =
  rev_includes_map := NUri.UriMap.remove u !rev_includes_map;
  rev_includes_map :=
   NUri.UriMap.map
    (fun l -> List.filter (fun uri -> not (NUri.eq u uri)) l) !rev_includes_map;
  store_db ()
 in
  load_db,
  (fun ga -> global_aliases := ga; store_db ()),
  (fun () -> !global_aliases),
  (fun u l ->
    rev_includes_map := NUri.UriMap.add u (l @ get_deps u) !rev_includes_map;
    store_db ()),
  get_deps,
  remove_deps
;;

let init = load_db;;

type automation_cache = NDiscriminationTree.DiscriminationTree.t
type unit_eq_cache = NCicParamod.state

class type g_eq_status =
 object
   method eq_cache : unit_eq_cache 
 end

class eq_status =
 object(self)
  val eq_cache = NCicParamod.empty_state
  method eq_cache = eq_cache
  method set_eq_cache v = {< eq_cache = v >}
  method set_eq_status
   : 'status. #g_eq_status as 'status -> 'self
   = fun o -> self#set_eq_cache o#eq_cache
 end

class type g_auto_status =
 object
   method auto_cache : automation_cache
 end

class auto_status =
 object(self)
  val auto_cache = NDiscriminationTree.DiscriminationTree.empty
  method auto_cache = auto_cache
  method set_auto_cache v = {< auto_cache = v >}
  method set_auto_status
   : 'status. #g_auto_status as 'status -> 'self
   = fun o -> self#set_auto_cache o#auto_cache
 end

class type g_status =
 object
  inherit NRstatus.g_status
  method timestamp: timestamp
 end

class status =
 object(self)
  inherit NRstatus.status
  val timestamp = (time0 : timestamp)
  method timestamp = timestamp
  method set_timestamp v = {< timestamp = v >}
  method set_library_status
   : 'status. #g_status as 'status -> 'self
   = fun o -> self#set_timestamp o#timestamp
 end

let time_travel status =
 let sto,ali,cac,inc = status#timestamp in
  let diff_len = List.length !storage - List.length sto in
  let to_be_deleted,_ = HExtlib.split_nth diff_len !storage in
   if List.length to_be_deleted > 0 then
     NCicEnvironment.invalidate_item (HExtlib.list_last to_be_deleted);
   storage := sto; local_aliases := ali; cache := cac; includes := inc
;;

let serialize ~baseuri dump =
 let ch = open_out (path_of_baseuri baseuri) in
 Marshal.to_channel ch (magic,dump) [];
 close_out ch;
 List.iter
  (function 
   | `Obj (uri,obj) ->
       let ch = open_out (path_of_baseuri uri) in
       Marshal.to_channel ch (magic,obj) [];
       close_out ch
   | `Constr _ -> ()
  ) !storage;
 set_global_aliases (!local_aliases @ get_global_aliases ());
 List.iter (fun u -> add_deps u [baseuri]) !includes;
 time_travel (new status)
;;
  
type obj = string * Obj.t


class type g_dumpable_status =
 object
  inherit g_status
  inherit g_auto_status
  inherit g_eq_status
  method dump: obj list
 end

class dumpable_status =
 object(self)
  inherit status
  inherit auto_status
  inherit eq_status
  val dump = ([] : obj list)
  method dump = dump
  method set_dump v = {< dump = v >}
  method set_dumpable_status : 'status. #g_dumpable_status as 'status -> 'self
   = fun o -> 
     (((self#set_dump o#dump)#set_coercion_status o)#set_auto_status o)#set_eq_status o
 end

type 'a register_type =
 < run: 'status.
    'a -> refresh_uri_in_universe:(NCic.universe ->
      NCic.universe) -> refresh_uri_in_term:(NCic.term -> NCic.term) ->
       (#dumpable_status as 'status) -> 'status >

module Serializer =
 struct
  let require1 = ref (object method run : 'status. obj -> (#dumpable_status as 'status) -> 'status  = fun _ -> assert false end (* unknown data*))
  let already_registered = ref []

  let register =
   object
    method run : 'a.  string -> 'a register_type -> ('a -> obj)
    = fun tag require ->
     assert (not (List.mem tag !already_registered));
     already_registered := tag :: !already_registered;
     let old_require1 = !require1 in
     require1 :=
       object
        method run : 'status. obj -> (#dumpable_status as 'status) -> 'status =
         fun ((tag',data) as x) ->
         if tag=tag' then
          require#run (Obj.magic data) ~refresh_uri_in_universe ~refresh_uri_in_term
         else
          old_require1#run x
       end;
     (fun x -> tag,Obj.repr x)
   end

  let serialize = serialize

  let require ~baseuri status =
   includes := baseuri::!includes;
   let dump = require0 ~baseuri in
    List.fold_right !require1#run dump status
end


let decompile ~baseuri =
 let baseuris = get_deps baseuri in
 List.iter (fun baseuri ->
  remove_deps baseuri;
  HExtlib.safe_remove (path_of_baseuri baseuri);
  let basepath = path_of_baseuri ~no_suffix:true baseuri in
  try
   let od = Unix.opendir basepath in
   let rec aux names =
    try
     let name = Unix.readdir od in
      if name <> "." && name <> ".." then aux (name::names) else aux names
    with
     End_of_file -> names in
   let names = List.map (fun name -> basepath ^ "/" ^ name) (aux []) in
    Unix.closedir od;
    List.iter Unix.unlink names;
    HExtlib.rmdir_descend basepath;
    set_global_aliases
     (List.filter
      (fun (_,_,NReference.Ref (nuri,_)) ->
        Filename.dirname (NUri.string_of_uri nuri) <> NUri.string_of_uri baseuri
      ) (get_global_aliases ()))
  with
   Unix.Unix_error _ -> () (* raised by Unix.opendir, we hope :-) *)
 ) baseuris
;;

LibraryClean.set_decompile_cb
 (fun ~baseuri -> decompile ~baseuri:(NUri.uri_of_string baseuri));;

let fetch_obj uri =
 let obj = require0 ~baseuri:uri in
  refresh_uri_in_obj obj
;;

let resolve name =
 try
  HExtlib.filter_map
   (fun (_,name',nref) -> if name'=name then Some nref else None)
   (!local_aliases @ get_global_aliases ())
 with
  Not_found -> raise (NCicEnvironment.ObjectNotFound (lazy name))
;;

let aliases_of uri =
  HExtlib.filter_map
   (fun (uri',_,nref) ->
     if NUri.eq uri' uri then Some nref else None) !local_aliases
;;

let add_obj status ((u,_,_,_,_) as obj) =
 NCicEnvironment.check_and_add_obj obj;
 storage := (`Obj (u,obj))::!storage;
  let _,height,_,_,obj = obj in
  let references =
   match obj with
      NCic.Constant (_,name,None,_,_) ->
       [u,name,NReference.reference_of_spec u NReference.Decl]
    | NCic.Constant (_,name,Some _,_,_) ->
       [u,name,NReference.reference_of_spec u (NReference.Def height)]
    | NCic.Fixpoint (is_ind,fl,_) ->
       HExtlib.list_mapi
        (fun (_,name,recno,_,_) i ->
          if is_ind then
           u,name,NReference.reference_of_spec u(NReference.Fix(i,recno,height))
          else
           u,name,NReference.reference_of_spec u (NReference.CoFix i)) fl
    | NCic.Inductive (inductive,leftno,il,_) ->
       List.flatten
        (HExtlib.list_mapi
         (fun (_,iname,_,cl) i ->
           HExtlib.list_mapi
            (fun (_,cname,_) j->
              u,cname,
               NReference.reference_of_spec u (NReference.Con (i,j+1,leftno))
            ) cl @
           [u,iname,
             NReference.reference_of_spec u
              (NReference.Ind (inductive,i,leftno))]
         ) il)
  in
  local_aliases := references @ !local_aliases;
  status#set_timestamp (!storage,!local_aliases,!cache,!includes)
;;

let add_constraint status u1 u2 = 
  NCicEnvironment.add_lt_constraint u1 u2;
  storage := (`Constr (u1,u2)) :: !storage;
  status#set_timestamp (!storage,!local_aliases,!cache,!includes)
;;

let get_obj u =
 try 
  List.assq u 
   (HExtlib.filter_map 
    (function `Obj (u,o) -> Some (u,o) | _ -> None )
    !storage)
 with Not_found ->
  try fetch_obj u
  with Sys_error _ ->
   try NUri.UriMap.find u !cache
   with Not_found ->
    let ouri = NCic2OCic.ouri_of_nuri u in
    try
      let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph ouri in
      let l = OCic2NCic.convert_obj ouri o in
      List.iter (fun (u,_,_,_,_ as o) -> cache:= NUri.UriMap.add u o !cache) l;
      HExtlib.list_last l
    with CicEnvironment.Object_not_found u -> 
      raise (NCicEnvironment.ObjectNotFound 
               (lazy (NUri.string_of_uri (OCic2NCic.nuri_of_ouri u))))
;;

let clear_cache () = cache := NUri.UriMap.empty;;

NCicEnvironment.set_get_obj get_obj;;
NCicPp.set_get_obj get_obj;;
