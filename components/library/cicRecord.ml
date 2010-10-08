(* Copyright (C) 2004-2005, HELM Team.
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

let rec_ty uri leftno  = 
  let rec_ty = Cic.MutInd (uri,0,[]) in
  if leftno = 0 then rec_ty else
    Cic.Appl (rec_ty :: (CicUtil.mk_rels leftno 0))

let generate_one_proj uri params paramsno fields t i =
 let mk_lambdas l start = 
  List.fold_right (fun (name,ty) acc -> 
    Cic.Lambda (Cic.Name name,ty,acc)) l start in
 let recty = rec_ty uri paramsno in
 let outtype = Cic.Lambda (Cic.Name "w'", CicSubstitution.lift 1 recty, t) in
   (mk_lambdas params
     (Cic.Lambda (Cic.Name "w", recty,
       Cic.MutCase (uri,0,outtype, Cic.Rel 1, 
        [mk_lambdas fields (Cic.Rel i)]))))

let projections_of uri field_names =
 let buri = UriManager.buri_of_uri uri in
 let obj,ugraph = CicEnvironment.get_cooked_obj CicUniv.oblivion_ugraph uri in
  match obj with
     Cic.InductiveDefinition ([_,_,sort,[_,ty]],params,paramsno,_) ->
      assert (params = []); (* general case not implemented *)
      let leftparams,ty =
       let rec aux =
        function
           0,ty -> [],ty
         | n,Cic.Prod (Cic.Name name,s,t) ->
            let leftparams,ty = aux (n - 1,t) in
             (name,s)::leftparams,ty
         | _,_ -> assert false
       in
        aux (paramsno,ty)
      in
      let fields =
       let rec aux =
        function
           Cic.MutInd _, []
         | Cic.Appl _,   [] -> []
         | Cic.Prod (_,s,t), name::tl -> (name,s)::aux (t,tl)
         | _,_ -> assert false
       in
        aux ((CicSubstitution.lift 1 ty),field_names)
      in
       let rec aux i =
        function
           Cic.MutInd _, []
         | Cic.Appl _,   [] -> []
         | Cic.Prod (_,s,t), name::tl ->
            let p = generate_one_proj uri leftparams paramsno fields s i in
            let puri = UriManager.uri_of_string (buri ^ "/" ^ name ^ ".con") in
             (puri,name,p) ::
               aux (i - 1)
                (CicSubstitution.subst
                  (Cic.Appl
                    (Cic.Const (puri,[]) ::
                      CicUtil.mk_rels paramsno 2 @ [Cic.Rel 1])
                  ) t, tl)
         | _,_ -> assert false
       in
        aux (List.length fields) (CicSubstitution.lift 2 ty,field_names)
   | _ -> assert false
;;

let generate_projections ~add_obj ~add_coercion (uri as orig_uri) obj =
 match obj with
  | Cic.InductiveDefinition (inductivefuns,_,_,attrs) ->
     let rec get_record_attrs =
       function
       | [] -> None
       | (`Class (`Record fields))::_ -> Some fields
       | _::tl -> get_record_attrs tl
     in
      (match get_record_attrs attrs with
      | None -> []
      | Some fields ->
         let uris = ref [] in
         let projections = 
           projections_of uri (List.map (fun (x,_,_) -> x) fields) 
         in
          List.iter2 
            (fun (uri, name, bo) (_name, coercion, arity) ->
             try
              let ty, _ =
                CicTypeChecker.type_of_aux' [] [] bo CicUniv.oblivion_ugraph in
              let attrs = [`Class `Projection; `Generated] in
              let obj = Cic.Constant (name,Some bo,ty,[],attrs) in
              let lemmas = add_obj uri obj in
              let lemmas1 = 
                if not coercion then [] else 
                 add_coercion uri arity 0 (UriManager.buri_of_uri orig_uri)
              in
               uris := lemmas1 @ lemmas @ uri::!uris
             with
                CicTypeChecker.TypeCheckerFailure s ->
                 HLog.message ("Unable to create projection " ^ name ^
                  " cause: " ^ Lazy.force s);
              | CicEnvironment.Object_not_found uri ->
                 let depend = UriManager.name_of_uri uri in
                  HLog.message ("Unable to create projection " ^ name ^
                   " because it requires " ^ depend)
            ) projections fields;
          !uris)
  | _ -> []
;;


let init () = 
  LibrarySync.add_object_declaration_hook generate_projections;;
