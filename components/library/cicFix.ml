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

(* $Id: librarySync.ml 9482 2009-01-08 18:12:28Z tassi $ *)

let generate_sibling_mutual_definitions ~add_obj ~add_coercion uri obj =
 match obj with
 | Cic.Constant (name_to_avoid,Some bo,_,_,attrs) when
   List.mem (`Flavour `MutualDefinition) attrs ->
    (match bo with
      Cic.Fix (_,funs) ->
       snd (
        List.fold_right
         (fun (name,idx,ty,bo) (n,uris) ->
           if name = name_to_avoid then
            (n-1,uris)
           else
            let uri =
             UriManager.uri_of_string
              (UriManager.buri_of_uri uri ^ "/" ^ name ^ ".con") in
  	        let bo = Cic.Fix (n-1,funs) in 
            let obj = Cic.Constant (name,Some bo,ty,[],attrs) in
            let lemmas = add_obj uri obj in
            (n-1,lemmas @ uri::uris))
         (List.tl funs) (List.length funs,[]))
    | Cic.CoFix (_,funs) ->
       snd (
        List.fold_right
         (fun (name,ty,bo) (n,uris) ->
           if name = name_to_avoid then
            (n-1,uris)
           else
            let uri =
             UriManager.uri_of_string
              (UriManager.buri_of_uri uri ^ "/" ^ name ^ ".con") in
            let bo = Cic.CoFix (n-1,funs) in 
            let obj = Cic.Constant (name,Some bo,ty,[],attrs) in
            let lemmas = add_obj uri obj in
             (n-1,lemmas @ uri::uris)) 
          (List.tl funs) (List.length funs,[]))
    | _ -> assert false)
  | _ -> []
;;


let init () = 
  LibrarySync.add_object_declaration_hook generate_sibling_mutual_definitions;;
