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

module Ast = CicNotationPt
module Util = CicNotationUtil

module Matcher32 =
struct
  module Pattern32 =
  struct
    type cic_mask_t =
      Blob
    | Uri of UriManager.uri
    | NRef of NReference.reference
    | Appl of cic_mask_t list

    let uri_of_term t = CicUtil.uri_of_term (Deannotate.deannotate_term t)

    let mask_of_cic = function
      | Cic.AAppl (_, tl) -> Appl (List.map (fun _ -> Blob) tl), tl
      | Cic.AConst (_, _, [])
      | Cic.AVar (_, _, [])
      | Cic.AMutInd (_, _, _, [])
      | Cic.AMutConstruct (_, _, _, _, []) as t -> Uri (uri_of_term t), []
      | _ -> Blob, []

    let tag_of_term t =
      let mask, tl = mask_of_cic t in
      Hashtbl.hash mask, tl

    let mask_of_appl_pattern = function
      | Ast.NRefPattern nref -> NRef nref, []
      | Ast.UriPattern uri -> Uri uri, []
      | Ast.ImplicitPattern
      | Ast.VarPattern _ -> Blob, []
      | Ast.ApplPattern pl -> Appl (List.map (fun _ -> Blob) pl), pl

    let tag_of_pattern p =
      let mask, pl = mask_of_appl_pattern p in
      Hashtbl.hash mask, pl

    type pattern_t = Ast.cic_appl_pattern
    type term_t = Cic.annterm

    let string_of_pattern = CicNotationPp.pp_cic_appl_pattern
    let string_of_term t = CicPp.ppterm (Deannotate.deannotate_term t)

    let classify = function
      | Ast.ImplicitPattern
      | Ast.VarPattern _ -> PatternMatcher.Variable
      | Ast.UriPattern _
      | Ast.NRefPattern _
      | Ast.ApplPattern _ -> PatternMatcher.Constructor
  end

  module M = PatternMatcher.Matcher (Pattern32)

  let compiler rows =
    let match_cb rows matched_terms constructors =
     HExtlib.list_findopt
      (fun (pl,pid) _ ->
        let env =
          try
            List.map2
              (fun p t ->
                match p with
                | Ast.ImplicitPattern -> Util.fresh_name (), t
                | Ast.VarPattern name -> name, t
                | _ -> assert false)
              pl matched_terms
          with Invalid_argument _ -> assert false in
        let rec check_non_linear_patterns =
         function
            [] -> true
          | (name,t)::tl ->
             List.for_all
              (fun (name',t') ->
                name <> name' ||
                CicUtil.alpha_equivalence
                 (Deannotate.deannotate_term t) (Deannotate.deannotate_term t')
              ) tl && check_non_linear_patterns tl
        in
         if check_non_linear_patterns env then
          Some (env, constructors, pid)
         else
          None
      ) rows
    in
    M.compiler rows match_cb (fun () -> None)
end

