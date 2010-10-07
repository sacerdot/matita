(* Copyright (C) 2000, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

(***************************************************************************)
(*                                                                         *)
(*                            PROJECT HELM                                 *)
(*                                                                         *)
(*                Andrea Asperti <asperti@cs.unibo.it>                     *)
(*                              19/11/2003                                 *)
(*                                                                         *)
(***************************************************************************)

(* $Id$ *)

let p_mtr a b = Mpresentation.Mtr(a,b)
let p_mtd a b = Mpresentation.Mtd(a,b)
let p_mtable a b = Mpresentation.Mtable(a,b)
let p_mtext a b = Mpresentation.Mtext(a,b)
let p_mi a b = Mpresentation.Mi(a,b)
let p_mo a b = Mpresentation.Mo(a,b)
let p_mrow a b = Mpresentation.Mrow(a,b)
let p_mphantom a b = Mpresentation.Mphantom(a,b)
let b_ink a = Box.Ink a

module K = Content
module P = Mpresentation

let sequent2pres0 term2pres (_,_,context,ty) =
   let context2pres context = 
     let rec aux accum =
     function 
       [] -> accum 
     | None::tl -> aux accum tl
     | (Some (`Declaration d))::tl ->
         let
           { K.dec_name = dec_name ;
             K.dec_id = dec_id ;
             K.dec_type = ty } = d in
         let r = 
           Box.b_h [Some "helm", "xref", dec_id] 
             [ Box.b_object (p_mi []
               (match dec_name with
                  None -> "_"
                | Some n -> n)) ;
               Box.b_space; Box.b_text [] ":"; Box.b_space;
               term2pres ty] in
         aux (r::accum) tl
     | (Some (`Definition d))::tl ->
         let
           { K.def_name = def_name ;
             K.def_id = def_id ;
             K.def_term = bo } = d in
         let r = 
            Box.b_h [Some "helm", "xref", def_id]
              [ Box.b_object (p_mi []
                (match def_name with
                   None -> "_"
                 | Some n -> n)) ; Box.b_space ;
                Box.b_text [] (Utf8Macro.unicode_of_tex "\\def") ;
                Box.b_space; term2pres bo] in
         aux (r::accum) tl
      | _::_ -> assert false in
      aux [] context in
 let pres_context =
  if context <> [] then [Box.b_v [] (context2pres context)] else [] in
 let pres_goal = term2pres ty in 
 (Box.b_h [] [
   Box.b_space; 
   (Box.b_v []
      (Box.b_space ::
       pres_context @ [
       b_ink [None,"width","4cm"; None,"height","2px"]; (* sequent line *)
       Box.b_space; 
       pres_goal]))])

let nsequent2pres ~ids_to_nrefs ~subst =
 let lookup_uri id =
  try
   let nref = Hashtbl.find ids_to_nrefs id in
    Some (NReference.string_of_reference nref)
  with Not_found -> None
 in
  sequent2pres0
    (fun ast ->
      CicNotationPres.box_of_mpres
       (CicNotationPres.render ~lookup_uri
         (TermContentPres.pp_ast ast)))
