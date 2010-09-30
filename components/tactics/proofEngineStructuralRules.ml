(* Copyright (C) 2002, HELM Team.
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

(* $Id$ *)

module PET = ProofEngineTypes
module C = Cic

let clearbody ~hyp = 
 let clearbody (proof, goal) =
   let curi,metasenv,_subst,pbo,pty, attrs = proof in
    let metano,_,_ = CicUtil.lookup_meta goal metasenv in
     let string_of_name =
      function
         C.Name n -> n
       | C.Anonymous -> "_"
     in
     let metasenv' =
      List.map
       (function
           (m,canonical_context,ty) when m = metano ->
             let canonical_context' =
              List.fold_right
               (fun entry context ->
                 match entry with
                    Some (C.Name hyp',C.Def (term,ty)) when hyp = hyp' ->
                     let cleared_entry = Some (C.Name hyp, Cic.Decl ty) in
                      cleared_entry::context
                  | None -> None::context
                  | Some (n,C.Decl t) ->
                     let _,_ =
                      try
                       CicTypeChecker.type_of_aux' metasenv context t
                        CicUniv.oblivion_ugraph (* TASSI: FIXME *)
                      with
                       _ ->
                         raise
                          (PET.Fail
                            (lazy ("The correctness of hypothesis " ^
                             string_of_name n ^
                             " relies on the body of " ^ hyp)
                          ))
                     in
                      entry::context
                  | Some (n,Cic.Def (te,ty)) ->
                     (try
                       ignore
                        (CicTypeChecker.type_of_aux' metasenv context te
                          CicUniv.oblivion_ugraph (* TASSI: FIXME *));
                       ignore
                        (CicTypeChecker.type_of_aux' metasenv context ty
                          CicUniv.oblivion_ugraph (* TASSI: FIXME *));
                      with
                       _ ->
                         raise
                          (PET.Fail
                            (lazy ("The correctness of hypothesis " ^
                             string_of_name n ^
                             " relies on the body of " ^ hyp)
                          )));
                     entry::context
               ) canonical_context []
             in
              let _,_ =
               try
                CicTypeChecker.type_of_aux' metasenv canonical_context' ty
                 CicUniv.oblivion_ugraph (* TASSI: FIXME *)
               with
                _ ->
                 raise
                  (PET.Fail
                   (lazy ("The correctness of the goal relies on the body of " ^
                    hyp)))
              in
               m,canonical_context',ty
         | t -> t
       ) metasenv
     in
      (curi,metasenv',_subst,pbo,pty, attrs), [goal]
 in
  PET.mk_tactic clearbody

let clear_one ~hyp =
 let clear_one (proof, goal) =
   let curi,metasenv,_subst,pbo,pty, attrs = proof in
    let metano,context,ty =
     CicUtil.lookup_meta goal metasenv
    in
     let string_of_name =
      function
         C.Name n -> n
       | C.Anonymous -> "_"
     in
     let metasenv' =
      List.map
       (function
           (m,canonical_context,ty) when m = metano ->
             let context_changed, canonical_context' =
              List.fold_right
               (fun entry (b, context) ->
                 match entry with
                    Some (Cic.Name hyp',_) when hyp' = hyp -> 
                      (true, None::context)
                  | None -> (b, None::context)
                  | Some (n,C.Decl t)
                  | Some (n,Cic.Def (t,_)) ->
                      if b then
                         let _,_ =
                          try
                           CicTypeChecker.type_of_aux' metasenv context t
                            CicUniv.oblivion_ugraph
                          with _ ->
                           raise
                            (PET.Fail
                              (lazy ("Hypothesis " ^ string_of_name n ^
                               " uses hypothesis " ^ hyp)))
                         in
                          (b, entry::context)
                      else
                        (b, entry::context)
               ) canonical_context (false, [])
             in
             if not context_changed then
               raise (PET.Fail (lazy ("Hypothesis " ^ hyp ^ " does not exist")));
             let _,_ =
               try
                CicTypeChecker.type_of_aux' metasenv canonical_context' ty
                 CicUniv.oblivion_ugraph 
               with _ ->
                raise (PET.Fail (lazy ("Hypothesis " ^ hyp ^ " occurs in the goal")))
              in
               m,canonical_context',ty
         | t -> t
       ) metasenv
     in
      (curi,metasenv',_subst,pbo,pty, attrs), [goal]
 in
  PET.mk_tactic clear_one

let clear ~hyps =
   let clear status =
      let aux status hyp = 
         match PET.apply_tactic (clear_one ~hyp) status with
	    | proof, [g] -> proof, g
	    | _          -> raise (PET.Fail (lazy "clear: internal error"))
      in
      let proof, g = List.fold_left aux status hyps in
      proof, [g]
   in
   PET.mk_tactic clear

(* Warning: this tactic has no effect on the proof term.
   It just changes the name of an hypothesis in the current sequent *)
let rename ~froms ~tos =
   let rename (proof, goal) =
      let error = "rename: lists of different length" in
      let assocs = 
         try List.combine froms tos
	 with Invalid_argument _ -> raise (PET.Fail (lazy error))
      in
      let curi, metasenv, _subst, pbo, pty, attrs = proof in
      let metano, _, _ = CicUtil.lookup_meta goal metasenv in      
      let rename_map = function
         | Some (Cic.Name hyp, decl_or_def) as entry ->
	    begin try Some (Cic.Name (List.assoc hyp assocs), decl_or_def)
	    with Not_found -> entry end
         | entry -> entry
      in
      let map = function
         | m, canonical_context, ty when m = metano ->
	    let canonical_context = List.map rename_map canonical_context in
            m, canonical_context, ty
         | conjecture -> conjecture
      in
      let metasenv = List.map map metasenv in
      (curi, metasenv, _subst, pbo, pty, attrs), [goal]
   in
   PET.mk_tactic rename
