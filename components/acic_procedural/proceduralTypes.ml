(* Copyright (C) 2003-2005, HELM Team.
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

module HEL = HExtlib
module C   = Cic
module I   = CicInspect
module G   = GrafiteAst
module N   = CicNotationPt

module H   = ProceduralHelpers

(* functions to be moved ****************************************************)

let list_rev_map2 map l1 l2 =
   let rec aux res = function
      | hd1 :: tl1, hd2 :: tl2 -> aux (map hd1 hd2 :: res) (tl1, tl2)
      | _                      -> res
   in
   aux [] (l1, l2)

let list_map2_filter map l1 l2 =
   let rec filter l = function
      | []           -> l
      | None :: tl   -> filter l tl
      | Some a :: tl -> filter (a :: l) tl 
  in 
  filter [] (list_rev_map2 map l1 l2)

let list_init f i =
   let rec aux a j = if j < 0 then a else aux (f j :: a) (pred j) in
   aux [] i

(****************************************************************************)

type flavour  = C.object_flavour
type name     = string option
type hyp      = string
type what     = C.annterm
type how      = bool
type using    = C.annterm
type count    = int
type note     = string
type where    = (hyp * name) option
type inferred = C.annterm
type pattern  = C.annterm
type body     = C.annterm option
type types    = C.anninductiveType list
type lpsno    = int
type fields   = (string * bool * int) list

type step = Note of note 
          | Record of types * lpsno * fields * note
          | Inductive of types * lpsno * note
	  | Statement of flavour * name * what * body * note
          | Qed of note
	  | Id of note
	  | Exact of what * note
	  | Intros of count option * name list * note
	  | Cut of name * what * note
	  | LetIn of name * what * note
	  | LApply of name * what * note
	  | Rewrite of how * what * where * pattern * note
	  | Elim of what * using option * pattern * note
	  | Cases of what * pattern * note
	  | Apply of what * note
	  | Change of inferred * what * where * pattern * note 
	  | Clear of hyp list * note
	  | ClearBody of hyp * note
	  | Branch of step list list * note
          | Reflexivity of note

(* annterm constructors *****************************************************)

let mk_arel i b = C.ARel ("", "", i, b)

(* FG: this is really awful !! *)
let arel_of_name = function
   | C.Name s    -> mk_arel 0 s
   | C.Anonymous -> mk_arel 0 "_"

(* helper functions on left params for use with inductive types *************)

let strip_lps lpsno arity =
   let rec aux no lps = function
      | C.AProd (_, name, w, t) when no > 0 ->
         let lp = name, Some w in
	 aux (pred no) (lp :: lps) t
      | t                                   -> lps, t
   in
   aux lpsno [] arity

let merge_lps lps1 lps2 =
   let map (n1, w1) (n2, _) =
      let n = match n1, n2 with
         | C.Name _, _ -> n1
	 | _           -> n2
      in
      n, w1
   in
   if lps1 = [] then lps2 else
   List.map2 map lps1 lps2

(* grafite ast constructors *************************************************)

let floc = HEL.dummy_floc

let mk_note str = G.Comment (floc, G.Note (floc, str))

let mk_tacnote str a =
   if str = "" then mk_note "" :: a else mk_note "" :: mk_note str :: a

let mk_notenote str a =
   if str = "" then a else mk_note str :: a

let mk_thnote str a =
   if str = "" then a else mk_note "" :: mk_note str :: a

let mk_pre_inductive types lpsno =
   let map1 (lps1, cons) (name, arity) = 
      let lps2, arity = strip_lps lpsno arity in
      merge_lps lps1 lps2, (name, arity) :: cons
   in
   let map2 (lps1, types) (_, name, kind, arity, cons) =
      let lps2, arity = strip_lps lpsno arity in 
      let lps1, rev_cons = List.fold_left map1 (lps1, []) cons in 
      merge_lps lps1 lps2, (name, kind, arity, List.rev rev_cons) :: types
   in
   let map3 (name, xw) = arel_of_name name, xw in
   let rev_lps, rev_types = List.fold_left map2 ([], []) types in
   List.rev_map map3 rev_lps, List.rev rev_types

let mk_inductive types lpsno =
   let lpars, types = mk_pre_inductive types lpsno in
   let obj = N.Inductive (lpars, types) in
   G.Executable (floc, G.Command (floc, G.Obj (floc, obj)))

let mk_record types lpsno fields =
   match mk_pre_inductive types lpsno with
      | lpars, [name, _, ty, [_, cty]] -> 
         let map (fields, cty) (name, coercion, arity) =
	    match cty with
	       | C.AProd (_, _, w, t) ->
	          (name, w, coercion, arity) :: fields, t
	       | _                    ->
	          assert false
	 in
	 let rev_fields, _ = List.fold_left map ([], cty) fields in 
	 let fields = List.rev rev_fields in
	 let obj = N.Record (lpars, name, ty, fields) in
         G.Executable (floc, G.Command (floc, G.Obj (floc, obj)))
      | _ -> assert false

let mk_statement flavour name t v =
   let name = match name with Some name -> name | None -> assert false in
   let obj = N.Theorem (flavour, name, t, v, `Regular) in
   G.Executable (floc, G.Command (floc, G.Obj (floc, obj)))

let mk_qed =
   G.Executable (floc, G.Command (floc, G.Qed floc))

let mk_tactic tactic punctation =
   G.Executable (floc, G.Tactic (floc, Some tactic, punctation))

let mk_punctation punctation =
   G.Executable (floc, G.Tactic (floc, None, punctation))

let mk_id punctation =
   let tactic = G.IdTac floc in
   mk_tactic tactic punctation

let mk_exact t punctation =
   let tactic = G.Exact (floc, t) in
   mk_tactic tactic punctation

let mk_intros xi xids punctation =
   let tactic = G.Intros (floc, (xi, xids)) in
   mk_tactic tactic punctation

let mk_cut name what punctation =
   let name = match name with Some name -> name | None -> assert false in
   let tactic = G.Cut (floc, Some name, what) in
   mk_tactic tactic punctation

let mk_letin name what punctation =
   let name = match name with Some name -> name | None -> assert false in
   let tactic = G.LetIn (floc, what, name) in
   mk_tactic tactic punctation

let mk_lapply name what punctation =
   let tactic = G.LApply (floc, false, None, [], what, name) in
   mk_tactic tactic punctation

let mk_rewrite direction what where pattern punctation =
   let direction = if direction then `RightToLeft else `LeftToRight in 
   let pattern, rename = match where with
      | None                      -> (None, [], Some pattern), []
      | Some (premise, Some name) -> (None, [premise, pattern], None), [Some name]
      | Some (premise, None)      -> (None, [premise, pattern], None), [] 
   in
   let tactic = G.Rewrite (floc, direction, what, pattern, rename) in
   mk_tactic tactic punctation

let mk_elim what using pattern punctation =
   let pattern = None, [], Some pattern in
   let tactic = G.Elim (floc, what, using, pattern, (Some 0, [])) in
   mk_tactic tactic punctation

let mk_cases what pattern punctation =
   let pattern = None, [], Some pattern in
   let tactic = G.Cases (floc, what, pattern, (Some 0, [])) in
   mk_tactic tactic punctation

let mk_apply t punctation =
   let tactic = G.Apply (floc, t) in
   mk_tactic tactic punctation

let mk_change t where pattern punctation =
   let pattern = match where with
      | None              -> None, [], Some pattern
      | Some (premise, _) -> None, [premise, pattern], None
   in
   let tactic = G.Change (floc, pattern, t) in
   mk_tactic tactic punctation

let mk_clear ids punctation =
   let tactic = G.Clear (floc, ids) in
   mk_tactic tactic punctation

let mk_clearbody id punctation =
   let tactic = G.ClearBody (floc, id) in
   mk_tactic tactic punctation

let mk_reflexivity punctation =
   let tactic = G.Reflexivity floc in
   mk_tactic tactic punctation

let mk_ob = 
   let punctation = G.Branch floc in
   mk_punctation punctation

let mk_dot = G.Dot floc

let mk_sc = G.Semicolon floc

let mk_cb = G.Merge floc

let mk_vb = G.Shift floc

(* rendering ****************************************************************)

let rec render_step sep a = function
   | Note s                    -> mk_notenote s a
   | Statement (f, n, t, v, s) -> mk_statement f n t v :: mk_thnote s a 
   | Inductive (ts, lps, s)    -> mk_inductive ts lps :: mk_thnote s a
   | Record (ts, lps, fs, s)   -> mk_record ts lps fs :: mk_thnote s a
   | Qed s                     -> mk_qed :: mk_tacnote s a
   | Exact (t, s)              -> mk_exact t sep :: mk_tacnote s a   
   | Id s                      -> mk_id sep :: mk_tacnote s a
   | Intros (c, ns, s)         -> mk_intros c ns sep :: mk_tacnote s a
   | Cut (n, t, s)             -> mk_cut n t sep :: mk_tacnote s a
   | LetIn (n, t, s)           -> mk_letin n t sep :: mk_tacnote s a
   | LApply (n, t, s)          -> mk_lapply n t sep :: mk_tacnote s a
   | Rewrite (b, t, w, e, s)   -> mk_rewrite b t w e sep :: mk_tacnote s a
   | Elim (t, xu, e, s)        -> mk_elim t xu e sep :: mk_tacnote s a
   | Cases (t, e, s)           -> mk_cases t e sep :: mk_tacnote s a
   | Apply (t, s)              -> mk_apply t sep :: mk_tacnote s a
   | Change (t, _, w, e, s)    -> mk_change t w e sep :: mk_tacnote s a
   | Clear (ns, s)             -> mk_clear ns sep :: mk_tacnote s a
   | ClearBody (n, s)          -> mk_clearbody n sep :: mk_tacnote s a
   | Branch ([], s)            -> a
   | Branch ([ps], s)          -> render_steps sep a ps
   | Branch (ps :: pss, s)     ->
      let a = mk_ob :: mk_tacnote s a in
      let a = List.fold_left (render_steps mk_vb) a (List.rev pss) in
      mk_punctation sep :: render_steps mk_cb a ps
   | Reflexivity s             -> mk_reflexivity sep :: mk_tacnote s a

and render_steps sep a = function
   | []                                          -> a
   | [p]                                         -> render_step sep a p
   | p :: Branch ([], _) :: ps                   ->
      render_steps sep a (p :: ps)
   | p :: ((Branch (_ :: _ :: _, _) :: _) as ps) ->
      render_steps sep (render_step mk_sc a p) ps
   | p :: ps                                     ->
      render_steps sep (render_step mk_sc a p) ps

let render_steps a = render_steps mk_dot a

(* counting *****************************************************************)

let rec count_step a = function
   | Note _
   | Statement _
   | Inductive _
   | Qed _                  -> a
(* level A0 *)   
   | Branch (pps, _)        -> List.fold_left count_steps a pps
   | Clear _
   | ClearBody _
   | Id _
   | Intros (Some 0, [], _)
(* leval A1 *)   
   | Exact _
(* level B1 *)   
   | Cut _
   | LetIn _
(* level B2 *)   
   | Change _               -> a
(* level C *)   
   | _                      -> succ a   

and count_steps a = List.fold_left count_step a

let count = I.count_nodes ~meta:false

let rec count_node a = function
   | Note _
   | Record _
   | Inductive _
   | Statement _
   | Qed _   
   | Reflexivity _
   | Id _
   | Intros _
   | Clear _
   | ClearBody _             -> a
   | Exact (t, _) 
   | Cut (_, t, _)
   | LetIn (_, t, _)
   | LApply (_, t, _)
   | Apply (t, _)            -> count a (H.cic t)
   | Rewrite (_, t, _, p, _)
   | Elim (t, _, p, _)
   | Cases (t, p, _)
   | Change (t, _, _, p, _)  -> let a = count a (H.cic t) in count a (H.cic p) 
   | Branch (ss, _)          -> List.fold_left count_nodes a ss

and count_nodes a = List.fold_left count_node a

(* helpers ******************************************************************)

let rec note_of_step = function
   | Note s
   | Statement (_, _, _, _, s)
   | Inductive (_, _, s)
   | Record (_, _, _, s)
   | Qed s
   | Exact (_, s)
   | Id s
   | Intros (_, _, s)
   | Cut (_, _, s)
   | LetIn (_, _, s)
   | LApply (_, _, s)
   | Rewrite (_, _, _, _, s)
   | Elim (_, _, _, s)
   | Cases (_, _, s)
   | Apply (_, s)
   | Change (_, _, _, _, s)
   | Clear (_, s)
   | ClearBody (_, s)
   | Reflexivity s
   | Branch (_, s)             -> s
