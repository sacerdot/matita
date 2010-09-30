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

(* functions to be moved ****************************************************)

val list_rev_map2: ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val list_map2_filter: ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list

val mk_arel: int -> string -> Cic.annterm

(****************************************************************************)

type flavour  = Cic.object_flavour
type name     = string option
type hyp      = string
type what     = Cic.annterm
type how      = bool
type using    = Cic.annterm
type count    = int
type note     = string
type where    = (hyp * name) option
type inferred = Cic.annterm
type pattern  = Cic.annterm
type body     = Cic.annterm option
type types    = Cic.anninductiveType list
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

val render_steps: 
   (what, inferred, [> `Whd] as 'b, what CicNotationPt.obj, hyp) GrafiteAst.statement list -> 
   step list -> 
   (what, inferred, 'b, what CicNotationPt.obj, hyp) GrafiteAst.statement list

val count_steps:
   int -> step list -> int

val count_nodes:
   int -> step list -> int

val note_of_step:
   step -> note
