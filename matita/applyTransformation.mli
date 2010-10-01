(* Copyright (C) 2000-2002, HELM Team.
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
(*                               PROJECT HELM                              *)
(*                                                                         *)
(*                   Andrea Asperti <asperti@cs.unibo.it>                  *)
(*                                21/11/2003                               *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)

val mml_of_cic_sequent:
 Cic.metasenv ->                              (* metasenv *)
 Cic.conjecture ->                            (* sequent *)
  Gdome.document *                              (* Math ML *)
   Cic.conjecture *                             (* unshared sequent *)
   (Cic.annconjecture *                         (* annsequent *)
    ((Cic.id, Cic.term) Hashtbl.t *             (* id -> term *)
     (Cic.id, Cic.id option) Hashtbl.t *        (* id -> father id *)
     (Cic.id, Cic.hypothesis) Hashtbl.t *       (* id -> hypothesis *)
     (Cic.id, Cic2acic.sort_kind) Hashtbl.t))   (* ids_to_inner_sorts *)

val nmml_of_cic_sequent:
 #NCicCoercion.status ->
 NCic.metasenv -> NCic.substitution ->          (* metasenv, substitution *)
 int * NCic.conjecture ->                       (* sequent *)
  Gdome.document                                (* Math ML *)

val ntxt_of_cic_sequent:
 map_unicode_to_tex:bool -> int ->
 #NCicCoercion.status ->
 NCic.metasenv -> NCic.substitution ->          (* metasenv, substitution *)
 int * NCic.conjecture ->                       (* sequent *)
  string                                        (* text *)

val mml_of_cic_object:
  Cic.obj ->                                  (* object *)
    Gdome.document *                            (* Math ML *)
     (Cic.annobj *                              (* annobj *)
      ((Cic.id, Cic.term) Hashtbl.t *           (* id -> term *)
       (Cic.id, Cic.id option) Hashtbl.t *      (* id -> father id *)
       (Cic.id, Cic.conjecture) Hashtbl.t *     (* id -> conjecture *)
       (Cic.id, Cic.hypothesis) Hashtbl.t *     (* id -> hypothesis *)
       (Cic.id, Cic2acic.sort_kind) Hashtbl.t * (* ids_to_inner_sorts *)
       (Cic.id, Cic2acic.anntypes) Hashtbl.t))  (* ids_to_inner_types *)

val nmml_of_cic_object: #NCicCoercion.status -> NCic.obj -> Gdome.document

val ntxt_of_cic_object:
 map_unicode_to_tex:bool -> int -> #NCicCoercion.status -> NCic.obj -> string

val txt_of_cic_sequent_all:
 map_unicode_to_tex:bool -> int ->
 Cic.metasenv ->                              (* metasenv *)
 Cic.conjecture ->                            (* sequent *)
  string *                                    (* text *)
   Cic.conjecture *                             (* unshared sequent *)
   (Cic.annconjecture *                         (* annsequent *)
    ((Cic.id, Cic.term) Hashtbl.t *             (* id -> term *)
     (Cic.id, Cic.id option) Hashtbl.t *        (* id -> father id *)
     (Cic.id, Cic.hypothesis) Hashtbl.t *       (* id -> hypothesis *)
     (Cic.id, Cic2acic.sort_kind) Hashtbl.t))   (* ids_to_inner_sorts *)

val txt_of_cic_term: 
  map_unicode_to_tex:bool -> int -> Cic.metasenv -> Cic.context -> Cic.term ->
   string 
val txt_of_cic_sequent: 
  map_unicode_to_tex:bool -> int -> Cic.metasenv -> Cic.conjecture -> string
val txt_of_cic_sequent_conclusion: 
  map_unicode_to_tex:bool -> output_type:[`Pattern | `Term] -> int ->
   Cic.metasenv -> Cic.conjecture -> string

(* columns, params, object *)
val txt_of_cic_object: 
  map_unicode_to_tex:bool -> 
  ?skip_thm_and_qed:bool -> ?skip_initial_lambdas:int -> 
  int -> GrafiteAst.inline_param list -> Cic.obj ->
    string

val txt_of_cic_object_all: 
  map_unicode_to_tex:bool -> 
  ?skip_thm_and_qed:bool -> ?skip_initial_lambdas:int -> 
  int -> GrafiteAst.inline_param list -> Cic.obj ->
    string *                                    (* text *)
     (Cic.annobj *                              (* annobj *)
      ((Cic.id, Cic.term) Hashtbl.t *           (* id -> term *)
       (Cic.id, Cic.id option) Hashtbl.t *      (* id -> father id *)
       (Cic.id, Cic.conjecture) Hashtbl.t *     (* id -> conjecture *)
       (Cic.id, Cic.hypothesis) Hashtbl.t *     (* id -> hypothesis *)
       (Cic.id, Cic2acic.sort_kind) Hashtbl.t * (* ids_to_inner_sorts *)
       (Cic.id, Cic2acic.anntypes) Hashtbl.t))  (* ids_to_inner_types *)

(* params, uri or baseuri *)
val txt_of_inline_macro:
  map_unicode_to_tex:bool -> GrafiteAst.inline_param list -> string ->
    string

val txt_of_macro:
  map_unicode_to_tex:bool ->
    Cic.metasenv ->
    Cic.context ->
    (Cic.term, Cic.lazy_term) GrafiteAst.macro -> string

(* columns, rendering depth, context, term *)
val procedural_txt_of_cic_term: 
  map_unicode_to_tex:bool -> int -> GrafiteAst.inline_param list -> 
  Cic.context -> Cic.term ->
    string
