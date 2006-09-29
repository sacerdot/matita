(* Copyright (C) 2006, HELM Team.
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

let raw_preamble buri = "
inductive eq (A:Type) (x:A) : A \\to Prop \\def refl_eq : eq A x x.

theorem sym_eq : \\forall A:Type.\\forall x,y:A. eq A x y \\to eq A y x.
intros.elim H. apply refl_eq.
qed.

theorem eq_elim_r:
 \\forall A:Type.\\forall x:A. \\forall P: A \\to Prop.
   P x \\to \\forall y:A. eq A y x \\to P y.
intros. elim (sym_eq ? ? ? H1).assumption.
qed.

theorem trans_eq : 
    \\forall A:Type.\\forall x,y,z:A. eq A x y \\to eq A y z \\to eq A x z.
intros.elim H1.assumption.
qed.

default \"equality\"
 " ^ buri ^ "/eq.ind
 " ^ buri ^ "/sym_eq.con
 " ^ buri ^ "/trans_eq.con
 " ^ buri ^ "/eq_ind.con
 " ^ buri ^ "/eq_elim_r.con
 " ^ buri ^ "/eq_f.con
 " ^ buri ^ "/eq_f1.con.

theorem eq_f: \\forall  A,B:Type.\\forall f:A\\to B.
  \\forall x,y:A. eq A x y \\to eq B (f x) (f y).
intros.elim H.reflexivity.
qed.

theorem eq_f1: \\forall  A,B:Type.\\forall f:A\\to B.
  \\forall x,y:A. eq A x y \\to eq B (f y) (f x).
intros.elim H.reflexivity.
qed.

inductive ex (A:Type) (P:A \\to Prop) : Prop \\def
    ex_intro: \\forall x:A. P x \\to ex A P.
interpretation \"exists\" 'exists \\eta.x =
  (" ^ buri ^ "/ex.ind#xpointer(1/1) _ x).

notation < \"hvbox(\\exists ident i opt (: ty) break . p)\"
  right associative with precedence 20
for @{ 'exists ${default
  @{\\lambda ${ident i} : $ty. $p)}
  @{\\lambda ${ident i} . $p}}}.

"
;;

let p_to_ma ?timeout ~tptppath ~filename () = 
  let data = 
     Tptp2grafite.tptp2grafite ?timeout ~filename ~tptppath:tptppath
     ~raw_preamble ()
  in
  data
;;

let main () =
  MatitaInit.fill_registry ();
  let tptppath = ref "./" in
  let timeout = ref 600 in
  MatitaInit.add_cmdline_spec
    ["-tptppath",Arg.String (fun s -> tptppath:= s),
       "Where to find the Axioms/ and Problems/ directory";
     "-timeout", Arg.Int (fun x -> timeout := x),
       "Timeout in seconds"];
  MatitaInit.parse_cmdline ();
  MatitaInit.load_configuration_file ();
  Helm_registry.set_bool "db.nodb" true;
  Helm_registry.set_bool "matita.nodisk" true;
  HLog.set_log_callback (fun _ _ -> ()); 
  let args = Helm_registry.get_list Helm_registry.string "matita.args" in
  let inputfile = 
    match args with
    | [file] -> file
    | _ -> prerr_endline "You must specify exactly one .p file."; exit 1
  in
  let data = 
    p_to_ma ~timeout:!timeout ~filename:inputfile ~tptppath:!tptppath ()
  in
(*   prerr_endline data; *)
  let is = Ulexing.from_utf8_string data in
  let gs = GrafiteSync.init () in
  let ls = 
    CicNotation2.load_notation ~include_paths:[] 
      BuildTimeConf.core_notation_script 
  in
  Sys.catch_break true;
  try
    let _ = 
      MatitaEngine.eval_from_stream 
        ~first_statement_only:false 
        ~include_paths:[]
        ~clean_baseuri:true
        ~do_heavy_checks:false
        ~prompt:false
        ls gs is
         (fun _ _ -> ()) 
(*
        (fun _ s -> 
          let pp_ast_statement =
            GrafiteAstPp.pp_statement ~term_pp:CicNotationPp.pp_term
            ~lazy_term_pp:CicNotationPp.pp_term ~obj_pp:CicNotationPp.pp_obj
          in
          prerr_endline (pp_ast_statement s)) 
*)
    in
    exit 0
  with exn ->
    prerr_endline (snd (MatitaExcPp.to_string exn));
    exit 1
;;
