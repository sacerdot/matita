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

module G = GrafiteAst
module L = LexiconAst
module H = HExtlib

(* from transcript *)

let out_comment och s =
   let s = if s <> "" && s.[0] = '*' then "#" ^ s else s in 
   Printf.fprintf och "%s%s%s\n\n" "(*" s "*)"

let out_line_comment och s =
   let l = 70 - String.length s in
   let s = Printf.sprintf " %s %s" s (String.make l '*') in
   out_comment och s

let out_preamble och (path, lines) =
   let ich = open_in path in
   let rec print i =
      if i > 0 then 
         let s = input_line ich in
         begin Printf.fprintf och "%s\n" s; print (pred i) end
   in 
   print lines;
   out_line_comment och "This file was automatically generated: do not edit"

(* from matitacLib *)

let pp_ast_statement st =
  GrafiteAstPp.pp_statement ~term_pp:CicNotationPp.pp_term
    ~map_unicode_to_tex:(Helm_registry.get_bool
      "matita.paste_unicode_as_tex")
    ~lazy_term_pp:CicNotationPp.pp_term ~obj_pp:(CicNotationPp.pp_obj CicNotationPp.pp_term) st

(**)

let dump f =
   Helm_registry.set_bool "matita.moo" false;
   let floc = H.dummy_floc in
   let nl_ast = G.Comment (floc, G.Note (floc, "")) in
   let och = open_out f in
   let atexit () = close_out och in
   let nl () =  output_string och (pp_ast_statement nl_ast) in
   let rt_base_dir = Filename.dirname Sys.argv.(0) in
   let path = Filename.concat rt_base_dir "matita.ma.templ" in
   let lines = 14 in
   out_preamble och (path, lines);
   let grafite_parser_cb fname = 
      let ast = G.Executable (floc, G.Command (floc, G.Include (floc, fname))) in
      output_string och (pp_ast_statement ast); nl (); nl ()
   in
   let matita_engine_cb = function
      | G.Executable (_, G.Macro (_, G.Inline _)) 
      | G.Executable (_, G.Command (_, G.Include _)) -> ()
      | ast                                          ->
         output_string och (pp_ast_statement ast); nl (); nl ()
   in
   let matitac_lib_cb = output_string och in
   GrafiteParser.set_callback grafite_parser_cb;
   MatitaEngine.set_callback matita_engine_cb;
   MatitacLib.set_callback matitac_lib_cb;
   at_exit atexit
   
let main () =
 Helm_registry.set_bool "matita.moo" true;
 match Filename.basename Sys.argv.(0) with
 |"gragrep"    |"gragrep.opt"    |"gragrep.opt.static"    ->Gragrep.main()
 |"matitadep"  |"matitadep.opt"  |"matitadep.opt.static"  ->Matitadep.main()
 |"matitaclean"|"matitaclean.opt"|"matitaclean.opt.static"->Matitaclean.main()
 |"matitamake" |"matitamake.opt" |"matitamake.opt.static" ->Matitamake.main()
 |"matitaprover"|"matitaprover.opt"
 |"matitaprover.opt.static" ->Matitaprover.main()
 |"matitawiki"|"matitawiki.opt" ->MatitaWiki.main()
 | _ ->
      let dump_msg = "<filename> Dump source with expanded macros to <filename>" in
      MatitaInit.add_cmdline_spec ["-dump", Arg.String dump, dump_msg];
      MatitacLib.main ()

let _ = main ()

