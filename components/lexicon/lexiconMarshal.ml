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

type lexicon = LexiconAst.command list

let format_name = "lexicon"

let save_lexicon_to_file ~fname lexicon =
  HMarshal.save ~fmt:format_name ~version:LexiconAst.magic ~fname lexicon

let load_lexicon_from_file ~fname =
  let raw = HMarshal.load ~fmt:format_name ~version:LexiconAst.magic ~fname in
  (raw: lexicon)

let rehash_cmd_uris =
  let rehash_uri uri =
    UriManager.uri_of_string (UriManager.string_of_uri uri) in
  function
  | LexiconAst.Interpretation (loc, dsc, args, cic_appl_pattern) ->
      let rec aux =
        function
        | NotationPt.UriPattern uri ->
            NotationPt.UriPattern (rehash_uri uri)
        | NotationPt.NRefPattern (NReference.Ref (uri,spec)) ->
           let uri = NCicLibrary.refresh_uri uri in
            NotationPt.NRefPattern (NReference.reference_of_spec uri spec)
        | NotationPt.ApplPattern args ->
            NotationPt.ApplPattern (List.map aux args)
        | NotationPt.VarPattern _
        | NotationPt.ImplicitPattern as pat -> pat
      in
      let appl_pattern = aux cic_appl_pattern in
      LexiconAst.Interpretation (loc, dsc, args, appl_pattern)
  | LexiconAst.Notation _
  | LexiconAst.Alias _ as cmd -> cmd
  | cmd ->
      prerr_endline "Found a command not expected in a .lexicon:";
      prerr_endline (LexiconAstPp.pp_command cmd);
      assert false

let save_lexicon ~fname lexicon = save_lexicon_to_file ~fname (List.rev lexicon)

let load_lexicon ~fname =
  let lexicon = load_lexicon_from_file ~fname in
  List.map rehash_cmd_uris lexicon

