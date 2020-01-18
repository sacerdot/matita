(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department, University of Bologna, Italy.
    ||I||
    ||T||  HELM is free software; you can redistribute it and/or
    ||A||  modify it under the terms of the GNU General Public License
    \   /  version 2 or (at your option) any later version.
     \ /   This software is distributed as is, NO WARRANTY.
      V_______________________________________________________________ *)

module A = Array
module P = Printf

module C  = NCic
module R  = Helm_registry
module U  = NUri
module US = NUri.UriSet

module UriPair = struct

  type t = U.uri * U.uri

  let equal (u1l,u1r) (u2l,u2r) =
     U.eq u1l u2l && U.eq u1r u2r

  let compare (u1l,u1r) (u2l,u2r) =
    match U.compare u1l u2l with
    | 0 -> U.compare u1r u2r
    | c -> c

  let hash (ul,ur) =
    Hashtbl.hash (U.hash ul, U.hash ur)

end

module UPS = Set.Make(UriPair)

type def_xflavour = [ C.def_flavour
                    | `Inductive
                    ]

let default_objs = US.empty

let default_srcs = US.empty

let default_names = US.empty

let default_remove = []

let default_exclude = []

let default_net = 0

let default_chars = 0

let default_debug_lexer = false

let default_no_devel = true

let default_no_init = true

let xflavours = 8

let slot = A.make xflavours 0

let objs = ref default_objs

let srcs = ref default_srcs

let names = ref default_names

let remove = ref default_remove

let exclude = ref default_exclude

let net = ref default_net

let chars = ref default_chars

let debug_lexer = ref default_debug_lexer

let no_devel = ref default_no_devel

let no_init = ref default_no_init

let deps = ref UPS.empty

let index_of_xflavour = function
  | `Inductive  -> 0
  | `Axiom      -> 1
  | `Definition -> 2
  | `Fact       -> 3
  | `Lemma      -> 4
  | `Theorem    -> 5
  | `Corollary  -> 6
  | `Example    -> 7

let add_xflavour n xf =
  let i = index_of_xflavour xf in
  slot.(i) <- slot.(i) + n

let clear_slot i _ = slot.(i) <- 0

let iter_xflavours map = A.iteri (fun _ -> map) slot

let add_dep c u =
  deps := UPS.add (c,u) !deps

let out_deps file =
  let och = open_out file in
  let map (a,b) =
    P.fprintf och "\"%s\": \"%s\"\n" (U.string_of_uri a) (U.string_of_uri b)
  in
  UPS.iter map !deps;
  close_out och

let clear () =
  R.clear (); A.iteri clear_slot slot;
  objs := default_objs; srcs := default_srcs; names := default_names;
  remove := default_remove; exclude := default_exclude; net := default_net;
  chars := default_chars; debug_lexer := default_debug_lexer;
  no_devel := default_no_devel; no_init := default_no_init;
  deps := UPS.empty
