type word = string

type words = word list

type subst = words list

type substs = subst list

type mrc_status = {
(* component module *)
  cmod   : string; 
(* register module *)
  rmod   : string;
(* register function *)
  rfun   : string;
(* optional depend module *)
  dmod   : string;
(* parallel component *)
  para   : bool;
(* optional component *)
  optn   : bool;
(* substitutions *)
  substs : substs;
}

type idx_status = {
(* indexed directory *)
  cdir: string;
(* indexed modules *)
  mods: string list;
}
