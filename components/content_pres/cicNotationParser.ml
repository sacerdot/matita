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

open Printf

module Ast = NotationPt
module Env = NotationEnv

exception Parse_error of string
exception Level_not_found of int

let min_precedence = 0
let max_precedence = 100

type ('a,'b,'c,'d) grammars = {
  level1_pattern: 'a Grammar.Entry.e;
  level2_ast: 'b Grammar.Entry.e;
  level2_ast_grammar : Grammar.g;
  term: 'b Grammar.Entry.e;
  let_defs: 'c Grammar.Entry.e;
  protected_binder_vars: 'd Grammar.Entry.e;
  level2_meta: 'b Grammar.Entry.e;
}

let initial_grammars () =
  let level1_pattern_grammar = 
    Grammar.gcreate (CicNotationLexer.level1_pattern_lexer ()) in
  let level2_ast_grammar = 
    Grammar.gcreate (CicNotationLexer.level2_ast_lexer ()) in
  let level2_meta_grammar = 
    Grammar.gcreate (CicNotationLexer.level2_meta_lexer ()) in
  let level1_pattern =
    Grammar.Entry.create level1_pattern_grammar "level1_pattern" in
  let level2_ast = Grammar.Entry.create level2_ast_grammar "level2_ast" in
  let term = Grammar.Entry.create level2_ast_grammar "term" in
  let let_defs = Grammar.Entry.create level2_ast_grammar "let_defs" in
  let protected_binder_vars = 
    Grammar.Entry.create level2_ast_grammar "protected_binder_vars" in
  let level2_meta = Grammar.Entry.create level2_meta_grammar "level2_meta" in
  { level1_pattern=level1_pattern;
    level2_ast=level2_ast;
    term=term;
    let_defs=let_defs;
    protected_binder_vars=protected_binder_vars;
    level2_meta=level2_meta;
    level2_ast_grammar=level2_ast_grammar;
}
;;

let grammars = ref (initial_grammars ());;

let int_of_string s =
  try
    Pervasives.int_of_string s
  with Failure _ ->
    failwith (sprintf "Lexer failure: string_of_int \"%s\" failed" s)

(** {2 Grammar extension} *)

let level_of precedence =
  if precedence < min_precedence || precedence > max_precedence then
    raise (Level_not_found precedence);
  string_of_int precedence 

let gram_symbol s = Gramext.Stoken ("SYMBOL", s)
let gram_ident s = Gramext.Stoken ("IDENT", s)
let gram_number s = Gramext.Stoken ("NUMBER", s)
let gram_keyword s = Gramext.Stoken ("", s)
let gram_term = function
  | Ast.Self _ -> Gramext.Sself
  | Ast.Level precedence ->
      Gramext.Snterml 
        (Grammar.Entry.obj (!grammars.term: 'a Grammar.Entry.e), 
         level_of precedence)
;;

let gram_of_literal =
  function
  | `Symbol s -> gram_symbol s
  | `Keyword s -> gram_keyword s
  | `Number s -> gram_number s

type binding =
  | NoBinding
  | Binding of string * Env.value_type
  | Env of (string * Env.value_type) list

let make_action action bindings =
  let rec aux (vl : NotationEnv.t) =
    function
      [] -> Gramext.action (fun (loc: Ast.location) -> action vl loc)
    | NoBinding :: tl -> Gramext.action (fun _ -> aux vl tl)
    (* LUCA: DEFCON 3 BEGIN *)
    | Binding (name, Env.TermType l) :: tl ->
        Gramext.action
          (fun (v:Ast.term) ->
            aux ((name, (Env.TermType l, Env.TermValue v))::vl) tl)
    | Binding (name, Env.StringType) :: tl ->
        Gramext.action
          (fun (v:string) ->
            aux ((name, (Env.StringType, Env.StringValue v)) :: vl) tl)
    | Binding (name, Env.NumType) :: tl ->
        Gramext.action
          (fun (v:string) ->
            aux ((name, (Env.NumType, Env.NumValue v)) :: vl) tl)
    | Binding (name, Env.OptType t) :: tl ->
        Gramext.action
          (fun (v:'a option) ->
            aux ((name, (Env.OptType t, Env.OptValue v)) :: vl) tl)
    | Binding (name, Env.ListType t) :: tl ->
        Gramext.action
          (fun (v:'a list) ->
            aux ((name, (Env.ListType t, Env.ListValue v)) :: vl) tl)
    | Env _ :: tl ->
        Gramext.action (fun (v:NotationEnv.t) -> aux (v @ vl) tl)
    (* LUCA: DEFCON 3 END *)
  in
    aux [] (List.rev bindings)

let flatten_opt =
  let rec aux acc =
    function
      [] -> List.rev acc
    | NoBinding :: tl -> aux acc tl
    | Env names :: tl -> aux (List.rev names @ acc) tl
    | Binding (name, ty) :: tl -> aux ((name, ty) :: acc) tl
  in
  aux []

  (* given a level 1 pattern computes the new RHS of "term" grammar entry *)
let extract_term_production pattern =
  let rec aux = function
    | Ast.AttributedTerm (_, t) -> aux t
    | Ast.Literal l -> aux_literal l
    | Ast.Layout l -> aux_layout l
    | Ast.Magic m -> aux_magic m
    | Ast.Variable v -> aux_variable v
    | t ->
        prerr_endline (NotationPp.pp_term t);
        assert false
  and aux_literal =
    function
    | `Symbol s -> [NoBinding, gram_symbol s]
    | `Keyword s ->
        (* assumption: s will be registered as a keyword with the lexer *)
        [NoBinding, gram_keyword s]
    | `Number s -> [NoBinding, gram_number s]
  and aux_layout = function
    | Ast.Sub (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\sub "] @ aux p2
    | Ast.Sup (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\sup "] @ aux p2
    | Ast.Below (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\below "] @ aux p2
    | Ast.Above (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\above "] @ aux p2
    | Ast.Frac (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\frac "] @ aux p2
    | Ast.InfRule (p1, p2, p3) -> [NoBinding, gram_symbol "\\infrule "] @ aux p1 @ aux p2 @ aux p3
    | Ast.Atop (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\atop "] @ aux p2
    | Ast.Over (p1, p2) -> aux p1 @ [NoBinding, gram_symbol "\\over "] @ aux p2
    | Ast.Root (p1, p2) ->
        [NoBinding, gram_symbol "\\root "] @ aux p2
        @ [NoBinding, gram_symbol "\\of "] @ aux p1
    | Ast.Sqrt p -> [NoBinding, gram_symbol "\\sqrt "] @ aux p
    | Ast.Break -> []
    | Ast.Box (_, pl) -> List.flatten (List.map aux pl)
    | Ast.Group pl -> List.flatten (List.map aux pl)
    | Ast.Mstyle (_,pl) -> List.flatten (List.map aux pl)
    | Ast.Mpadded (_,pl) -> List.flatten (List.map aux pl)
    | Ast.Maction l -> List.flatten (List.map aux l)
  and aux_magic magic =
    match magic with
    | Ast.Opt p ->
        let p_bindings, p_atoms, p_names, p_action = inner_pattern p in
        let action (env_opt : NotationEnv.t option) (loc : Ast.location) =
          match env_opt with
          | Some env -> List.map Env.opt_binding_some env
          | None -> List.map Env.opt_binding_of_name p_names
        in
        [ Env (List.map Env.opt_declaration p_names),
          Gramext.srules
            [ [ Gramext.Sopt (Gramext.srules [ p_atoms, p_action ]) ],
              Gramext.action action ] ]
    | Ast.List0 (p, _)
    | Ast.List1 (p, _) ->
        let p_bindings, p_atoms, p_names, p_action = inner_pattern p in
        let action (env_list : NotationEnv.t list) (loc : Ast.location) =
          NotationEnv.coalesce_env p_names env_list
        in
        let gram_of_list s =
          match magic with
          | Ast.List0 (_, None) -> Gramext.Slist0 s
          | Ast.List1 (_, None) -> Gramext.Slist1 s
          | Ast.List0 (_, Some l) -> Gramext.Slist0sep (s, gram_of_literal l)
          | Ast.List1 (_, Some l) -> Gramext.Slist1sep (s, gram_of_literal l)
          | _ -> assert false
        in
        [ Env (List.map Env.list_declaration p_names),
          Gramext.srules
            [ [ gram_of_list (Gramext.srules [ p_atoms, p_action ]) ],
              Gramext.action action ] ]
    | _ -> assert false
  and aux_variable =
    function
    | Ast.NumVar s -> [Binding (s, Env.NumType), gram_number ""]
    | Ast.TermVar (s,(Ast.Self level|Ast.Level level as lv)) -> 
        [Binding (s, Env.TermType level), gram_term lv]
    | Ast.IdentVar s -> [Binding (s, Env.StringType), gram_ident ""]
    | Ast.Ascription (p, s) -> assert false (* TODO *)
    | Ast.FreshVar _ -> assert false
  and inner_pattern p =
    let p_bindings, p_atoms = List.split (aux p) in
    let p_names = flatten_opt p_bindings in
    let action =
      make_action (fun (env : NotationEnv.t) (loc : Ast.location) -> env)
        p_bindings
    in
    p_bindings, p_atoms, p_names, action
  in
  aux pattern

type rule_id = Grammar.token Gramext.g_symbol list

let compare_rule_id x y =
  let rec aux = function
    | [],[] -> 0
    | [],_ -> ~-1
    | _,[] -> 1
    | ((s1::tl1) as x),((s2::tl2) as y) ->
        if Gramext.eq_symbol s1 s2 then aux (tl1,tl2)
        else Pervasives.compare x y 
  in
    aux (x,y)

  (* mapping: rule_id -> owned keywords. (rule_id, string list) Hashtbl.t *)
let initial_owned_keywords () = Hashtbl.create 23
let owned_keywords = ref (initial_owned_keywords ())

type checked_l1_pattern = CL1P of NotationPt.term * int

let check_l1_pattern level1_pattern pponly level associativity =
  let variables = ref 0 in
  let symbols = ref 0 in
  let rec aux = function
    | Ast.AttributedTerm (att, t) -> Ast.AttributedTerm (att,aux t)
    | Ast.Literal _ as l -> incr symbols; l
    | Ast.Layout l -> Ast.Layout (aux_layout l)
    | Ast.Magic m -> Ast.Magic (aux_magic m)
    | Ast.Variable v -> (aux_variable v)
    | t -> assert false
  and aux_layout = function
    | Ast.Sub (p1, p2)   -> let p1 = aux p1 in let p2 = aux p2 in Ast.Sub (p1, p2)
    | Ast.Sup (p1, p2)   -> let p1 = aux p1 in let p2 = aux p2 in Ast.Sup (p1, p2)
    | Ast.Below (p1, p2) -> let p1 = aux p1 in let p2 = aux p2 in Ast.Below (p1, p2)
    | Ast.Above (p1, p2) -> let p1 = aux p1 in let p2 = aux p2 in Ast.Above (p1, p2)
    | Ast.Frac (p1, p2)  -> let p1 = aux p1 in let p2 = aux p2 in Ast.Frac (p1, p2)
    | Ast.InfRule (p1, p2, p3)  -> let p1 = aux p1 in let p2 = aux p2 in let p3 = aux p3 in Ast.InfRule (p1, p2, p3)
    | Ast.Atop (p1, p2)  -> let p1 = aux p1 in let p2 = aux p2 in Ast.Atop (p1, p2)
    | Ast.Over (p1, p2)  -> let p1 = aux p1 in let p2 = aux p2 in Ast.Over (p1, p2)
    | Ast.Root (p1, p2)  -> let p1 = aux p1 in let p2 = aux p2 in Ast.Root (p1, p2)
    | Ast.Sqrt p -> Ast.Sqrt (aux p)
    | Ast.Break as t -> t 
    | Ast.Box (b, pl) -> Ast.Box(b, List.map aux pl)
    | Ast.Group pl -> Ast.Group (List.map aux pl)
    | Ast.Mstyle (l,pl) -> Ast.Mstyle (l, List.map aux pl)
    | Ast.Mpadded (l,pl) -> Ast.Mpadded (l, List.map aux pl)
    | Ast.Maction l as t -> 
        if not pponly then 
        raise(Parse_error("Maction can be used only in output notations")) 
        else t
  and aux_magic magic =
    match magic with
    | Ast.Opt p -> Ast.Opt (aux p)
    | Ast.List0 (p, x) -> Ast.List0 (aux p, x)
    | Ast.List1 (p, x) -> Ast.List1 (aux p, x)
    | _ -> assert false
  and aux_variable =
    function
    | Ast.NumVar _ as t -> Ast.Variable t
    | Ast.TermVar (s,Ast.Self _) when associativity <> Gramext.NonA -> 
        incr variables; 
        if !variables > 2 then
          raise (Parse_error ("Exactly 2 variables must be specified in an "^
          "associative notation"));
        (match !variables, associativity with
        | 1,Gramext.LeftA -> 
             Ast.Variable (Ast.TermVar (s, Ast.Self level))
        | 1,Gramext.RightA -> 
             Ast.Variable (Ast.TermVar (s, Ast.Self (level+1)))
        | 2,Gramext.LeftA ->
             Ast.Variable (Ast.TermVar (s, Ast.Self (level+1)))
        | 2,Gramext.RightA -> 
             Ast.Variable (Ast.TermVar (s, Ast.Level (level-1)))
        | _ -> assert false)
    | Ast.TermVar (s,Ast.Level _) when associativity <> Gramext.NonA -> 
          raise (Parse_error ("Variables can not be declared with a " ^ 
            "precedence in an associative notation"))
       (*avoid camlp5 divergence due to non-Sself recursion at the same level *)
    | Ast.TermVar (s,Ast.Level l) when l<=level && !variables=0 && !symbols=0-> 
       raise(Parse_error("Left recursive rule with precedence not greater " ^
        "than " ^ string_of_int level ^ " is not allowed to avoid divergence"))
    | Ast.TermVar _ as t -> incr variables; Ast.Variable t
    | Ast.IdentVar _ as t -> Ast.Variable t
    | Ast.Ascription _ -> assert false (* TODO *)
    | Ast.FreshVar _ -> assert false
  in
  if associativity <> Gramext.NonA && level = min_precedence then
    raise (Parse_error ("You can not specify an associative notation " ^
    "at level "^string_of_int min_precedence ^ "; increase it"));
  let cp = aux level1_pattern in
(*   prerr_endline ("checked_pattern: " ^ NotationPp.pp_term cp); *)
  if !variables <> 2 && associativity <> Gramext.NonA then
    raise (Parse_error ("Exactly 2 variables must be specified in an "^
     "associative notation"));
  CL1P (cp,level)
;;

let extend (CL1P (level1_pattern,precedence)) action =
  let p_bindings, p_atoms =
    List.split (extract_term_production level1_pattern)
  in
  let level = level_of precedence in
  let _ =
    Grammar.extend
      [ Grammar.Entry.obj (!grammars.term: 'a Grammar.Entry.e),
        Some (Gramext.Level level),
        [ None,
          Some (*Gramext.NonA*) Gramext.NonA,
          [ p_atoms, 
            (make_action
              (fun (env: NotationEnv.t) (loc: Ast.location) ->
                (action env loc))
              p_bindings) ]]]
  in
  let keywords = NotationUtil.keywords_of_term level1_pattern in
  let rule_id = p_atoms in
  List.iter CicNotationLexer.add_level2_ast_keyword keywords;
  Hashtbl.add !owned_keywords rule_id keywords;  (* keywords may be [] *)
  rule_id

let delete rule_id =
  let atoms = rule_id in
  (try
    let keywords = Hashtbl.find !owned_keywords rule_id in
    List.iter CicNotationLexer.remove_level2_ast_keyword keywords
  with Not_found -> assert false);
  Grammar.delete_rule !grammars.term atoms

(** {2 Grammar} *)

let parse_level1_pattern_ref = ref (fun _ _ -> assert false)
let parse_level2_ast_ref = ref (fun _ -> assert false)
let parse_level2_meta_ref = ref (fun _ -> assert false)

let fold_cluster binder terms ty body =
  List.fold_right
    (fun term body -> Ast.Binder (binder, (term, ty), body))
    terms body  (* terms are names: either Ident or FreshVar *)

let fold_exists terms ty body =
  List.fold_right
    (fun term body ->
      let lambda = Ast.Binder (`Lambda, (term, ty), body) in
      Ast.Appl [ Ast.Symbol ("exists", 0); lambda ])
    terms body

let fold_binder binder pt_names body =
  List.fold_right
    (fun (names, ty) body -> fold_cluster binder names ty body)
    pt_names body

let return_term loc term = Ast.AttributedTerm (`Loc loc, term)
let return_term_of_level loc term l = 
  Ast.AttributedTerm (`Loc loc, term l)

  (* create empty precedence level for "term" *)
let initialize_grammars () =
  let dummy_action =
    Gramext.action (fun _ ->
      failwith "internal error, lexer generated a dummy token")
  in
  (* Needed since campl4 on "delete_rule" remove the precedence level if it gets
   * empty after the deletion. The lexer never generate the Stoken below. *)
  let dummy_prod = [ [ Gramext.Stoken ("DUMMY", "") ], dummy_action ] in
  let mk_level_list first last =
    let rec aux acc = function
      | i when i < first -> acc
      | i ->
          aux
            ((Some (level_of i), Some Gramext.NonA, dummy_prod)
             :: acc)
            (i - 1)
    in
    aux [] last
  in
  Grammar.extend
    [ Grammar.Entry.obj (!grammars.term: 'a Grammar.Entry.e),
      None,
      mk_level_list min_precedence max_precedence ];
(* {{{ Grammar for concrete syntax patterns, notation level 1 *)
  begin
  let level1_pattern = !grammars.level1_pattern in
EXTEND
  GLOBAL: level1_pattern;

  level1_pattern: [ 
    [ p = l1_pattern; EOI -> fun l -> NotationUtil.boxify (p l) ] 
  ];
  l1_pattern: [ 
    [ p = LIST1 l1_simple_pattern -> 
        fun l -> List.map (fun x -> x l) p ] 
  ];
  literal: [
    [ s = SYMBOL -> `Symbol s
    | k = QKEYWORD -> `Keyword k
    | n = NUMBER -> `Number n
    ]
  ];
  sep:       [ [ "sep";      sep = literal -> sep ] ];
  l1_magic_pattern: [
    [ "list0"; p = l1_simple_pattern; sep = OPT sep -> 
            fun l -> Ast.List0 (p l, sep)
    | "list1"; p = l1_simple_pattern; sep = OPT sep -> 
            fun l -> Ast.List1 (p l, sep)
    | "opt";   p = l1_simple_pattern -> fun l -> Ast.Opt (p l)
    ]
  ];
  l1_pattern_variable: [
    [ "term"; precedence = NUMBER; id = IDENT -> 
        Ast.TermVar (id, Ast.Level (int_of_string precedence))
    | "number"; id = IDENT -> Ast.NumVar id
    | "ident"; id = IDENT -> Ast.IdentVar id
    ]
  ];
  mstyle: [ 
    [ id = IDENT; 
      v = [ IDENT | NUMBER | COLOR | FLOATWITHUNIT ] -> id, v]];
  mpadded: [ 
    [ id = IDENT; 
      v = [ PERCENTAGE ] -> id, v]];
  l1_simple_pattern:
    [ "layout" LEFTA
      [ p1 = SELF; SYMBOL "\\sub "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Sub (p1 l, p2 l)))
      | p1 = SELF; SYMBOL "\\sup "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Sup (p1 l, p2 l)))
      | p1 = SELF; SYMBOL "\\below "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Below (p1 l, p2 l)))
      | p1 = SELF; SYMBOL "\\above "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Above (p1 l, p2 l)))
      | p1 = SELF; SYMBOL "\\over "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Over (p1 l, p2 l)))
      | p1 = SELF; SYMBOL "\\atop "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Atop (p1 l, p2 l)))
      | p1 = SELF; SYMBOL "\\frac "; p2 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Frac (p1 l, p2 l)))
      | SYMBOL "\\infrule "; p1 = SELF; p2 = SELF; p3 = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.InfRule (p1 l, p2 l, p3 l)))
      | SYMBOL "\\sqrt "; p = SELF -> 
          return_term_of_level loc (fun l -> Ast.Layout (Ast.Sqrt p l))
      | SYMBOL "\\root "; index = SELF; SYMBOL "\\of "; arg = SELF ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Root (arg l, index l)))
      | "hbox"; LPAREN; p = l1_pattern; RPAREN ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Box ((Ast.H, false, false), p l)))
      | "vbox"; LPAREN; p = l1_pattern; RPAREN ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Box ((Ast.V, false, false), p l)))
      | "hvbox"; LPAREN; p = l1_pattern; RPAREN ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Box ((Ast.HV, false, false), p l)))
      | "hovbox"; LPAREN; p = l1_pattern; RPAREN ->
          return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Box ((Ast.HOV, false, false), p l)))
      | "break" -> return_term_of_level loc (fun _ -> Ast.Layout Ast.Break)
      | "mstyle"; m = LIST1 mstyle ; LPAREN; t = l1_pattern; RPAREN ->
          return_term_of_level loc 
            (fun l -> 
               Ast.Layout (Ast.Mstyle (m, t l)))
      | "mpadded"; m = LIST1 mpadded ; LPAREN; t = l1_pattern; RPAREN ->
          return_term_of_level loc 
            (fun l -> 
               Ast.Layout (Ast.Mpadded (m, t l)))
      | "maction"; m = LIST1 [ LPAREN; l = l1_pattern; RPAREN -> l ] ->
           return_term_of_level loc 
            (fun l -> Ast.Layout (Ast.Maction (List.map (fun x ->
              NotationUtil.group (x l)) m)))
      | LPAREN; p = l1_pattern; RPAREN ->
          return_term_of_level loc (fun l -> NotationUtil.group (p l))
      ]
    | "simple" NONA
      [ i = IDENT -> 
         return_term_of_level loc 
           (fun l -> Ast.Variable (Ast.TermVar (i,Ast.Self l)))
      | m = l1_magic_pattern -> 
             return_term_of_level loc (fun l -> Ast.Magic (m l))
      | v = l1_pattern_variable -> 
             return_term_of_level loc (fun _ -> Ast.Variable v)
      | l = literal -> return_term_of_level loc (fun _ -> Ast.Literal l)
      ]
    ];
  END
  end;
(* }}} *)
(* {{{ Grammar for ast magics, notation level 2 *)
  begin
  let level2_meta = !grammars.level2_meta in
EXTEND
  GLOBAL: level2_meta;
  l2_variable: [
    [ "term"; precedence = NUMBER; id = IDENT -> 
        Ast.TermVar (id,Ast.Level (int_of_string precedence))
    | "number"; id = IDENT -> Ast.NumVar id
    | "ident"; id = IDENT -> Ast.IdentVar id
    | "fresh"; id = IDENT -> Ast.FreshVar id
    | "anonymous" -> Ast.TermVar ("_",Ast.Self 0) (* is the level relevant?*)
    | id = IDENT -> Ast.TermVar (id,Ast.Self 0)
    ]
  ];
  l2_magic: [
    [ "fold"; kind = [ "left" -> `Left | "right" -> `Right ];
      base = level2_meta; "rec"; id = IDENT; recursive = level2_meta ->
        Ast.Fold (kind, base, [id], recursive)
    | "default"; some = level2_meta; none = level2_meta ->
        Ast.Default (some, none)
    | "if"; p_test = level2_meta;
      "then"; p_true = level2_meta;
      "else"; p_false = level2_meta ->
        Ast.If (p_test, p_true, p_false)
    | "fail" -> Ast.Fail
    ]
  ];
  level2_meta: [
    [ magic = l2_magic -> Ast.Magic magic
    | var = l2_variable -> Ast.Variable var
    | blob = UNPARSED_AST ->
        !parse_level2_ast_ref (Ulexing.from_utf8_string blob)
    ]
  ];
END
  end;
(* }}} *)
(* {{{ Grammar for ast patterns, notation level 2 *)
  begin
  let level2_ast = !grammars.level2_ast in
  let term = !grammars.term in
  let let_defs = !grammars.let_defs in
  let protected_binder_vars = !grammars.protected_binder_vars in
EXTEND
  GLOBAL: level2_ast term let_defs protected_binder_vars;
  level2_ast: [ [ p = term -> p ] ];
  sort: [
    [ "Prop" -> `Prop
    | "Set" -> `Set
    | "Type"; SYMBOL "["; n = [ NUMBER| IDENT ]; SYMBOL "]" -> `NType n
    | "CProp"; SYMBOL "["; n = [ NUMBER| IDENT ]; SYMBOL "]" -> `NCProp n
    ]
  ];
  explicit_subst: [
    [ SYMBOL "\\subst ";  (* to avoid catching frequent "a [1]" cases *)
      SYMBOL "[";
      substs = LIST1 [
        i = IDENT; SYMBOL <:unicode<Assign>> (* ≔ *); t = term -> (i, t)
      ] SEP SYMBOL ";";
      SYMBOL "]" ->
        substs
    ]
  ];
  meta_subst: [
    [ s = SYMBOL "_" -> None
    | p = term -> Some p ]
  ];
  meta_substs: [
    [ SYMBOL "["; substs = LIST0 meta_subst; SYMBOL "]" -> substs ]
  ];
  possibly_typed_name: [
    [ LPAREN; id = single_arg; SYMBOL ":"; typ = term; RPAREN ->
        id, Some typ
    | arg = single_arg -> arg, None
    | id = PIDENT -> Ast.Ident (id, None), None
    | SYMBOL "_" -> Ast.Ident ("_", None), None
    | LPAREN; id = PIDENT; SYMBOL ":"; typ = term; RPAREN ->
        Ast.Ident (id, None), Some typ
    | LPAREN; SYMBOL "_"; SYMBOL ":"; typ = term; RPAREN ->
        Ast.Ident ("_", None), Some typ
    ]
  ];
  match_pattern: [
    [ SYMBOL "_" -> Ast.Wildcard
    | id = IDENT -> Ast.Pattern (id, None, [])
    | LPAREN; id = IDENT; vars = LIST1 possibly_typed_name; RPAREN ->
       Ast.Pattern (id, None, vars)
    | id = IDENT; vars = LIST1 possibly_typed_name ->
       Ast.Pattern (id, None, vars)
    ]
  ];
  binder: [
    [ SYMBOL <:unicode<Pi>>     (* Π *) -> `Pi
    | SYMBOL <:unicode<forall>> (* ∀ *) -> `Forall
    | SYMBOL <:unicode<lambda>> (* λ *) -> `Lambda
    ]
  ];
  arg: [
    [ LPAREN; names = LIST1 IDENT SEP SYMBOL ",";
      SYMBOL ":"; ty = term; RPAREN ->
        List.map (fun n -> Ast.Ident (n, None)) names, Some ty
    | name = IDENT -> [Ast.Ident (name, None)], None
    | blob = UNPARSED_META ->
        let meta = !parse_level2_meta_ref (Ulexing.from_utf8_string blob) in
        match meta with
        | Ast.Variable (Ast.FreshVar _) -> [meta], None
        | Ast.Variable (Ast.TermVar ("_",_)) -> [Ast.Ident ("_", None)], None
        | _ -> failwith "Invalid bound name."
   ]
  ];
  single_arg: [
    [ name = IDENT -> Ast.Ident (name, None)
    | blob = UNPARSED_META ->
        let meta = !parse_level2_meta_ref (Ulexing.from_utf8_string blob) in
        match meta with
        | Ast.Variable (Ast.FreshVar _)
        | Ast.Variable (Ast.IdentVar _) -> meta
        | Ast.Variable (Ast.TermVar ("_",_)) -> Ast.Ident ("_", None)
        | _ -> failwith "Invalid index name."
    ]
  ];
  let_defs: [
    [ defs = LIST1 [
        name = single_arg;
        args = LIST1 arg;
        index_name = OPT [ "on"; id = single_arg -> id ];
        ty = OPT [ SYMBOL ":" ; p = term -> p ];
        SYMBOL <:unicode<def>> (* ≝ *); body = term ->
          let rec position_of name p = function 
            | [] -> None, p
            | n :: _ when n = name -> Some p, p
            | _ :: tl -> position_of name (p + 1) tl
          in
          let rec find_arg name n = function 
            | [] ->
                Ast.fail loc (sprintf "Argument %s not found"
                  (NotationPp.pp_term name))
            | (l,_) :: tl -> 
                (match position_of name 0 l with
                | None, len -> find_arg name (n + len) tl
                | Some where, len -> n + where)
          in
          let index = 
            match index_name with 
            | None -> 0 
            | Some index_name -> find_arg index_name 0 args
          in
          let args =
           List.concat
            (List.map
             (function (names,ty) -> List.map (function x -> x,ty) names
             ) args)
          in
           args, (name, ty), body, index
      ] SEP "and" ->
        defs
    ]
  ];
  binder_vars: [
    [ vars = [ l =
        [ l = LIST1 single_arg SEP SYMBOL "," -> l
        | l = LIST1 [ PIDENT | SYMBOL "_" ] SEP SYMBOL "," -> 
            List.map (fun x -> Ast.Ident(x,None)) l
      ] -> l ];
      typ = OPT [ SYMBOL ":"; t = term -> t ] -> (vars, typ)
    ]
  ];
  protected_binder_vars: [
    [ LPAREN; vars = binder_vars; RPAREN -> vars 
    ]
  ];
  maybe_protected_binder_vars: [
    [ vars = binder_vars -> vars
    | vars = protected_binder_vars -> vars
    ]
  ];
  term: LEVEL "10"
  [
    [ "let"; 
     var = 
      [ LPAREN; id = single_arg; SYMBOL ":"; typ = term; RPAREN ->
	  id, Some typ
      | id = IDENT; ty = OPT [ SYMBOL ":"; typ = term -> typ] ->
	  Ast.Ident(id,None), ty ];
      SYMBOL <:unicode<def>> (* ≝ *);
      p1 = term; "in"; p2 = term ->
        return_term loc (Ast.LetIn (var, p1, p2))
    | LETCOREC; defs = let_defs; "in";
      body = term ->
        return_term loc (Ast.LetRec (`CoInductive, defs, body))
    | LETREC; defs = let_defs; "in";
      body = term ->
        return_term loc (Ast.LetRec (`Inductive, defs, body))
    ]
  ];
  term: LEVEL "20"
    [
      [ b = binder; (vars, typ) = maybe_protected_binder_vars; SYMBOL "."; body = term LEVEL "19" ->
          return_term loc (fold_cluster b vars typ body)
      ]
    ];
  term: LEVEL "70"
    [
      [ p1 = term; p2 = term LEVEL "71" ->
          let rec aux = function
            | Ast.Appl (hd :: tl)
            | Ast.AttributedTerm (_, Ast.Appl (hd :: tl)) ->
                aux hd @ tl
            | term -> [term]
          in
          return_term loc (Ast.Appl (aux p1 @ [p2]))
      ]
    ];
  term: LEVEL "90"
    [
      [ id = IDENT -> return_term loc (Ast.Ident (id, None))
      | id = IDENT; s = explicit_subst ->
          return_term loc (Ast.Ident (id, Some s))
      | s = CSYMBOL -> return_term loc (Ast.Symbol (s, 0))
      | u = URI -> return_term loc (Ast.Uri (u, None))
      | r = NREF -> return_term loc (Ast.NRef (NReference.reference_of_string r))
      | n = NUMBER -> return_term loc (Ast.Num (n, 0))
      | IMPLICIT -> return_term loc (Ast.Implicit `JustOne)
      | SYMBOL <:unicode<ldots>> -> return_term loc (Ast.Implicit `Vector)
      | PLACEHOLDER -> return_term loc Ast.UserInput
      | m = META -> return_term loc (Ast.Meta (int_of_string m, []))
      | m = META; s = meta_substs ->
          return_term loc (Ast.Meta (int_of_string m, s))
      | s = sort -> return_term loc (Ast.Sort s)
      | "match"; t = term;
        indty_ident = OPT [ "in"; id = IDENT -> id, None ];
        outtyp = OPT [ "return"; ty = term -> ty ];
        "with"; SYMBOL "[";
        patterns = LIST0 [
          lhs = match_pattern; SYMBOL <:unicode<Rightarrow>> (* ⇒ *);
          rhs = term ->
            lhs, rhs
        ] SEP SYMBOL "|";
        SYMBOL "]" ->
          return_term loc (Ast.Case (t, indty_ident, outtyp, patterns))
      | LPAREN; p1 = term; SYMBOL ":"; p2 = term; RPAREN ->
          return_term loc (Ast.Cast (p1, p2))
      | LPAREN; p = term; RPAREN -> p
      | blob = UNPARSED_META ->
          !parse_level2_meta_ref (Ulexing.from_utf8_string blob)
      ]
    ];
END
  end
(* }}} *)
;;

let _ = initialize_grammars ();;

let history = ref [];;

let push () =
  CicNotationLexer.push ();
  history := (!owned_keywords,!grammars) :: !history;
  owned_keywords := (initial_owned_keywords ());
  grammars := initial_grammars ();
  initialize_grammars ()
;;

let pop () =
  CicNotationLexer.pop ();
  match !history with
  | [] -> assert false
  | (kw,gram) :: old_history ->
      owned_keywords := kw;
      grammars := gram;
      history := old_history
;;

(** {2 API implementation} *)

let exc_located_wrapper f =
  try
    f ()
  with
  | Stdpp.Exc_located (floc, Stream.Error msg) ->
      raise (HExtlib.Localized (floc, Parse_error msg))
  | Stdpp.Exc_located (floc, HExtlib.Localized (_,exn)) ->
      raise (HExtlib.Localized (floc, (Parse_error (Printexc.to_string exn))))
  | Stdpp.Exc_located (floc, exn) ->
      raise (HExtlib.Localized (floc, (Parse_error (Printexc.to_string exn))))

let parse_level1_pattern precedence lexbuf =
  exc_located_wrapper
    (fun () -> Grammar.Entry.parse !grammars.level1_pattern (Obj.magic lexbuf) precedence)

let parse_level2_ast lexbuf =
  exc_located_wrapper
    (fun () -> Grammar.Entry.parse !grammars.level2_ast (Obj.magic lexbuf))

let parse_level2_meta lexbuf =
  exc_located_wrapper
    (fun () -> Grammar.Entry.parse !grammars.level2_meta (Obj.magic lexbuf))

let _ =
  parse_level1_pattern_ref := parse_level1_pattern;
  parse_level2_ast_ref := parse_level2_ast;
  parse_level2_meta_ref := parse_level2_meta

let parse_term lexbuf =
  exc_located_wrapper
    (fun () -> (Grammar.Entry.parse !grammars.term (Obj.magic lexbuf)))

let level2_ast_grammar () = !grammars.level2_ast_grammar
let term  () = !grammars.term
let let_defs  () = !grammars.let_defs
let protected_binder_vars  () = !grammars.protected_binder_vars


(** {2 Debugging} *)

let print_l2_pattern () =
  Grammar.print_entry Format.std_formatter (Grammar.Entry.obj !grammars.term);
  Format.pp_print_flush Format.std_formatter ();
  flush stdout  

(* vim:set encoding=utf8 foldmethod=marker: *)