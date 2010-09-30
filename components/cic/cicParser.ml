(* Copyright (C) 2004-2005, HELM Team.
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

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

open Printf

(* ZACK TODO element from the DTD still to be handled:
   <!ELEMENT CurrentProof (Conjecture*,body)>
   <!ELEMENT Sequent %sequent;>
   <!ELEMENT Conjecture %sequent;>
   <!ELEMENT Decl %term;>
   <!ELEMENT Def %term;>
   <!ELEMENT Hidden EMPTY>
   <!ELEMENT Goal %term;>
*)

exception Getter_failure of string * string
exception Parser_failure of string

type stack_entry =
  | Arg of string * Cic.annterm (* relative uri, term *)
  (* constants' body and types resides in differne files, thus we can't simple
   * keep constants in Cic_obj stack entries *)
  | Cic_attributes of Cic.attribute list
  | Cic_constant_body of string * string * UriManager.uri list * Cic.annterm
      * Cic.attribute list
      (* id, for, params, body, object attributes *)
  | Cic_constant_type of string * string * UriManager.uri list * Cic.annterm
      * Cic.attribute list
      (* id, name, params, type, object attributes *)
  | Cic_term of Cic.annterm (* term *)
  | Cic_obj of Cic.annobj   (* object *)
  | Cofix_fun of Cic.id * string * Cic.annterm * Cic.annterm
      (* id, name, type, body *)
  | Constructor of string * Cic.annterm   (* name, type *)
  | Decl of Cic.id * Cic.name * Cic.annterm (* id, binder, source *)
  | Def of Cic.id * Cic.name * Cic.annterm * Cic.annterm  (* id, binder, source, type *)
  | Fix_fun of Cic.id * string * int * Cic.annterm * Cic.annterm
      (* id, name, ind. index, type, body *)
  | Inductive_type of string * string * bool * Cic.annterm *
      (string * Cic.annterm) list (* id, name, inductive, arity, constructors *)
  | Meta_subst of Cic.annterm option
  | Obj_class of Cic.object_class
  | Obj_flavour of Cic.object_flavour
  | Obj_field of string (* field name *)
  | Obj_generated
  | Tag of string * (string * string) list  (* tag name, attributes *)
      (* ZACK TODO add file position to tag stack entry so that when attribute
       * errors occur, the position of their _start_tag_ could be printed
       * instead of the current position (usually the end tag) *)

type ctxt = {
  mutable stack: stack_entry list;
  mutable xml_parser: XmlPushParser.xml_parser option;
  mutable filename: string;
  uri: UriManager.uri;
}

let string_of_stack ctxt =
  "[" ^ (String.concat "; "
    (List.map
      (function
      | Arg (reluri, _) -> sprintf "Arg %s" reluri
      | Cic_attributes _ -> "Cic_attributes"
      | Cic_constant_body (id, name, _, _, _) ->
          sprintf "Cic_constant_body %s (id=%s)" name id
      | Cic_constant_type (id, name, _, _, _) ->
          sprintf "Cic_constant_type %s (id=%s)" name id
      | Cic_term _ -> "Cic_term"
      | Cic_obj _ -> "Cic_obj"
      | Constructor (name, _) -> "Constructor " ^ name
      | Cofix_fun (id, _, _, _) -> sprintf "Cofix_fun (id=%s)" id
      | Decl (id, _, _) -> sprintf "Decl (id=%s)" id
      | Def (id, _, _, _) -> sprintf "Def (id=%s)" id
      | Fix_fun (id, _, _, _, _) -> sprintf "Fix_fun (id=%s)" id
      | Inductive_type (id, name, _, _, _) ->
          sprintf "Inductive_type %s (id=%s)" name id
      | Meta_subst _ -> "Meta_subst"
      | Obj_class _ -> "Obj_class"
      | Obj_flavour _ -> "Obj_flavour"
      | Obj_field name -> "Obj_field " ^ name
      | Obj_generated -> "Obj_generated"
      | Tag (tag, _) -> "Tag " ^ tag)
      ctxt.stack)) ^ "]"

let compare_attrs (a1, v1) (a2, v2) = Pervasives.compare a1 a2
let sort_attrs = List.sort compare_attrs

let new_parser_context uri = {
  stack = [];
  xml_parser = None;
  filename = "-";
  uri = uri;
}

let get_parser ctxt =
  match ctxt.xml_parser with
  | Some p -> p
  | None -> assert false

(** {2 Error handling} *)

let parse_error ctxt msg =
  let (line, col) = XmlPushParser.get_position (get_parser ctxt) in
  raise (Parser_failure (sprintf "[%s: line %d, column %d] %s"
    ctxt.filename line col msg))

let attribute_error ctxt tag =
  parse_error ctxt ("wrong attribute set for " ^ tag)

(** {2 Parsing context management} *)

let pop ctxt =
(*  debug_print (lazy "pop");*)
  match ctxt.stack with
  | hd :: tl -> (ctxt.stack <- tl)
  | _ -> assert false

let push ctxt v =
(*  debug_print (lazy "push");*)
  ctxt.stack <- v :: ctxt.stack

let set_top ctxt v =
(*  debug_print (lazy "set_top");*)
  match ctxt.stack with
  | _ :: tl -> (ctxt.stack <- v :: tl)
  | _ -> assert false

  (** pop the last tag from the open tags stack returning a pair <tag_name,
   * attribute_list> *)
let pop_tag ctxt =
  match ctxt.stack with
  | Tag (tag, attrs) :: tl ->
      ctxt.stack <- tl;
      (tag, attrs)
  | _ -> parse_error ctxt "unexpected extra content"

  (** pop the last tag from the open tags stack returning its attributes.
   * Attributes are returned as a list of pair <name, value> _sorted_ by
   * attribute name *)
let pop_tag_attrs ctxt = sort_attrs (snd (pop_tag ctxt))

let pop_cics ctxt =
  let rec aux acc stack =
    match stack with
    | Cic_term t :: tl -> aux (t :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  ctxt.stack <- new_stack;
  values

let pop_class_modifiers ctxt =
  let rec aux acc stack =
    match stack with
    | (Cic_term (Cic.ASort _) as m) :: tl
    | (Obj_field _ as m) :: tl ->
        aux (m :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  ctxt.stack <- new_stack;
  values

let pop_meta_substs ctxt =
  let rec aux acc stack =
    match stack with
    | Meta_subst t :: tl -> aux (t :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  ctxt.stack <- new_stack;
  values

let pop_fix_funs ctxt =
  let rec aux acc stack =
    match stack with
    | Fix_fun (id, name, index, typ, body) :: tl ->
        aux ((id, name, index, typ, body) :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  ctxt.stack <- new_stack;
  values

let pop_cofix_funs ctxt =
  let rec aux acc stack =
    match stack with
    | Cofix_fun (id, name, typ, body) :: tl ->
        aux ((id, name, typ, body) :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  ctxt.stack <- new_stack;
  values

let pop_constructors ctxt =
  let rec aux acc stack =
    match stack with
    | Constructor (name, t) :: tl -> aux ((name, t) :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  ctxt.stack <- new_stack;
  values

let pop_inductive_types ctxt =
  let rec aux acc stack =
    match stack with
    | Inductive_type (id, name, ind, arity, ctors) :: tl ->
        aux ((id, name, ind, arity, ctors) :: acc) tl
    | tl -> acc, tl
  in
  let values, new_stack = aux [] ctxt.stack in
  if values = [] then
    parse_error ctxt "no \"InductiveType\" element found";
  ctxt.stack <- new_stack;
  values

  (** travels the stack (without popping) for the first term subject of explicit
   * named substitution and return its URI *)
let find_base_uri ctxt =
  let rec aux = function
    | Cic_term (Cic.AConst (_, uri, _)) :: _
    | Cic_term (Cic.AMutInd (_, uri, _, _)) :: _
    | Cic_term (Cic.AMutConstruct (_, uri, _, _, _)) :: _
    | Cic_term (Cic.AVar (_, uri, _)) :: _ ->
        uri
    | Arg _ :: tl -> aux tl
    | _ -> parse_error ctxt "no \"arg\" element found"
  in
  UriManager.buri_of_uri (aux ctxt.stack)

  (** backwardly eats the stack building an explicit named substitution from Arg
   * stack entries *)
let pop_subst ctxt base_uri =
  let rec aux acc stack =
    match stack with
    | Arg (rel_uri, term) :: tl ->
        let uri = UriManager.uri_of_string (base_uri ^ "/" ^ rel_uri) in
        aux ((uri, term) :: acc) tl
    | tl -> acc, tl
  in
  let subst, new_stack = aux [] ctxt.stack in
  if subst = [] then
    parse_error ctxt "no \"arg\" element found";
  ctxt.stack <- new_stack;
  subst

let pop_cic ctxt =
  match ctxt.stack with
  | Cic_term t :: tl ->
      ctxt.stack <- tl;
      t
  | _ -> parse_error ctxt "no cic term found"

let pop_obj_attributes ctxt =
  match ctxt.stack with
  | Cic_attributes attributes :: tl ->
      ctxt.stack <- tl;
      attributes
  | _ -> []

(** {2 Auxiliary functions} *)

let uri_of_string = UriManager.uri_of_string

let uri_list_of_string =
  let space_RE = Str.regexp " " in
  fun s ->
    List.map uri_of_string (Str.split space_RE s)

let impredicative_set = ref true;;

let sort_of_string ctxt = function
  | "Prop" -> Cic.Prop
  (* THIS CASE IS HERE ONLY TO ALLOW THE PARSING OF COQ LIBRARY
   * THIS SHOULD BE REMOVED AS SOON AS univ_maker OR COQ'S EXPORTATION 
   * IS FIXED *)
  | "CProp" -> Cic.CProp (CicUniv.fresh ~uri:ctxt.uri ())
  | "Type" ->  Cic.Type (CicUniv.fresh ~uri:ctxt.uri ())
  | "Set" when !impredicative_set -> Cic.Set
  | "Set" -> Cic.Type (CicUniv.fresh ~uri:ctxt.uri ())
  | s ->
      let len = String.length s in
      let sort_len, mk_sort = 
        if len > 5 && String.sub s 0 5 = "Type:" then 5,fun x -> Cic.Type x 
        else if len > 6 && String.sub s 0 6 = "CProp:" then 6,fun x->Cic.CProp x
        else parse_error ctxt "sort expected"
      in
      let s = String.sub s sort_len (len - sort_len) in
      let i = String.index s ':' in  
      let id =  int_of_string (String.sub s 0 i) in
      let suri = String.sub s (i+1) (len - sort_len - i - 1) in
      let uri = UriManager.uri_of_string suri in
      try mk_sort (CicUniv.fresh ~uri ~id ())
      with
      | Failure "int_of_string" 
      | Invalid_argument _ -> parse_error ctxt "sort expected" 

let patch_subst ctxt subst = function
  | Cic.AConst (id, uri, _) -> Cic.AConst (id, uri, subst)
  | Cic.AMutInd (id, uri, typeno, _) ->
      Cic.AMutInd (id, uri, typeno, subst)
  | Cic.AMutConstruct (id, uri, typeno, consno, _) ->
      Cic.AMutConstruct (id, uri, typeno, consno, subst)
  | Cic.AVar (id, uri, _) -> Cic.AVar (id, uri, subst)
  | _ ->
      parse_error ctxt
        ("only \"CONST\", \"VAR\", \"MUTIND\", and \"MUTCONSTRUCT\" can be" ^
        " instantiated")

  (** backwardly eats the stack seeking for the first open tag carrying
   * "helm:exception" attributes. If found return Some of a pair containing
   * exception name and argument. Return None otherwise *)
let find_helm_exception ctxt =
  let rec aux = function
    | [] -> None
    | Tag (_, attrs) :: tl ->
        (try
          let exn = List.assoc "helm:exception" attrs in
          let arg =
            try List.assoc "helm:exception_arg" attrs with Not_found -> ""
          in
          Some (exn, arg)
        with Not_found -> aux tl)
    | _ :: tl -> aux tl
  in
  aux ctxt.stack

(** {2 Push parser callbacks}
 * each callback needs to be instantiated to a parsing context *)

let start_element ctxt tag attrs =
(*  debug_print (lazy (sprintf "<%s%s>" tag (match attrs with | [] -> "" | _ -> " " ^ String.concat " " (List.map (fun (a,v) -> sprintf "%s=\"%s\"" a v) attrs))));*)
  push ctxt (Tag (tag, attrs))

let end_element ctxt tag =
(*  debug_print (lazy (sprintf "</%s>" tag));*)
(*  debug_print (lazy (string_of_stack ctxt));*)
  let attribute_error () = attribute_error ctxt tag in
  let parse_error = parse_error ctxt in
  let sort_of_string = sort_of_string ctxt in
  match tag with
  | "REL" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["binder", binder; "id", id; "idref", idref; "value", value]
        | ["binder", binder; "id", id; "idref", idref; "sort", _;
           "value", value] ->
            Cic.ARel (id, idref, int_of_string value, binder)
        | _ -> attribute_error ()))
  | "VAR" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "uri", uri]
        | ["id", id; "sort", _; "uri", uri] ->
            Cic.AVar (id, uri_of_string uri, [])
        | _ -> attribute_error ()))
  | "CONST" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "uri", uri]
        | ["id", id; "sort", _; "uri", uri] ->
            Cic.AConst (id, uri_of_string uri, [])
        | _ -> attribute_error ()))
  | "SORT" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "value", sort] -> Cic.ASort (id, sort_of_string sort)
        | _ -> attribute_error ()))
  | "APPLY" ->
      let args = pop_cics ctxt in
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id ]
        | ["id", id; "sort", _] -> Cic.AAppl (id, args)
        | _ -> attribute_error ()))
  | "decl" ->
      let source = pop_cic ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["binder", binder; "id", id ]
        | ["binder", binder; "id", id; "type", _] ->
            Decl (id, Cic.Name binder, source)
        | ["id", id]
        | ["id", id; "type", _] -> Decl (id, Cic.Anonymous, source)
        | _ -> attribute_error ())
  | "def" ->  (* same as "decl" above *)
      let ty,source =
       (*CSC: hack to parse Coq files where the LetIn is not typed *)
       let ty = pop_cic ctxt in
       try
        let source = pop_cic ctxt in
         ty,source
       with
        Parser_failure _ -> Cic.AImplicit ("MISSING_def_TYPE",None),ty
      in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["binder", binder; "id", id]
        | ["binder", binder; "id", id; "sort", _] ->
            Def (id, Cic.Name binder, source, ty)
        | ["id", id]
        | ["id", id; "sort", _] -> Def (id, Cic.Anonymous, source, ty)
        | _ -> attribute_error ())
  | "arity"           (* transparent elements (i.e. which contain a CIC) *)
  | "body"
  | "inductiveTerm"
  | "pattern"
  | "patternsType"
  | "target"
  | "term"
  | "type" ->
      let term = pop_cic ctxt in
      pop ctxt; (* pops start tag matching current end tag (e.g. <arity>) *)
      push ctxt (Cic_term term)
  | "substitution" ->   (* optional transparent elements (i.e. which _may_
                         * contain a CIC) *)
      set_top ctxt  (* replace <substitution> *)
        (match ctxt.stack with
        | Cic_term term :: tl ->
            ctxt.stack <- tl;
            (Meta_subst (Some term))
        | _ ->  Meta_subst None)
  | "PROD" ->
      let target = pop_cic ctxt in
      let rec add_decl target = function
        | Decl (id, binder, source) :: tl ->
            add_decl (Cic.AProd (id, binder, source, target)) tl
        | tl ->
            ctxt.stack <- tl;
            target
      in
      let term = add_decl target ctxt.stack in
      (match pop_tag_attrs ctxt with
        []
      | ["type", _] -> ()
      | _ -> attribute_error ());
      push ctxt (Cic_term term)
  | "LAMBDA" ->
      let target = pop_cic ctxt in
      let rec add_decl target = function
        | Decl (id, binder, source) :: tl ->
            add_decl (Cic.ALambda (id, binder, source, target)) tl
        | tl ->
            ctxt.stack <- tl;
            target
      in
      let term = add_decl target ctxt.stack in
      (match pop_tag_attrs ctxt with
        []
      | ["sort", _] -> ()
      | _ -> attribute_error ());
      push ctxt (Cic_term term)
  | "LETIN" ->
      let target = pop_cic ctxt in
      let rec add_def target = function
        | Def (id, binder, source, ty) :: tl ->
            add_def (Cic.ALetIn (id, binder, source, ty, target)) tl
        | tl ->
            ctxt.stack <- tl;
            target
      in
      let term = add_def target ctxt.stack in
      (match pop_tag_attrs ctxt with
        []
      | ["sort", _] -> ()
      | _ -> attribute_error ());
      push ctxt (Cic_term term)
  | "CAST" ->
      let typ = pop_cic ctxt in
      let term = pop_cic ctxt in
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
          ["id", id]
        | ["id", id; "sort", _] -> Cic.ACast (id, term, typ)
        | _ -> attribute_error ()));
  | "IMPLICIT" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id] -> Cic.AImplicit (id, None)
        | ["annotation", annotation; "id", id] ->
            let implicit_annotation =
              match annotation with
              | "closed" -> `Closed
              | "hole" -> `Hole
              | "type" -> `Type
              | _ -> parse_error "invalid value for \"annotation\" attribute"
            in
            Cic.AImplicit (id, Some implicit_annotation)
        | _ -> attribute_error ()))
  | "META" ->
      let meta_substs = pop_meta_substs ctxt in
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "no", no]
        | ["id", id; "no", no; "sort", _] ->
            Cic.AMeta (id, int_of_string no, meta_substs)
        | _ -> attribute_error ()));
  | "MUTIND" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "noType", noType; "uri", uri] ->
            Cic.AMutInd (id, uri_of_string uri, int_of_string noType, [])
        | _ -> attribute_error ()));
  | "MUTCONSTRUCT" ->
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "noConstr", noConstr; "noType", noType; "uri", uri]
        | ["id", id; "noConstr", noConstr; "noType", noType; "sort", _;
           "uri", uri] ->
            Cic.AMutConstruct (id, uri_of_string uri, int_of_string noType,
              int_of_string noConstr, [])
        | _ -> attribute_error ()));
  | "FixFunction" ->
      let body = pop_cic ctxt in
      let typ = pop_cic ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["id", id; "name", name; "recIndex", recIndex] ->
            Fix_fun (id, name, int_of_string recIndex, typ, body)
        | _ -> attribute_error ())
  | "CofixFunction" ->
      let body = pop_cic ctxt in
      let typ = pop_cic ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["id", id; "name", name] ->
            Cofix_fun (id, name, typ, body)
        | _ -> attribute_error ())
  | "FIX" ->
      let fix_funs = pop_fix_funs ctxt in
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "noFun", noFun]
        | ["id", id; "noFun", noFun; "sort", _] ->
            Cic.AFix (id, int_of_string noFun, fix_funs)
        | _ -> attribute_error ()))
  | "COFIX" ->
      let cofix_funs = pop_cofix_funs ctxt in
      push ctxt (Cic_term
        (match pop_tag_attrs ctxt with
        | ["id", id; "noFun", noFun]
        | ["id", id; "noFun", noFun; "sort", _] ->
            Cic.ACoFix (id, int_of_string noFun, cofix_funs)
        | _ -> attribute_error ()))
  | "MUTCASE" ->
      (match pop_cics ctxt with
      | patternsType :: inductiveTerm :: patterns ->
          push ctxt (Cic_term
            (match pop_tag_attrs ctxt with
            | ["id", id; "noType", noType; "uriType", uriType]
            | ["id", id; "noType", noType; "sort", _; "uriType", uriType] ->
                Cic.AMutCase (id, uri_of_string uriType, int_of_string noType,
                  patternsType, inductiveTerm, patterns)
            | _ -> attribute_error ()))
      | _ -> parse_error "invalid \"MUTCASE\" content")
  | "Constructor" ->
      let typ = pop_cic ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["name", name] -> Constructor (name, typ)
        | _ -> attribute_error ())
  | "InductiveType" ->
      let constructors = pop_constructors ctxt in
      let arity = pop_cic ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["id", id; "inductive", inductive; "name", name] ->
            Inductive_type (id, name, bool_of_string inductive, arity,
              constructors)
        | _ -> attribute_error ())
  | "InductiveDefinition" ->
      let inductive_types = pop_inductive_types ctxt in
      let obj_attributes = pop_obj_attributes ctxt in
      push ctxt (Cic_obj
        (match pop_tag_attrs ctxt with
        | ["id", id; "noParams", noParams; "params", params] ->
            Cic.AInductiveDefinition (id, inductive_types,
              uri_list_of_string params, int_of_string noParams, obj_attributes)
        | _ -> attribute_error ()))
  | "ConstantType" ->
      let typ = pop_cic ctxt in
      let obj_attributes = pop_obj_attributes ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["id", id; "name", name; "params", params] ->
            Cic_constant_type (id, name, uri_list_of_string params, typ,
              obj_attributes)
        | _ -> attribute_error ())
  | "ConstantBody" ->
      let body = pop_cic ctxt in
      let obj_attributes = pop_obj_attributes ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["for", for_; "id", id; "params", params] ->
            Cic_constant_body (id, for_, uri_list_of_string params, body,
              obj_attributes)
        | _ -> attribute_error ())
  | "Variable" ->
      let typ = pop_cic ctxt in
      let body =
        match pop_cics ctxt with
        | [] -> None
        | [t] -> Some t
        | _ -> parse_error "wrong content for \"Variable\""
      in
      let obj_attributes = pop_obj_attributes ctxt in
      push ctxt (Cic_obj
        (match pop_tag_attrs ctxt with
        | ["id", id; "name", name; "params", params] ->
            Cic.AVariable (id, name, body, typ, uri_list_of_string params,
              obj_attributes)
        | _ -> attribute_error ()))
  | "arg" ->
      let term = pop_cic ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["relUri", relUri] -> Arg (relUri, term)
        | _ -> attribute_error ())
  | "instantiate" ->
        (* explicit named substitution handling: when the end tag of an element
         * subject of exlicit named subst (MUTIND, MUTCONSTRUCT, CONST, VAR) it
         * is stored on the stack with no substitutions (i.e. []). When the end
         * tag of an "instantiate" element is found we patch the term currently
         * on the stack with the substitution built from "instantiate" children
         *)
        (* XXX inefficiency here: first travels the <arg> elements in order to
         * find the baseUri, then in order to build the explicit named subst *)
      let base_uri = find_base_uri ctxt in
      let subst = pop_subst ctxt base_uri in
      let term = pop_cic ctxt in
        (* comment from CicParser3.ml:
         * CSC: the "id" optional attribute should be parsed and reflected in
         *      Cic.annterm and id = string_of_xml_attr (n#attribute "id") *)
        (* replace <instantiate> *)
      set_top ctxt (Cic_term (patch_subst ctxt subst term))
  | "attributes" ->
      let rec aux acc = function  (* retrieve object attributes *)
        | Obj_class c :: tl -> aux (`Class c :: acc) tl
        | Obj_flavour f :: tl -> aux (`Flavour f :: acc) tl
        | Obj_generated :: tl -> aux (`Generated :: acc) tl
        | tl -> acc, tl
      in
      let obj_attrs, new_stack = aux [] ctxt.stack in
      ctxt.stack <- new_stack;
      set_top ctxt (Cic_attributes obj_attrs)
  | "generated" -> set_top ctxt Obj_generated
  | "field" ->
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["name", name] -> Obj_field name
        | _ -> attribute_error ())
  | "flavour" ->
      push ctxt 
        (match pop_tag_attrs ctxt with
        | [ "value", "definition"] -> Obj_flavour `Definition
        | [ "value", "mutual_definition"] -> Obj_flavour `MutualDefinition
        | [ "value", "fact"] -> Obj_flavour `Fact
        | [ "value", "lemma"] -> Obj_flavour `Lemma
        | [ "value", "remark"] -> Obj_flavour `Remark
        | [ "value", "theorem"] -> Obj_flavour `Theorem
        | [ "value", "variant"] -> Obj_flavour `Variant
        | [ "value", "axiom"] -> Obj_flavour `Axiom
        | _ -> attribute_error ())
  | "class" ->
      let class_modifiers = pop_class_modifiers ctxt in
      push ctxt
        (match pop_tag_attrs ctxt with
        | ["value", "elim"] ->
            (match class_modifiers with
            | [Cic_term (Cic.ASort (_, sort))] -> Obj_class (`Elim sort)
            | _ ->
                parse_error
                  "unexpected extra content for \"elim\" object class")
        | ["value", "record"] ->
            let fields =
              List.map
                (function
                  | Obj_field name -> 
                      (match Str.split (Str.regexp " ") name with
                      | [name] -> name, false, 0
                      | [name;"coercion"] -> name,true,0
                      | [name;"coercion"; n] -> 
                          let n = 
                            try int_of_string n 
                            with Failure _ -> 
                              parse_error "int expected after \"coercion\""
                          in
                          name,true,n
                      | _ -> 
                          parse_error
                            "wrong \"field\"'s name attribute")
                  | _ ->
                      parse_error
                        "unexpected extra content for \"record\" object class")
                class_modifiers
            in
            Obj_class (`Record fields)
        | ["value", "projection"] -> Obj_class `Projection
        | ["value", "inversion"] -> Obj_class `InversionPrinciple
	| _ -> attribute_error ())
  | tag ->
      match find_helm_exception ctxt with
      | Some (exn, arg) -> raise (Getter_failure (exn, arg))
      | None -> parse_error (sprintf "unknown element \"%s\"" tag)

(** {2 Parser internals} *)

let has_gz_suffix fname =
  try
    let idx = String.rindex fname '.' in
    let suffix = String.sub fname idx (String.length fname - idx) in
    suffix = ".gz"
  with Not_found -> false

let parse uri filename =
  let ctxt = new_parser_context uri in
  ctxt.filename <- filename;
  let module P = XmlPushParser in
  let callbacks = {
    P.default_callbacks with
      P.start_element = Some (start_element ctxt);
      P.end_element = Some (end_element ctxt);
  } in
  let xml_parser = P.create_parser callbacks in
  ctxt.xml_parser <- Some xml_parser;
  try
    (try
      let xml_source =
        if has_gz_suffix filename then `Gzip_file filename
        else `File filename
      in
      P.parse xml_parser xml_source
    with exn ->
      ctxt.xml_parser <- None;
      (* ZACK: the above "<- None" is vital for garbage collection. Without it
       * we keep in memory a circular structure parser -> callbacks -> ctxt ->
       * parser. I don't know if the ocaml garbage collector is supposed to
       * collect such structures, but for sure the expat bindings will (orribly)
       * leak when used in conjunction with such structures *)
      raise exn);
    ctxt.xml_parser <- None; (* ZACK: same comment as above *)
(*    debug_print (lazy (string_of_stack stack));*)
    (* assert (List.length ctxt.stack = 1) *)
    List.hd ctxt.stack
  with
  | Failure "int_of_string" -> parse_error ctxt "integer number expected"
  | Invalid_argument "bool_of_string" -> parse_error ctxt "boolean expected"
  | P.Parse_error msg -> parse_error ctxt ("parse error: " ^ msg)
  | Sys.Break
  | Parser_failure _
  | Getter_failure _ as exn ->
      raise exn
  | exn ->
      raise (Parser_failure ("CicParser: uncaught exception: " ^ Printexc.to_string exn))

(** {2 API implementation} *)

let annobj_of_xml uri filename filenamebody =
  match filenamebody with
  | None ->
      (match parse uri filename with
      | Cic_constant_type (id, name, params, typ, obj_attributes) ->
          Cic.AConstant (id, None, name, None, typ, params, obj_attributes)
      | Cic_obj obj -> obj
      | _ -> raise (Parser_failure ("no object found in " ^ filename)))
  | Some filenamebody ->
      (match parse uri filename, parse uri filenamebody with
      | Cic_constant_type (type_id, name, params, typ, obj_attributes),
        Cic_constant_body (body_id, _, _, body, _) ->
          Cic.AConstant (type_id, Some body_id, name, Some body, typ, params,obj_attributes)
      | _ ->
          raise (Parser_failure (sprintf "no constant found in %s, %s"
            filename filenamebody)))

let obj_of_xml uri filename filenamebody =
 Deannotate.deannotate_obj (annobj_of_xml uri filename filenamebody)
