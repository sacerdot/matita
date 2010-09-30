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

(* $Id$ *)

let document_of_xml (domImplementation : Gdome.domImplementation) strm =
 let module G = Gdome in
 let module X = Xml in
  let rec update_namespaces ((defaultns,bindings) as namespaces) =
   function
      [] -> namespaces
    | (None,"xmlns",value)::tl ->
       update_namespaces (Some (Gdome.domString value),bindings) tl
    | (prefix,name,value)::tl when prefix = Some "xmlns"  ->
        update_namespaces (defaultns,(name,Gdome.domString value)::bindings) tl
    | _::tl -> update_namespaces namespaces tl in
  let rec namespace_of_prefix (defaultns,bindings) =
   function
      None -> None
    | Some "xmlns" -> Some (Gdome.domString "xml-ns")
    | Some p' ->
       try
        Some (List.assoc p' bindings)
       with
        Not_found ->
         raise
          (Failure ("The prefix " ^ p' ^ " is not bound to any namespace")) in
  let get_qualified_name p n =
   match p with
      None -> Gdome.domString n
    | Some p' -> Gdome.domString (p' ^ ":" ^ n) in
  let root_prefix,root_name,root_attributes,root_content =
   ignore (Stream.next strm) ; (* to skip the <?xml ...?> declaration *)
   ignore (Stream.next strm) ; (* to skip the DOCTYPE declaration *)
   match Stream.next strm with
      X.Empty(p,n,l) -> p,n,l,[<>]
    | X.NEmpty(p,n,l,c) -> p,n,l,c
    | _ -> assert false
  in
   let namespaces = update_namespaces (None,[]) root_attributes in
   let namespaceURI = namespace_of_prefix namespaces root_prefix in
   let document =
    domImplementation#createDocument ~namespaceURI
     ~qualifiedName:(get_qualified_name root_prefix root_name)
     ~doctype:None
   in
   let rec aux namespaces (node : Gdome.node) =
    parser
      [< 'X.Str a ; s >] ->
        let textnode = document#createTextNode ~data:(Gdome.domString a) in
         ignore (node#appendChild ~newChild:(textnode :> Gdome.node)) ;
         aux namespaces node s
    | [< 'X.Empty(p,n,l) ; s >] ->
        let namespaces' = update_namespaces namespaces l in
         let namespaceURI = namespace_of_prefix namespaces' p in
          let element =
           document#createElementNS ~namespaceURI
            ~qualifiedName:(get_qualified_name p n)
          in
           List.iter
            (function (p,n,v) ->
              if p = None then
               element#setAttribute ~name:(Gdome.domString n)
                ~value:(Gdome.domString v)
              else
               let namespaceURI = namespace_of_prefix namespaces' p in
                element#setAttributeNS
                 ~namespaceURI
                 ~qualifiedName:(get_qualified_name p n)
                 ~value:(Gdome.domString v)
            ) l ;
          ignore
           (node#appendChild
             ~newChild:(element : Gdome.element :> Gdome.node)) ;
          aux namespaces node s
    | [< 'X.NEmpty(p,n,l,c) ; s >] ->
        let namespaces' = update_namespaces namespaces l in
         let namespaceURI = namespace_of_prefix namespaces' p in
          let element =
           document#createElementNS ~namespaceURI
            ~qualifiedName:(get_qualified_name p n)
          in
           List.iter
            (function (p,n,v) ->
              if p = None then
               element#setAttribute ~name:(Gdome.domString n)
                ~value:(Gdome.domString v)
              else
               let namespaceURI = namespace_of_prefix namespaces' p in
                element#setAttributeNS ~namespaceURI
                 ~qualifiedName:(get_qualified_name p n)
                 ~value:(Gdome.domString v)
            ) l ;
           ignore (node#appendChild ~newChild:(element :> Gdome.node)) ;
           aux namespaces' (element :> Gdome.node) c ;
           aux namespaces node s
    | [< >] -> ()
   in
    let root = document#get_documentElement in
     List.iter
      (function (p,n,v) ->
        if p = None then
         root#setAttribute ~name:(Gdome.domString n)
          ~value:(Gdome.domString v)
        else
         let namespaceURI = namespace_of_prefix namespaces p in
          root#setAttributeNS ~namespaceURI
           ~qualifiedName:(get_qualified_name p n)
           ~value:(Gdome.domString v)
      ) root_attributes ;
     aux namespaces (root : Gdome.element :> Gdome.node) root_content ;
     document
;;
