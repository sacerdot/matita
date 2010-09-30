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

let mathmlns = "http://www.w3.org/1998/Math/MathML";;
let xmldiffns = "http://helm.cs.unibo.it/XmlDiff";;
let helmns = "http://www.cs.unibo.it/helm";;

let ds_selection      = Gdome.domString "selection";;
let ds_2              = Gdome.domString "2";;
let ds_mathmlns       = Gdome.domString mathmlns;;
let ds_m_style        = Gdome.domString "m:mstyle";;
let ds_mathbackground = Gdome.domString "mathbackground";;
let ds_xmldiffns      = Gdome.domString xmldiffns;;
let ds_xmldiff_type   = Gdome.domString "xmldiff:type";;
let ds_fake           = Gdome.domString "fake";;
let ds_helmns         = Gdome.domString helmns;;
let ds_xref           = Gdome.domString "xref";;
let ds_type           = Gdome.domString "type";;
let ds_yellow         = Gdome.domString "yellow";;
let ds_green          = Gdome.domString "#00ff00";;
let ds_maction        = Gdome.domString "maction";;
let ds_mtr            = Gdome.domString "mtr";;
let ds_mtd            = Gdome.domString "mtd";;

type highlighted_nodes = Gdome.node list;;

let rec make_visible (n: Gdome.node) =
 match n#get_parentNode with
    None -> ()
  | Some p ->
     match p#get_namespaceURI, p#get_localName with
        Some nu, Some ln when
         nu#equals ds_mathmlns && ln#equals ds_maction ->
          (new Gdome.element_of_node p)#setAttribute
            ~name:ds_selection
             ~value:ds_2 ;
          make_visible p
      | _,_ -> make_visible p
;;

let highlight_node_total_time = ref 0.0;;

let highlight_node ?(color=ds_yellow) (doc: Gdome.document) (n: Gdome.node) =
 let highlight (n: Gdome.node) =
  let highlighter =
   doc#createElementNS
    ~namespaceURI:(Some ds_mathmlns)
    ~qualifiedName:ds_m_style
  in
   highlighter#setAttribute ~name:ds_mathbackground ~value:color ;
   highlighter#setAttributeNS
    ~namespaceURI:(Some ds_xmldiffns)
    ~qualifiedName:ds_xmldiff_type
    ~value:ds_fake ;
   let parent = 
    match n#get_parentNode with
       None -> assert false
     | Some p -> p
   in
    ignore
     (parent#replaceChild ~oldChild:n ~newChild:(highlighter :> Gdome.node)) ;
    ignore (highlighter#appendChild n) ;
    (highlighter :> Gdome.node)
 in
  let rec find_mstylable_node n =
   match n#get_namespaceURI, n#get_localName with
      Some nu, Some ln when
       nu#equals ds_mathmlns &&
        (not (ln#equals ds_mtr)) && (not (ln#equals ds_mtd)) -> n
    | Some nu, Some ln when
       nu#equals ds_mathmlns &&
        ln#equals ds_mtr || ln#equals ds_mtd ->
         let true_child =
          match n#get_firstChild with
             None -> assert false
           | Some n -> n
         in
          find_mstylable_node true_child
    | _,_ ->
      match n#get_parentNode with
         None -> assert false
       | Some p -> find_mstylable_node p
  in
   let highlighter = highlight (find_mstylable_node n) in
    make_visible highlighter ;
    highlighter
;;

let iter_children ~f (n:Gdome.node) =
 let rec aux =
  function
     None -> ()
   | Some n ->
      let sibling = n#get_nextSibling in
       (f n) ;
       aux sibling
 in
  aux n#get_firstChild
;;

let highlight_nodes ~xrefs (doc:Gdome.document) =
 let highlighted = ref [] in
 let rec aux (n:Gdome.element) =
  let attributeNS =
    (n#getAttributeNS ~namespaceURI:ds_helmns
     ~localName:ds_xref)#to_string in
  if List.mem attributeNS xrefs then
   highlighted :=
    (highlight_node ~color:ds_green doc (n :> Gdome.node))::
    !highlighted ;
   iter_children (n :> Gdome.node)
    ~f:(function n ->
         if n#get_nodeType = GdomeNodeTypeT.ELEMENT_NODE then
          aux (new Gdome.element_of_node n))
 in
  aux doc#get_documentElement ;
  !highlighted
;;

let dim_nodes =
 List.iter 
  (function (n : Gdome.node) ->
    assert
     (n#get_nodeType = GdomeNodeTypeT.ELEMENT_NODE &&
      ((new Gdome.element_of_node n)#getAttributeNS
        ~namespaceURI:ds_xmldiffns
        ~localName:ds_type)#equals ds_fake) ;
    let true_child =
     match n#get_firstChild with
        None -> assert false
      | Some n -> n in
    let p =
     match n#get_parentNode with
        None -> assert false
      | Some n -> n
    in
     ignore (p#replaceChild ~oldChild:n ~newChild:true_child)
  )
;;

let update_dom ~(from : Gdome.document) (d : Gdome.document) =
 let rec aux (p: Gdome.node) (f: Gdome.node) (t: Gdome.node) =
 let replace t1 =
  if
   t1 = GdomeNodeTypeT.ELEMENT_NODE &&
   ((new Gdome.element_of_node f)#getAttributeNS
     ~namespaceURI:ds_xmldiffns
     ~localName:ds_type)#equals ds_fake
  then
   let true_child =
    match f#get_firstChild with
       None -> assert false
     | Some n -> n
   in
    begin
     ignore (p#replaceChild ~oldChild:f ~newChild:true_child) ;
     aux p true_child t
    end
  else
   let t' = from#importNode t true in
    ignore (p#replaceChild ~newChild:t' ~oldChild:f) ;
    (* ignore (highlight_node from t') *)
  in
  match
   f#get_nodeType,t#get_nodeType
  with
     GdomeNodeTypeT.TEXT_NODE,GdomeNodeTypeT.TEXT_NODE ->
      (match f#get_nodeValue, t#get_nodeValue with
          Some v, Some v' when v#equals v' -> ()
        | Some _, (Some _ as v') -> f#set_nodeValue v'
        | _,_ -> assert false)
   | GdomeNodeTypeT.ELEMENT_NODE as t1,GdomeNodeTypeT.ELEMENT_NODE ->
      (match
        f#get_namespaceURI,t#get_namespaceURI,f#get_localName,t#get_localName
       with
        Some nu, Some nu', Some ln, Some ln' when
         ln#equals ln' && nu#equals nu' ->
          begin
           match f#get_attributes, t#get_attributes with
              Some fattrs, Some tattrs ->
               let flen = fattrs#get_length in
               let tlen = tattrs#get_length in
                let processed = ref [] in
                for i = 0 to flen -1 do
                 match fattrs#item i with
                    None -> () (* CSC: sigh, togliere un nodo rompe fa decrescere la lunghezza ==> passare a un while *)
                  | Some attr ->
                      match attr#get_namespaceURI with
                         None ->
                          (* Back to DOM Level 1 ;-( *)
                          begin
                           let name = attr#get_nodeName in
                            match tattrs#getNamedItem ~name with
                               None ->
                               ignore (fattrs#removeNamedItem ~name)
                             | Some attr' ->
                                processed :=
                                 (None,Some name)::!processed ;
                                match attr#get_nodeValue, attr'#get_nodeValue with
                                   Some v1, Some v2 when
                                       v1#equals v2
                                    || (name#equals ds_selection &&
                                        nu#equals ds_mathmlns &&
                                        ln#equals ds_maction)
                                    ->
                                     ()
                                 | Some v1, Some v2 ->
                                    let attr'' = from#importNode attr' true in
                                     ignore (fattrs#setNamedItem attr'')
                                 | _,_ -> assert false
                          end
                       | Some namespaceURI ->
                          let localName = 
                           match attr#get_localName with
                             Some v -> v
                            | None -> assert false
                          in
                           match
                            tattrs#getNamedItemNS ~namespaceURI ~localName
                           with
                              None ->
                               ignore
                                (fattrs#removeNamedItemNS
                                  ~namespaceURI ~localName)
                            | Some attr' ->
                               processed :=
                                (Some namespaceURI,Some localName)::!processed ;
                                match attr#get_nodeValue, attr'#get_nodeValue with
                                   Some v1, Some v2 when
                                    v1#equals v2 ->
                                     ()
                                 | Some _, Some _ ->
                                    let attr'' = from#importNode attr' true in
                                     ignore (fattrs#setNamedItem attr'')
                                 | _,_ -> assert false
                done ;
                for i = 0 to tlen -1 do
                 match tattrs#item i with
                    None -> assert false
                  | Some attr ->
                     let namespaceURI,localName =
                      match attr#get_namespaceURI with
                         None ->
                          None,attr#get_nodeName
                       | Some namespaceURI as v ->
                         v, match attr#get_localName with
                            None -> assert false
                          | Some v -> v
                     in
                      if
                       not
                        (List.exists
                          (function
                              None,Some localName' ->
                               (match namespaceURI with
                                   None ->
                                    localName#equals localName'
                                 | Some _ -> false)
                            | Some namespaceURI', Some localName' ->
                               (match namespaceURI with
                                   None -> false
                                 | Some namespaceURI ->
                                    localName#equals localName' &&
                                    namespaceURI#equals namespaceURI'
                               )
                            | _,_ -> assert false
                          ) !processed)
                      then
                       let attr' = from#importNode attr false in
                        ignore (fattrs#setNamedItem attr')
                done
            | _,_ -> assert false
          end ;
          let rec dumb_diff =
           function
              [],[] -> ()
            | he1::tl1,he2::tl2 ->
               aux f he1 he2 ;
               dumb_diff (tl1,tl2)
            | [],tl2 ->
               List.iter
                (function n ->
                  let n' = from#importNode n true in
                    ignore (f#appendChild n') ;
                    (* ignore (highlight_node from n') *)
		    ()
                ) tl2
            | tl1,[] ->
               List.iter (function n -> ignore (f#removeChild n)) tl1
          in
           let node_list_of_nodeList n =
            let rec aux =
             function
                None -> []
              | Some n when
                    n#get_nodeType = GdomeNodeTypeT.ELEMENT_NODE
                 or n#get_nodeType = GdomeNodeTypeT.TEXT_NODE ->
                  n::(aux n#get_nextSibling)
              | Some n ->
                aux n#get_nextSibling
            in
             aux n#get_firstChild
           in
            dumb_diff
             (node_list_of_nodeList f, node_list_of_nodeList t)
      | _,_,_,_ -> replace t1
      )
   | t1,t2 when
      (t1 = GdomeNodeTypeT.ELEMENT_NODE || t1 = GdomeNodeTypeT.TEXT_NODE) &&
      (t2 = GdomeNodeTypeT.ELEMENT_NODE || t2 = GdomeNodeTypeT.TEXT_NODE) ->
       replace t1
   | _,_ -> assert false
 in
  try
   aux (d :> Gdome.node)
    (from#get_documentElement :> Gdome.node)
    (d#get_documentElement :> Gdome.node)
  with
     (GdomeInit.DOMException (e,msg) as ex) -> raise ex
  | e -> raise e
;;
