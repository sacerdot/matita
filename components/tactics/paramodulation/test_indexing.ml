(* $Id$ *)

open Path_indexing

(*
let build_equality term =
  let module C = Cic in
  C.Implicit None, (C.Implicit None, term, C.Rel 1, Utils.Gt), [], []
;;


(*
  f = Rel 1
  g = Rel 2
  a = Rel 3
  b = Rel 4
  c = Rel 5
*)
let path_indexing_test () =
  let module C = Cic in
  let terms = [
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Rel 3; C.Meta (1, [])]; C.Rel 5];
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Meta (1, []); C.Rel 4]; C.Meta (1, [])];
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Rel 3; C.Rel 4]; C.Rel 5];
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Meta (1, []); C.Rel 5]; C.Rel 4];
    C.Appl [C.Rel 1; C.Meta (1, []); C.Meta (1, [])]
  ] in
  let path_strings = List.map (path_strings_of_term 0) terms in
  let table =
    List.fold_left index PSTrie.empty (List.map build_equality terms) in
  let query =
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Meta (1, []); C.Rel 4]; C.Rel 5] in
  let matches = retrieve_generalizations table query in
  let unifications = retrieve_unifiables table query in
  let eq1 = build_equality (C.Appl [C.Rel 1; C.Meta (1, []); C.Meta (1, [])])
  and eq2 = build_equality (C.Appl [C.Rel 1; C.Meta (1, []); C.Meta (2, [])]) in
  let res1 = in_index table eq1
  and res2 = in_index table eq2 in
  let print_results res =
    String.concat "\n"
      (PosEqSet.fold
         (fun (p, e) l ->
            let s = 
              "(" ^ (Utils.string_of_pos p) ^ ", " ^
                (Inference.string_of_equality e) ^ ")"
            in
            s::l)
         res [])
  in
  Printf.printf "path_strings:\n%s\n\n"
    (String.concat "\n"
       (List.map
          (fun l ->
             "{" ^ (String.concat "; " (List.map string_of_path_string l)) ^ "}"
          ) path_strings));
  Printf.printf "table:\n%s\n\n" (string_of_pstrie table);
  Printf.printf "matches:\n%s\n\n" (print_results matches);
  Printf.printf "unifications:\n%s\n\n" (print_results unifications);
  Printf.printf "in_index %s: %s\n"
    (Inference.string_of_equality eq1) (string_of_bool res1);
  Printf.printf "in_index %s: %s\n"
    (Inference.string_of_equality eq2) (string_of_bool res2);
;;


let differing () =
  let module C = Cic in
  let t1 =
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Rel 3; C.Meta (1, [])]; C.Rel 5]
  and t2 = 
    C.Appl [C.Rel 1; C.Appl [C.Rel 5; C.Rel 4; C.Meta (1, [])]; C.Rel 5]
  in
  let res = Inference.extract_differing_subterms t1 t2 in
  match res with
  | None -> prerr_endline "NO DIFFERING SUBTERMS???"
  | Some (t1, t2) ->
      Printf.printf "OK: %s, %s\n" (CicPp.ppterm t1) (CicPp.ppterm t2);
;;


let next_after () =
  let module C = Cic in
  let t =
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Rel 3; C.Rel 4]; C.Rel 5]
  in
  let pos1 = Discrimination_tree.next_t [1] t in
  let pos2 = Discrimination_tree.after_t [1] t in
  Printf.printf "next_t 1: %s\nafter_t 1: %s\n"
    (CicPp.ppterm (Discrimination_tree.subterm_at_pos pos1 t))
    (CicPp.ppterm (Discrimination_tree.subterm_at_pos pos2 t));
;;


let discrimination_tree_test () =
  let module C = Cic in
  let terms = [
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Rel 3; C.Meta (1, [])]; C.Rel 5];
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Meta (1, []); C.Rel 4]; C.Meta (1, [])];
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Rel 3; C.Rel 4]; C.Rel 5];
    C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Meta (1, []); C.Rel 5]; C.Rel 4];
    C.Appl [C.Rel 10; C.Meta (5, []); C.Rel 11]
  ] in
  let path_strings =
    List.map Discrimination_tree.path_string_of_term terms in
  let table =
    List.fold_left
      Discrimination_tree.index
      Discrimination_tree.DiscriminationTree.empty
      (List.map build_equality terms)
  in
(*   let query = *)
(*     C.Appl [C.Rel 1; C.Appl [C.Rel 2; C.Meta (1, []); C.Rel 4]; C.Rel 5] in *)
  let query = C.Appl [C.Rel 10; C.Meta (14, []); C.Meta (13, [])] in
  let matches = Discrimination_tree.retrieve_generalizations table query in
  let unifications = Discrimination_tree.retrieve_unifiables table query in
  let eq1 = build_equality (C.Appl [C.Rel 1; C.Meta (1, []); C.Meta (1, [])])
  and eq2 = build_equality (C.Appl [C.Rel 1; C.Meta (1, []); C.Meta (2, [])]) in
  let res1 = Discrimination_tree.in_index table eq1
  and res2 = Discrimination_tree.in_index table eq2 in
  let print_results res =
    String.concat "\n"
      (Discrimination_tree.PosEqSet.fold
         (fun (p, e) l ->
            let s = 
              "(" ^ (Utils.string_of_pos p) ^ ", " ^
                (Inference.string_of_equality e) ^ ")"
            in
            s::l)
         res [])
  in
  Printf.printf "path_strings:\n%s\n\n"
    (String.concat "\n"
       (List.map Discrimination_tree.string_of_path_string path_strings));
  Printf.printf "table:\n%s\n\n"
    (Discrimination_tree.string_of_discrimination_tree table);
  Printf.printf "matches:\n%s\n\n" (print_results matches);
  Printf.printf "unifications:\n%s\n\n" (print_results unifications);
  Printf.printf "in_index %s: %s\n"
    (Inference.string_of_equality eq1) (string_of_bool res1);
  Printf.printf "in_index %s: %s\n"
    (Inference.string_of_equality eq2) (string_of_bool res2);
;;


let test_subst () =
  let module C = Cic in
  let module M = CicMetaSubst in
  let term = C.Appl [
    C.Rel 1;
    C.Appl [C.Rel 11;
            C.Meta (43, []);
            C.Appl [C.Rel 15; C.Rel 12; C.Meta (41, [])]];
    C.Appl [C.Rel 11;
            C.Appl [C.Rel 15; C.Meta (10, []); C.Meta (11, [])];
            C.Appl [C.Rel 15; C.Meta (10, []); C.Meta (12, [])]]
  ] in
  let subst1 = [
    (43, ([], C.Appl [C.Rel 15; C.Meta (10, []); C.Meta (11, [])], C.Rel 16));
    (10, ([], C.Rel 12, C.Rel 16));
    (12, ([], C.Meta (41, []), C.Rel 16))
  ]
  and subst2 = [
    (43, ([], C.Appl [C.Rel 15; C.Rel 12; C.Meta (11, [])], C.Rel 16));
    (10, ([], C.Rel 12, C.Rel 16));
    (12, ([], C.Meta (41, []), C.Rel 16))
  ] in
  let t1 = M.apply_subst subst1 term
  and t2 = M.apply_subst subst2 term in
  Printf.printf "t1 = %s\nt2 = %s\n" (CicPp.ppterm t1) (CicPp.ppterm t2);
;;
*)
  

let test_refl () =
  let module C = Cic in
  let context = [
    Some (C.Name "H", C.Decl (
            C.Prod (C.Name "z", C.Rel 3,
                    C.Appl [
                      C.MutInd (HelmLibraryObjects.Logic.eq_URI, 0, []);
                      C.Rel 4; C.Rel 3; C.Rel 1])));
    Some (C.Name "x", C.Decl (C.Rel 2));
    Some (C.Name "y", C.Decl (C.Rel 1));
    Some (C.Name "A", C.Decl (C.Sort C.Set))
  ]
  in
  let term = C.Appl [
    C.Const (HelmLibraryObjects.Logic.eq_ind_URI, []); C.Rel 4;
    C.Rel 2;
    C.Lambda (C.Name "z", C.Rel 4,
              C.Appl [
                C.MutInd (HelmLibraryObjects.Logic.eq_URI, 0, []);
                C.Rel 5; C.Rel 1; C.Rel 3
              ]);
    C.Appl [C.MutConstruct
              (HelmLibraryObjects.Logic.eq_URI, 0, 1, []); (* reflexivity *)
            C.Rel 4; C.Rel 2];
    C.Rel 3;
(*     C.Appl [C.Const (HelmLibraryObjects.Logic.sym_eq_URI, []); (\* symmetry *\) *)
(*             C.Rel 4; C.Appl [C.Rel 1; C.Rel 2]] *)
    C.Appl [
      C.Const (HelmLibraryObjects.Logic.eq_ind_URI, []);
      C.Rel 4; C.Rel 3;
      C.Lambda (C.Name "z", C.Rel 4,
                C.Appl [
                  C.MutInd (HelmLibraryObjects.Logic.eq_URI, 0, []);
                  C.Rel 5; C.Rel 1; C.Rel 4
                ]);
      C.Appl [C.MutConstruct (HelmLibraryObjects.Logic.eq_URI, 0, 1, []);
              C.Rel 4; C.Rel 3];
      C.Rel 2; C.Appl [C.Rel 1; C.Rel 2]
    ]
  ] in
  let ens = [
    (UriManager.uri_of_string "cic:/Coq/Init/Logic/Logic_lemmas/equality/A.var",
     C.Rel 4);
    (UriManager.uri_of_string "cic:/Coq/Init/Logic/Logic_lemmas/equality/x.var",
     C.Rel 3);
    (UriManager.uri_of_string "cic:/Coq/Init/Logic/Logic_lemmas/equality/y.var",
     C.Rel 2);    
  ] in
  let term2 = C.Appl [
    C.Const (HelmLibraryObjects.Logic.sym_eq_URI, ens);
    C.Appl [C.Rel 1; C.Rel 2]
  ] in
  let ty, ug =
    CicTypeChecker.type_of_aux' [] context term CicUniv.empty_ugraph
  in
  Printf.printf "OK, %s ha tipo %s\n" (CicPp.ppterm term) (CicPp.ppterm ty);
  let ty, ug =
    CicTypeChecker.type_of_aux' [] context term2 CicUniv.empty_ugraph
  in
  Printf.printf "OK, %s ha tipo %s\n" (CicPp.ppterm term2) (CicPp.ppterm ty); 
;;


let test_lib () =
  let uri = Sys.argv.(1) in
  let t = CicUtil.term_of_uri (UriManager.uri_of_string uri) in
  let ty, _ = CicTypeChecker.type_of_aux' [] [] t CicUniv.empty_ugraph in
  Printf.printf "Term of %s: %s\n" uri (CicPp.ppterm t);
  Printf.printf "type: %s\n" (CicPp.ppterm ty);
;;


(* differing ();; *)
(* next_after ();; *)
(* discrimination_tree_test ();; *)
(* path_indexing_test ();; *)
(* test_subst ();; *)
Helm_registry.load_from "../../matita/matita.conf.xml";
(* test_refl ();; *)
test_lib ();;
