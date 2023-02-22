
(*include "utility/utility.ma".

nlemma fold_right_neList2_aux3 :
\forall T. \forall h,h',t,t'.len_neList T (h§§t) = len_neList T (h'§§t') → len_neList T t = len_neList T t'.
 #T; #h; #h'; #t; #t';
 napply (ne_list_ind T ??? t);
 napply (ne_list_ind T ??? t');
 ##[ ##1: nnormalize; #x; #y; #H; napply (refl_eq ??)
 ##| ##2: #a; #l'; #H; #x; #H1;
          nchange in H1:(%) with ((S (len_neList T «£x»)) = (S (len_neList T (a§§l'))));
          nrewrite > (nat_destruct_S_S ?? H1);
          napply (refl_eq ??)
 ##| ##3: #x; #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S (len_neList T (a§§l')))= (S (len_neList T «£x»)));
          nrewrite > (nat_destruct_S_S ?? H1);
          napply (refl_eq ??)
 ##| ##4: #a; #l; #H; #a1; #l1; #H1; #H2;
          (* sarebbe nchange in H2:(%) with ((S (len_neList T (a1§§l1))) = (S (len_neList T (a§§l)))); *)
          (* ma fa passare il seguente errato ... *) 
          nchange in H2:(%) with ((S (len_neList T (a§§l1))) = (S (len_neList T (a§§l))));
*)

(*include "freescale/byte8_lemmas.ma".

nlemma associative_plusb8_aux
 : \forall e1,e2,e3,e4.
  match plus_ex_d_dc e2 e4 with
   [ pair l c ⇒ 〈plus_ex_dc_d e1 e3 c,l〉 ] =
  〈plus_ex_dc_d e1 e3 (snd ?? (plus_ex_d_dc e2 e4)),(fst ?? (plus_ex_d_dc e2 e4))〉.
 #e1; #e2; #e3; #e4;
 (* anche qui appare un T1 *)
 ncases (plus_ex_d_dc e2 e4);
 #e5; #c;
 napply (refl_eq ??).
nqed.

nlemma associative_plusb8
 : \forall b1,b2,b3.(plus_b8_d_d (plus_b8_d_d b1 b2) b3) = (plus_b8_d_d b1 (plus_b8_d_d b2 b3)).
 #b1; ncases b1; #e1; #e2;
 #b2; ncases b2; #e3; #e4;
 #b3; ncases b3; #e5; #e6;

(* perche' volendo posso introdurre anche 2 premesse diverse con lo stesso nome? tipo #e2; #e2 *)

 nchange with ( 
 match plus_ex_d_dc (b8l (match plus_ex_d_dc e2 e4 with
                           [ pair l1 c1 ⇒ 〈plus_ex_dc_d e1 e3 c1,l1〉 ])) e6 with
  [ pair l2 c2 ⇒ 〈plus_ex_dc_d (b8h (match plus_ex_d_dc e2 e4 with
                                    [ pair l3 c3 ⇒ 〈plus_ex_dc_d e1 e3 c3,l3〉 ])) e5 c2,l2〉 ] =
 match plus_ex_d_dc e2 (b8l (match plus_ex_d_dc e4 e6 with
                                    [ pair l4 c4 ⇒ 〈plus_ex_dc_d e3 e5 c4,l4〉 ])) with
  [ pair l5 c5 ⇒ 〈plus_ex_dc_d e1 (b8h (match plus_ex_d_dc e4 e6 with
                                             [ pair l6 c6 ⇒ 〈plus_ex_dc_d e3 e5 c6,l6〉 ])) c5,l5〉 ]);

(* gia' qua ci sono T1, T2 che appaiono dal nulla al posto delle variabili *)

 nrewrite > (associative_plusb8_aux e1 e2 e3 e4);
 nrewrite > (associative_plusb8_aux e3 e4 e5 e6);
 nrewrite > (plusex_d_dc_to_d_c e2 e4);
 nrewrite > (plusex_d_dc_to_d_d e2 e4);
 nrewrite > (plusex_d_dc_to_d_c e4 e6);

 (* nel visualizzatore era (snd ?? (plus_ex_d_dc e5 T2)) ma ha accettato la versione corretta *)

 nrewrite > (plusex_d_dc_to_d_d e4 e6);
 
 (*...*)
*)

(*include "compiler/ast_type_lemmas.ma".

nlemma symmetric_eqasttype_aux1
 : ∀x1,x2,y2.eq_nat (len_neList ast_type («£x1»)) (len_neList ast_type (x2§§y2)) = false.
 #x1; #x2; #y2; ncases y2; nnormalize;
 ##[ ##1: #t; napply (refl_eq ??)
 ##| ##2: #t; #l; napply (refl_eq ??)
 ##]
nqed.

nlemma symmetric_eqasttype_aux2
 : ∀x1,y1,x2.eq_nat (len_neList ast_type (x1§§y1)) (len_neList ast_type («£x2»)) = false.
 #x1; #y1; #x2; ncases y1; nnormalize;
 ##[ ##1: #t; napply (refl_eq ??)
 ##| ##2: #t; #l; napply (refl_eq ??)
 ##]
nqed.

ndefinition symmetric_eqasttype_aux3 ≝
λnelSubType1,nelSubType2:ne_list ast_type.
 match eq_nat (len_neList ast_type nelSubType1) (len_neList ast_type nelSubType2)
  return λx.eq_nat (len_neList ast_type nelSubType1) (len_neList ast_type nelSubType2) = x → bool
 with
  [ true ⇒ λp:(eq_nat (len_neList ast_type nelSubType1) (len_neList ast_type nelSubType2) = true).
   fold_right_neList2 ?? (λx1,x2,acc.(eq_ast_type x1 x2)⊗acc)
                      true nelSubType1 nelSubType2
                      (eqnat_to_eq (len_neList ? nelSubType1) (len_neList ? nelSubType2) p)
  | false ⇒ λp:(eq_nat (len_neList ast_type nelSubType1) (len_neList ast_type nelSubType2) = false).false
  ] (refl_eq ? (eq_nat (len_neList ast_type nelSubType1) (len_neList ast_type nelSubType2))).

nlemma symmetric_eqasttype : symmetricT ast_type bool eq_ast_type.
 #t1;
 napply (ast_type_ind ????? t1);
 ##[ ##1: #b1; #t2; ncases t2;
          ##[ ##1: #b2; nchange with ((eq_ast_base_type b1 b2) = (eq_ast_base_type b2 b1));
                   nrewrite > (symmetric_eqastbasetype b1 b2);
                   napply (refl_eq ??)
          ##| ##2: #tt; #n; nnormalize; napply (refl_eq ??)
          ##| ##3: #l; nnormalize; napply (refl_eq ??)
          ##]
 ##| ##2: #tt1; #n1; #H; #t2; ncases t2;
          ##[ ##2: #tt2; #n2; nchange with (((eq_ast_type tt1 tt2)⊗(eq_nat n1 n2)) = ((eq_ast_type tt2 tt1)⊗(eq_nat n2 n1)));
                   nrewrite > (H tt2);
                   nrewrite > (symmetric_eqnat n1 n2);
                   napply (refl_eq ??)
          ##| ##1: #b2; nnormalize; napply (refl_eq ??)
          ##| ##3: #l; nnormalize; napply (refl_eq ??)
          ##]
 ##| ##3: #tt1; #H; #t2; ncases t2;
          ##[ ##3: #l; ncases l;
                   ##[ ##1: #tt2; nnormalize; nrewrite > (H tt2); napply (refl_eq ??)
                   ##| ##2: #tt2; #l1;
                            nchange with (
                             (match eq_nat (len_neList ast_type «£tt1») (len_neList ast_type (tt2§§l1))
                               return λx.eq_nat (len_neList ast_type «£tt1») (len_neList ast_type (tt2§§l1)) = x → bool
                              with
                               [ true ⇒ λp:(eq_nat (len_neList ast_type «£tt1») (len_neList ast_type (tt2§§l1)) = true).
                                fold_right_neList2 ?? (λx1,x2,acc.(eq_ast_type x1 x2)⊗acc)
                                                   true «£tt1» (tt2§§l1)
                                                   (eqnat_to_eq (len_neList ? «£tt1») (len_neList ? (tt2§§l1)) p)
                               | false ⇒ λp:(eq_nat (len_neList ast_type «£tt1») (len_neList ast_type (tt2§§l1)) = false).false
                               ] (refl_eq ? (eq_nat (len_neList ast_type «£tt1») (len_neList ast_type (tt2§§l1))))) = ?);

                            (* eseguendo questa sequenza e' ok *)
                            nrewrite > (symmetric_eqasttype_aux1 tt1 tt2 l1);
                            nchange with (
                             false = (match eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1»)
                               return λx.eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1») = x → bool
                              with
                               [ true ⇒ λp:(eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1») = true).
                                fold_right_neList2 ?? (λx1,x2,acc.(eq_ast_type x1 x2)⊗acc)
                                                   true (tt2§§l1) «£tt1»
                                                   (eqnat_to_eq (len_neList ? (tt2§§l1)) (len_neList ? «£tt1») p)
                               | false ⇒ λp:(eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1») = false).false
                               ] (refl_eq ? (eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1»)))));
                            nrewrite > (symmetric_eqasttype_aux2 tt2 l1 tt1);
                            nnormalize;

                            (* se commentiamo invece la prima sequenza ed eseguiamo questa *)
                            (* come e' possibile che rigetti la seconda rewrite? *)
                            nchange with (
                             ? = (match eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1»)
                               return λx.eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1») = x → bool
                              with
                               [ true ⇒ λp:(eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1») = true).
                                fold_right_neList2 ?? (λx1,x2,acc.(eq_ast_type x1 x2)⊗acc)
                                                   true (tt2§§l1) «£tt1»
                                                   (eqnat_to_eq (len_neList ? (tt2§§l1)) (len_neList ? «£tt1») p)
                               | false ⇒ λp:(eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1») = false).false
                               ] (refl_eq ? (eq_nat (len_neList ast_type (tt2§§l1)) (len_neList ast_type «£tt1»)))));
                            nrewrite > (symmetric_eqasttype_aux1 tt1 tt2 l1);                            
                            nrewrite > (symmetric_eqasttype_aux2 tt2 l1 tt1);
*)
