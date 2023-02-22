
universe constraint Type[0] < Type[1].

ninductive exadecim : Type ≝
  x0: exadecim
| x1: exadecim
| x2: exadecim
| x3: exadecim
| x4: exadecim
| x5: exadecim
| x6: exadecim
| x7: exadecim
| x8: exadecim
| x9: exadecim
| xA: exadecim
| xB: exadecim
| xC: exadecim
| xD: exadecim
| xE: exadecim
| xF: exadecim.

ninductive bool : Type ≝ true :bool | false : bool .

ndefinition eq_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with [ x0 ⇒ true  | _ ⇒ false ]
  | x1 ⇒ match e2 with [ x1 ⇒ true  | _ ⇒ false ]
  | x2 ⇒ match e2 with [ x2 ⇒ true  | _ ⇒ false ]
  | x3 ⇒ match e2 with [ x3 ⇒ true  | _ ⇒ false ]
  | x4 ⇒ match e2 with [ x4 ⇒ true  | _ ⇒ false ]
  | x5 ⇒ match e2 with [ x5 ⇒ true  | _ ⇒ false ]
  | x6 ⇒ match e2 with [ x6 ⇒ true  | _ ⇒ false ]
  | x7 ⇒ match e2 with [ x7 ⇒ true  | _ ⇒ false ]
  | x8 ⇒ match e2 with [ x8 ⇒ true  | _ ⇒ false ]
  | x9 ⇒ match e2 with [ x9 ⇒ true  | _ ⇒ false ]
  | xA ⇒ match e2 with [ xA ⇒ true  | _ ⇒ false ]
  | xB ⇒ match e2 with [ xB ⇒ true  | _ ⇒ false ]
  | xC ⇒ match e2 with [ xC ⇒ true  | _ ⇒ false ]
  | xD ⇒ match e2 with [ xD ⇒ true  | _ ⇒ false ]
  | xE ⇒ match e2 with [ xE ⇒ true  | _ ⇒ false ]
  | xF ⇒ match e2 with [ xF ⇒ true  | _ ⇒ false ]
  ].

ndefinition succ_ex ≝
λe:exadecim.
 match e with
  [ x0 ⇒ x1 | x1 ⇒ x2 | x2 ⇒ x3 | x3 ⇒ x4 | x4 ⇒ x5 | x5 ⇒ x6 | x6 ⇒ x7 | x7 ⇒ x8
  | x8 ⇒ x9 | x9 ⇒ xA | xA ⇒ xB | xB ⇒ xC | xC ⇒ xD | xD ⇒ xE | xE ⇒ xF | xF ⇒ x0 ].


nrecord byte8 : Type ≝
 {
 b8h: exadecim;
 b8l: exadecim
 }.
 
notation "〈x,y〉" non associative with precedence 80
 for @{ 'mk_byte8 $x $y }.
interpretation "mk_byte8" 'mk_byte8 x y = (mk_byte8 x y).

ndefinition andb ≝ λa,b.match a with [ true ⇒ b | _ ⇒ false ].

ndefinition eq_b8 ≝ λb1,b2:byte8.andb (eq_ex (b8h b1) (b8h b2))  (eq_ex (b8l b1) (b8l b2)).
ndefinition succ_b8 ≝
λb:byte8.match eq_ex (b8l b) xF with
 [ true ⇒ mk_byte8 (succ_ex (b8h b)) (succ_ex (b8l b))
 | false ⇒ mk_byte8 (b8h b) (succ_ex (b8l b)) ]. 

nrecord word16 : Type ≝
 {
 w16h: byte8;
 w16l: byte8
 }.

(* \langle \rangle *)
notation "〈x:y〉" non associative with precedence 80
 for @{ 'mk_word16 $x $y }.
interpretation "mk_word16" 'mk_word16 x y = (mk_word16 x y).

ndefinition succ_w16 ≝
λw:word16.
  match eq_b8 (w16l w) (mk_byte8 xF xF) with
 [ true ⇒ mk_word16 (succ_b8 (w16h w)) (succ_b8 (w16l w))
 | false ⇒ mk_word16 (w16h w) (succ_b8 (w16l w)) ].

ninductive eq (A:Type) (a:A) : A → Prop ≝ refl_eq : eq A a a.

interpretation "aa" 'eq t a b = (eq t a b).

