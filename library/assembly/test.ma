(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/assembly/test/".

include "vm.ma".

notation "hvbox(# break a)"
  non associative with precedence 80
for @{ 'byte_of_opcode $a }.
interpretation "byte_of_opcode" 'byte_of_opcode a =
 (cic:/matita/assembly/vm/byte_of_opcode.con a).

definition mult_source : list byte ≝
  [#LDAi; mk_byte x0 x0; (* A := 0 *)
   #STAd; mk_byte x2 x0; (* Z := A *)
   #LDAd; mk_byte x1 xF; (* (l1) A := Y *)
   #BEQ;  mk_byte x0 xA; (* if A == 0 then goto l2 *)
   #LDAd; mk_byte x2 x0; (* A := Z *)
   #DECd; mk_byte x1 xF; (* Y := Y - 1 *)
   #ADDd; mk_byte x1 xE; (* A += X *)
   #STAd; mk_byte x2 x0; (* Z := A *)
   #BRA;  mk_byte xF x2; (* goto l1 *)
   #LDAd; mk_byte x2 x0].(* (l2) *)

definition mult_memory ≝
 λx,y.λa:addr.
     match leb a 29 with
      [ true ⇒ nth ? mult_source (mk_byte x0 x0) a
      | false ⇒
         match eqb a 30 with
          [ true ⇒ x
          | false ⇒ y
          ]
      ].

definition mult_status ≝
 λx,y.
  mk_status (mk_byte x0 x0) 0 0 false false (mult_memory x y) 0.

lemma test_O_O:
  let i ≝ 14 in
  let s ≝ execute (mult_status (mk_byte x0 x0) (mk_byte x0 x0)) i in
   pc s = 20 ∧ mem s 32 = byte_of_nat 0.
 normalize;
 split;
 reflexivity.
qed.

lemma test_0_2:
  let x ≝ mk_byte x0 x0 in
  let y ≝ mk_byte x0 x2 in
  let i ≝ 14 + 23 * nat_of_byte y in
  let s ≝ execute (mult_status x y) i in
   pc s = 20 ∧ mem s 32 = plusbytenc x x.
 intros;
 split;
 reflexivity.
qed.

lemma test_x_1:
 ∀x.
  let y ≝ mk_byte x0 x1 in
  let i ≝ 14 + 23 * nat_of_byte y in
  let s ≝ execute (mult_status x y) i in
   pc s = 20 ∧ mem s 32 = x.
 intros;
 split;
  [ reflexivity
  | change in ⊢ (? ? % ?) with (plusbytenc (mk_byte x0 x0) x);
    rewrite > plusbytenc_O_x;
    reflexivity
  ].
qed.

lemma test_x_2:
 ∀x.
  let y ≝ mk_byte x0 x2 in
  let i ≝ 14 + 23 * nat_of_byte y in
  let s ≝ execute (mult_status x y) i in
   pc s = 20 ∧ mem s 32 = plusbytenc x x.
 intros;
 split;
  [ reflexivity
  | change in ⊢ (? ? % ?) with
     (plusbytenc (plusbytenc (mk_byte x0 x0) x) x);
    rewrite > plusbytenc_O_x;
    reflexivity
  ].
qed.

lemma loop_invariant':
 ∀x,y:byte.∀j:nat. j ≤ y →
  execute (mult_status x y) (5 + 23*j)
   =
    mk_status (byte_of_nat (x * j)) 4 0 (eqbyte (mk_byte x0 x0) (byte_of_nat (x*j)))
     (plusbytec (byte_of_nat (x*pred j)) x)
     (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (y - j))) 32
      (byte_of_nat (x * j)))
     0.
 intros 3;
 elim j;
  [ do 2 (rewrite < times_n_O);
    apply status_eq;
    [1,2,3,4,7: normalize; reflexivity
    | rewrite > eq_plusbytec_x0_x0_x_false;
      normalize;
      reflexivity 
    | intro;
      rewrite < minus_n_O;
      normalize in ⊢ (? ? (? (? ? %) ?) ?);
      whd in ⊢ (? ? % ?);
      change in ⊢ (? ? % ?) with (update (mult_memory x y) 32 (mk_byte x0 x0) a);
      change in ⊢ (? ? ? %) with (update (update (update (mult_memory x y) 30 x) 31
        (byte_of_nat y)) 32 (byte_of_nat 0) a);
      change in ⊢ (? ? ? (? (? (? ? ? %) ? ?) ? ? ?)) with (mult_memory x y 30);
      rewrite > byte_of_nat_nat_of_byte;
      change in ⊢ (? ? ? (? (? ? ? %) ? ? ?)) with (mult_memory x y 31);
      apply inj_update;
      intro;
      rewrite > (eq_update_s_a_sa (update (mult_memory x y) 30 (mult_memory x y 30))
       31 a) in ⊢ (? ? ? %);
      rewrite > eq_update_s_a_sa;
      reflexivity
    ]
  | cut (5 + 23 * S n = 5 + 23 * n + 23);
    [ letin K ≝ (breakpoint (mult_status x y) (5 + 23 * n) 23); clearbody K;
      letin H' ≝ (H ?); clearbody H'; clear H;
      [ autobatch
      | letin xxx ≝ (eq_f ? ? (λz. execute (mult_status x y) z) ? ? Hcut); clearbody xxx;
        clear Hcut;
        rewrite > xxx;
        clear xxx;
        apply (transitive_eq ? ? ? ? K);
        clear K; 
        rewrite > H';
        clear H';
        cut (∃z.y-n=S z ∧ z < 255);
         [ elim Hcut; clear Hcut;
           elim H; clear H;
           rewrite > H2;
           (* instruction LDAd *)
           letin K ≝
            (breakpoint
              (mk_status (byte_of_nat (x*n)) 4 O
               (eqbyte (mk_byte x0 x0) (byte_of_nat (x*n)))
               (plusbytec (byte_of_nat (x*pred n)) x)
               (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (S a))) 32
               (byte_of_nat (x*n))) O)
              3 20); clearbody K;
           normalize in K:(? ? (? ? %) ?);
           apply transitive_eq; [2: apply K | skip | ]; clear K;
           whd in ⊢ (? ? (? % ?) ?);
           normalize in ⊢ (? ? (? (? ? % ? ? ? ? ?) ?) ?);
           change in ⊢ (? ? (? (? % ? ? ? ? ? ?) ?) ?)
            with (byte_of_nat (S a));
           change in ⊢ (? ? (? (? ? ? ? (? ? %) ? ? ?) ?) ?) with
            (byte_of_nat (S a));
           (* instruction BEQ *)
           letin K ≝
            (breakpoint
              (mk_status (byte_of_nat (S a)) 6 O
               (eqbyte (mk_byte x0 x0) (byte_of_nat (S a)))
               (plusbytec (byte_of_nat (x*pred n)) x)
                (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (S a))) 32
                 (byte_of_nat (x*n))) O)
              3 17); clearbody K;
           normalize in K:(? ? (? ? %) ?);
           apply transitive_eq; [2: apply K | skip | ]; clear K;
           whd in ⊢ (? ? (? % ?) ?);
           letin K ≝ (eq_eqbyte_x0_x0_byte_of_nat_S_false ? H3); clearbody K;
           rewrite > K; clear K;
           simplify in ⊢ (? ? (? (? ? % ? ? ? ? ?) ?) ?);
           (* instruction LDAd *)
           letin K ≝
            (breakpoint
              (mk_status (byte_of_nat (S a)) 8 O
               (eqbyte (mk_byte x0 x0) (byte_of_nat (S a)))
               (plusbytec (byte_of_nat (x*pred n)) x)
                (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (S a))) 32
                 (byte_of_nat (x*n))) O)
              3 14); clearbody K;
           normalize in K:(? ? (? ? %) ?);
           apply transitive_eq; [2: apply K | skip | ]; clear K;
           whd in ⊢ (? ? (? % ?) ?);
           change in ⊢ (? ? (? (? % ? ? ? ? ? ?) ?) ?) with (byte_of_nat (x*n));
           normalize in ⊢ (? ? (? (? ? % ? ? ? ? ?) ?) ?);
           change in ⊢ (? ? (? (? ? ? ? % ? ? ?) ?) ?) with (eqbyte (mk_byte x0 x0) (byte_of_nat (x*n)));
           (* instruction DECd *)
           letin K ≝
            (breakpoint
             (mk_status (byte_of_nat (x*n)) 10 O
              (eqbyte (mk_byte x0 x0) (byte_of_nat (x*n)))
              (plusbytec (byte_of_nat (x*pred n)) x)
               (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (S a))) 32
                (byte_of_nat (x*n))) O)
             5 9); clearbody K;
           normalize in K:(? ? (? ? %) ?);
           apply transitive_eq; [2: apply K | skip | ]; clear K;
           whd in ⊢ (? ? (? % ?) ?);
           change in ⊢ (? ? (? (? ? ? ? (? ? %) ? ? ?) ?) ?) with (bpred (byte_of_nat (S a)));
           rewrite > (eq_bpred_S_a_a ? H3);
           normalize in ⊢ (? ? (? (? ? % ? ? ? ? ?) ?) ?);
           normalize in ⊢ (? ? (? (? ? ? ? ? ? (? ? % ?) ?) ?) ?);
           cut (y - S n = a);
            [2: elim daemon | ];
           rewrite < Hcut; clear Hcut; clear H3; clear H2; clear a;          
           (* instruction ADDd *)
           letin K ≝
            (breakpoint
             (mk_status (byte_of_nat (x*n)) 12
              O (eqbyte (mk_byte x0 x0) (byte_of_nat (y-S n)))
              (plusbytec (byte_of_nat (x*pred n)) x)
              (update
               (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (S (y-S n))))
               32 (byte_of_nat (x*n))) 31
               (byte_of_nat (y-S n))) O)
             3 6); clearbody K;
           normalize in K:(? ? (? ? %) ?);            
           apply transitive_eq; [2: apply K | skip | ]; clear K;
           whd in ⊢ (? ? (? % ?) ?);
           change in ⊢ (? ? (? (? % ? ? ? ? ? ?) ?) ?) with
            (plusbytenc (byte_of_nat (x*n)) x);
           change in ⊢ (? ? (? (? ? ? ? (? ? %) ? ? ?) ?) ?) with
            (plusbytenc (byte_of_nat (x*n)) x);
           normalize in ⊢ (? ? (? (? ? % ? ? ? ? ?) ?) ?);
           change in ⊢ (? ? (? (? ? ? ? ? % ? ?) ?) ?)
            with (plusbytec (byte_of_nat (x*n)) x);
           rewrite > plusbytenc_S;
           (* instruction STAd *)
           letin K ≝
            (breakpoint
             (mk_status (byte_of_nat (x*S n)) 14 O
              (eqbyte (mk_byte x0 x0) (byte_of_nat (x*S n)))
              (plusbytec (byte_of_nat (x*n)) x)
               (update
                (update (update (update (mult_memory x y) 30 x) 31 (byte_of_nat (S (y-S n))))
                32 (byte_of_nat (x*n))) 31
                (byte_of_nat (y-S n))) O)
            3 3); clearbody K;
           normalize in K:(? ? (? ? %) ?);            
           apply transitive_eq; [2: apply K | skip | ]; clear K;
           whd in ⊢ (? ? (? % ?) ?);
           normalize in ⊢ (? ? (? (? ? % ? ? ? ? ?) ?) ?);
           (* instruction BRA *)
           whd in ⊢ (? ? % ?);
           normalize in ⊢ (? ? (? ? % ? ? ? ? ?) ?);
           rewrite < pred_Sn;        
           apply status_eq;
            [1,2,3,4,7: normalize; reflexivity
            | change with (plusbytec (byte_of_nat (x*n)) x =
                             plusbytec (byte_of_nat (x*n)) x);
              reflexivity
            |6: intro;
              simplify in ⊢ (? ? ? %);
              change in ⊢ (? ? % ?) with
               (update
                (update
                 (update
                  (update (update (mult_memory x y) 30 x) 31
                   (byte_of_nat (S (nat_of_byte y-S n)))) 32 (byte_of_nat (nat_of_byte x*n))) 31
                    (byte_of_nat (nat_of_byte y-S n)))
                   (nat_of_byte
                    (update
                     (update
                      (update (update (mult_memory x y) 30 x) 31
                       (byte_of_nat (S (nat_of_byte y-S n)))) 32 (byte_of_nat (nat_of_byte x*n))) 31
                      (byte_of_nat (nat_of_byte y-S n)) 15))
                     (byte_of_nat (nat_of_byte x*S n)) a);
              normalize in ⊢ (? ? (? ? % ? ?) ?);
              apply inj_update;
              intro;
              apply inj_update;
              intro;
              rewrite > not_eq_a_b_to_eq_update_a_b in ⊢ (? ? % ?); [2: apply H | ];
              rewrite > not_eq_a_b_to_eq_update_a_b in ⊢ (? ? % ?);
               [ reflexivity
               | assumption
               ]
            ]
         | exists;
            [ apply (y - S n)
            | split;
               [ rewrite < (minus_S_S y n);
                 autobatch
               | letin K ≝ (lt_nat_of_byte_256 y); clearbody K;
                 letin K' ≝ (lt_minus_m y (S n) ? ?); clearbody K';
                 autobatch
               ]
            ]
         ]
      ]
    | rewrite > associative_plus;
      rewrite < times_n_Sm;
      rewrite > sym_plus in ⊢ (? ? ? (? ? %));
      reflexivity
    ] 
  ]   
qed.

theorem test_x_y:
 ∀x,y:byte.
  let i ≝ 14 + 23 * y in
   execute (mult_status x y) i =
    mk_status (byte_of_nat (x*y)) 20 0
     (eqbyte (mk_byte x0 x0) (byte_of_nat (x*y)))
     (plusbytec (byte_of_nat (x*pred y)) x)
     (update
       (update (mult_memory x y) 31 (mk_byte x0 x0))
       32 (byte_of_nat (x*y)))
     0.
 intros;
 cut (14 + 23 * y = 5 + 23*y + 9);
  [2: autobatch paramodulation;
  | rewrite > Hcut; (* clear Hcut; *)
    rewrite > (breakpoint (mult_status x y) (5 + 23*y) 9);
    rewrite > loop_invariant';
     [2: apply le_n
     | rewrite < minus_n_n;
       apply status_eq;
        [1,2,3,4,5,7: normalize; reflexivity
        | elim daemon
        ]
     ]
  ].
qed.
