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

set "baseuri" "cic:/matita/assembly/byte".

include "exadecimal.ma".

record byte : Type ≝ {
 bh: exadecimal;
 bl: exadecimal
}.

definition eqbyte ≝
 λb,b'. eqex (bh b) (bh b') ∧ eqex (bl b) (bl b').

definition plusbyte ≝
 λb1,b2,c.
  match plusex (bl b1) (bl b2) c with
   [ couple l c' ⇒
      match plusex (bh b1) (bh b2) c' with
       [ couple h c'' ⇒ couple ? ? (mk_byte h l) c'' ]].

definition nat_of_byte ≝ λb:byte. 16*(bh b) + (bl b).

coercion cic:/matita/assembly/byte/nat_of_byte.con.

definition byte_of_nat ≝
 λn. mk_byte (exadecimal_of_nat (n / 16)) (exadecimal_of_nat n).

lemma byte_of_nat_nat_of_byte: ∀b. byte_of_nat (nat_of_byte b) = b.
 intros;
 elim b;
 elim e;
 elim e1;
 reflexivity.
qed.

lemma lt_nat_of_byte_256: ∀b. nat_of_byte b < 256.
 intro;
 unfold nat_of_byte;
 letin H ≝ (lt_nat_of_exadecimal_16 (bh b)); clearbody H;
 letin K ≝ (lt_nat_of_exadecimal_16 (bl b)); clearbody K;
 unfold lt in H K ⊢ %;
 letin H' ≝ (le_S_S_to_le ? ? H); clearbody H'; clear H;
 letin K' ≝ (le_S_S_to_le ? ? K); clearbody K'; clear K;
 apply le_S_S;
 cut (16*bh b ≤ 16*15);
  [ letin Hf ≝ (le_plus ? ? ? ? Hcut K'); clearbody Hf;
    simplify in Hf:(? ? %);
    assumption
  | autobatch
  ]
qed.

lemma nat_of_byte_byte_of_nat: ∀n. nat_of_byte (byte_of_nat n) = n \mod 256.
 intro;
 letin H ≝ (lt_nat_of_byte_256 (byte_of_nat n)); clearbody H;
 rewrite < (lt_to_eq_mod ? ? H); clear H;
 unfold byte_of_nat;
 unfold nat_of_byte;
 change with ((16*(exadecimal_of_nat (n/16)) + exadecimal_of_nat n) \mod 256 = n \mod 256);
 letin H ≝ (div_mod n 16 ?); clearbody H; [ autobatch | ];
 rewrite > symmetric_times in H;
 rewrite > nat_of_exadecimal_exadecimal_of_nat in ⊢ (? ? (? (? % ?) ?) ?);
 rewrite > nat_of_exadecimal_exadecimal_of_nat in ⊢ (? ? (? (? ? %) ?) ?);
 rewrite > H in ⊢ (? ? ? (? % ?)); clear H;
 rewrite > mod_plus in ⊢ (? ? % ?);
 rewrite > mod_plus in ⊢ (? ? ? %);
 apply eq_mod_to_eq_plus_mod;
 rewrite < mod_mod in ⊢ (? ? ? %); [ | autobatch];
 rewrite < mod_mod in ⊢ (? ? % ?); [ | autobatch];
 rewrite < (eq_mod_times_times_mod ? ? 16 256) in ⊢ (? ? (? % ?) ?); [2: reflexivity | ];
 rewrite < mod_mod in ⊢ (? ? % ?);
  [ reflexivity
  | autobatch
  ].
qed.

axiom eq_nat_of_byte_n_nat_of_byte_mod_n_256:
 ∀n. byte_of_nat n = byte_of_nat (n \mod 256).

lemma plusbyte_ok:
 ∀b1,b2,c.
  match plusbyte b1 b2 c with
   [ couple r c' ⇒ b1 + b2 + nat_of_bool c = nat_of_byte r + nat_of_bool c' * 256
   ].
 intros;
 unfold plusbyte;
 generalize in match (plusex_ok (bl b1) (bl b2) c);
 elim (plusex (bl b1) (bl b2) c);
 simplify in H ⊢ %;
 generalize in match (plusex_ok (bh b1) (bh b2) t1);
 elim (plusex (bh b1) (bh b2) t1);
 simplify in H1 ⊢ %;
 change in ⊢ (? ? ? (? (? % ?) ?)) with (16 * t2);
 unfold nat_of_byte;
 letin K ≝ (eq_f ? ? (λy.16*y) ? ? H1); clearbody K; clear H1;
 rewrite > distr_times_plus in K:(? ? ? %);
 rewrite > symmetric_times in K:(? ? ? (? ? (? ? %)));
 rewrite < associative_times in K:(? ? ? (? ? %));
 normalize in K:(? ? ? (? ? (? % ?)));
 rewrite > symmetric_times in K:(? ? ? (? ? %));
 rewrite > sym_plus in ⊢ (? ? ? (? % ?));
 rewrite > associative_plus in ⊢ (? ? ? %);
 letin K' ≝ (eq_f ? ? (plus t) ? ? K); clearbody K'; clear K;
  apply transitive_eq; [3: apply K' | skip | ];
 clear K';
 rewrite > sym_plus in ⊢ (? ? (? (? ? %) ?) ?);
 rewrite > associative_plus in ⊢ (? ? (? % ?) ?);
 rewrite > associative_plus in ⊢ (? ? % ?);
 rewrite > associative_plus in ⊢ (? ? (? ? %) ?);
 rewrite > associative_plus in ⊢ (? ? (? ? (? ? %)) ?);
 rewrite > sym_plus in ⊢ (? ? (? ? (? ? (? ? %))) ?);
 rewrite < associative_plus in ⊢ (? ? (? ? (? ? %)) ?);
 rewrite < associative_plus in ⊢ (? ? (? ? %) ?);
 rewrite < associative_plus in ⊢ (? ? (? ? (? % ?)) ?);
 rewrite > H; clear H;
 autobatch paramodulation.
qed.

definition bpred ≝
 λb.
  match eqex (bl b) x0 with
   [ true ⇒ mk_byte (xpred (bh b)) (xpred (bl b))
   | false ⇒ mk_byte (bh b) (xpred (bl b))
   ]. 

lemma plusbyte_O_x:
 ∀b. plusbyte (mk_byte x0 x0) b false = couple ? ? b false.
 intros;
 elim b;
 elim e;
 elim e1;
 reflexivity.
qed.

definition plusbytenc ≝
 λx,y.
  match plusbyte x y false with
   [couple res _ ⇒ res].

definition plusbytec ≝
 λx,y.
  match plusbyte x y false with
   [couple _ c ⇒ c].

lemma plusbytenc_O_x:
 ∀x. plusbytenc (mk_byte x0 x0) x = x.
 intros;
 unfold plusbytenc;
 rewrite > plusbyte_O_x;
 reflexivity.
qed.

axiom eq_nat_of_byte_mod: ∀b. nat_of_byte b = nat_of_byte b \mod 256.

theorem plusbytenc_ok:
 ∀b1,b2:byte. nat_of_byte (plusbytenc b1 b2) = (b1 + b2) \mod 256.
 intros;
 unfold plusbytenc;
 generalize in match (plusbyte_ok b1 b2 false);
 elim (plusbyte b1 b2 false);
 simplify in H ⊢ %;
 change with (nat_of_byte t = (b1 + b2) \mod 256);
 rewrite < plus_n_O in H;
 rewrite > H; clear H;
 rewrite > mod_plus;
 letin K ≝ (eq_nat_of_byte_mod t); clearbody K;
 letin K' ≝ (eq_mod_times_n_m_m_O (nat_of_bool t1) 256 ?); clearbody K';
  [ autobatch | ];
 autobatch paramodulation.
qed.



lemma eq_eqbyte_x0_x0_byte_of_nat_S_false:
 ∀b. b < 255 → eqbyte (mk_byte x0 x0) (byte_of_nat (S b)) = false.
 intros;
 unfold byte_of_nat;
 cut (b < 15 ∨ b ≥ 15);
  [ elim Hcut;
    [ unfold eqbyte;
      change in ⊢ (? ? (? ? %) ?) with (eqex x0 (exadecimal_of_nat (S b))); 
      rewrite > eq_eqex_S_x0_false;
       [ elim (eqex (bh (mk_byte x0 x0))
(bh (mk_byte (exadecimal_of_nat (S b/16)) (exadecimal_of_nat (S b)))));simplify;
(*
 alias id "andb_sym" = "cic:/matita/nat/propr_div_mod_lt_le_totient1_aux/andb_sym.con".
         rewrite > andb_sym;
*)
         reflexivity
       | assumption
       ]
    | unfold eqbyte;
      change in ⊢ (? ? (? % ?) ?) with (eqex x0 (exadecimal_of_nat (S b/16)));
      letin K ≝ (leq_m_n_to_eq_div_n_m_S (S b) 16 ? ?);
       [ autobatch
       | unfold in H1;
         apply le_S_S;
         assumption
       | clearbody K;
         elim K; clear K;
         rewrite > H2;
         rewrite > eq_eqex_S_x0_false;
          [ reflexivity
          | unfold lt;
            unfold lt in H;
            rewrite < H2;
            clear H2; clear a; clear H1; clear Hcut;
            apply (le_times_to_le 16) [ autobatch | ] ;
            rewrite > (div_mod (S b) 16) in H;[2:autobatch|]
            rewrite > (div_mod 255 16) in H:(? ? %);[2:autobatch|]
            lapply (le_to_le_plus_to_le ? ? ? ? ? H);
            [apply lt_S_to_le;
             apply lt_mod_m_m;autobatch
            |rewrite > sym_times;
             rewrite > sym_times in ⊢ (? ? %); (* just to speed up qed *)
             normalize in \vdash (? ? %);apply Hletin;
            ]
          ] 
       ]
    ]
  | elim (or_lt_le b 15);unfold ge;autobatch
  ].
qed.

lemma eq_bpred_S_a_a:
 ∀a. a < 255 → bpred (byte_of_nat (S a)) = byte_of_nat a.
elim daemon. (*
 intros;
 unfold byte_of_nat;
 cut (a \mod 16 = 15 ∨ a \mod 16 < 15);
  [ elim Hcut;
     [ 
     |
     ]
  | autobatch
  ].*)
qed.
 
lemma plusbytenc_S:
 ∀x:byte.∀n.plusbytenc (byte_of_nat (x*n)) x = byte_of_nat (x * S n).
 intros;
 rewrite < byte_of_nat_nat_of_byte;
 rewrite > (plusbytenc_ok (byte_of_nat (x*n)) x);
 rewrite < times_n_Sm;
 rewrite > mod_plus;
 rewrite < eq_nat_of_byte_mod in ⊢ (? ? (? (? (? ? %) ?)) ?);
 rewrite > nat_of_byte_byte_of_nat;
 rewrite < mod_mod in ⊢ (? ? (? (? (? % ?) ?)) ?);
elim daemon.
qed. 

lemma eq_plusbytec_x0_x0_x_false:
 ∀x.plusbytec (mk_byte x0 x0) x = false.
 intro;
 elim x;
 elim e;
 elim e1;
 reflexivity.
qed.
