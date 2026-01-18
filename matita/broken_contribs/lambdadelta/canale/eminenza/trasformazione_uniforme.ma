(* Questo documento fa parte della libreria digitale HELM (http://helm.cs.unibo.it)
   ed è distribuito ai sensi della licenza GNU GPL versione 2
*)

include "ground/arith/nat_rplus_succ.ma".
include "ground/notation/functions/element_u_1.ma".
include "canale/eminenza/trasformazione.ma".

(* Trasformazione uniforme dei rifeimenti ***********************************)

definition rt_uni (n) (r): ℝ ≝
match r with
[ NRef x ⇒ x
| DRef i ⇒ ⧣(i+n)
].

interpretation
  "uniforme (trasformazione)"
  'ElementU n = (rt_uni n).

(* Riscritture di base ******************************************************)

lemma rt_uni_nref (n) (x:𝕍):
      x =❪ℝ❫ 𝐮❨n❩ @ x.
//
qed.

lemma rt_uni_dref (n) (i):
      (⧣(i+n)) =❪ℝ❫ 𝐮❨n❩ @ ⧣i.
//
qed.

(* Riscritture avanzate *****************************************************)

lemma rt_uni_zero (r):
      r = 𝐮❨𝟎❩ @ r.
* //
qed.

(* Riscritture principali ***************************************************)

theorem rt_uni_iniettiva (n):
        rt_iniettiva @  𝐮❨n❩.
#n * [ #x1 <rt_uni_nref | #i1 <rt_uni_dref ] 
* [1,3: #x2 <rt_uni_nref |*: #i2 <rt_uni_dref ]
#H0 destruct // -e0 (**) (* destruct fallisce *)
lapply (eq_inv_dref_bi … H0) -H0 #H0
<(eq_inv_nrplus_bi_dx … H0) -H0 //
qed-.

(* Inversioni avanzate ******************************************************)

lemma neq_rt_uni_unit_dx (r):
      (⧣𝟏) ⧸= 𝐮❨⁤𝟏❩ @ r.
* [ #x <rt_uni_nref | #i <rt_uni_dref ] #H0 destruct -H0
<nrplus_unit_dx in e0; #H0 destruct
qed-.
