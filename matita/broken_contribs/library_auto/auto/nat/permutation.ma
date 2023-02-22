(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/library_autobatch/nat/permutation".

include "auto/nat/compare.ma".
include "auto/nat/sigma_and_pi.ma".

definition injn: (nat \to nat) \to nat \to Prop \def
\lambda f:nat \to nat.\lambda n:nat.\forall i,j:nat. 
i \le n \to j \le n \to f i = f j \to i = j.

theorem injn_Sn_n: \forall f:nat \to nat. \forall n:nat.
injn f (S n) \to injn f n.
unfold injn.
intros.
apply H;autobatch.
(*[ apply le_S.
  assumption
| apply le_S.
  assumption
| assumption
]*)
qed.

theorem injective_to_injn: \forall f:nat \to nat. \forall n:nat.
injective nat nat f \to injn f n.
unfold injective.
unfold injn.
intros.autobatch.
(*apply H.
assumption.*)
qed.

definition permut : (nat \to nat) \to nat \to Prop 
\def \lambda f:nat \to nat. \lambda m:nat.
(\forall i:nat. i \le m \to f i \le m )\land injn f m.

theorem permut_O_to_eq_O: \forall h:nat \to nat.
permut h O \to (h O) = O.
intros.
unfold permut in H.
elim H.
apply sym_eq.autobatch.
(*apply le_n_O_to_eq.
apply H1.
apply le_n.*)
qed.

theorem permut_S_to_permut: \forall f:nat \to nat. \forall m:nat.
permut f (S m) \to f (S m) = (S m) \to permut f m.
unfold permut.
intros.
elim H.
split
[ intros.
  cut (f i < S m \lor f i = S m)
  [ elim Hcut
    [ autobatch
      (*apply le_S_S_to_le.
      assumption*)
    | apply False_ind.
      apply (not_le_Sn_n m).
      cut ((S m) = i)
      [ rewrite > Hcut1.
        assumption
      | apply H3
        [ apply le_n
        | autobatch
          (*apply le_S.
          assumption*)
        | autobatch
          (*rewrite > H5.
          assumption*)
        ]
      ]
    ]
  | apply le_to_or_lt_eq.
    autobatch
    (*apply H2.
    apply le_S.
    assumption*)
  ]
| apply (injn_Sn_n f m H3)
]
qed.

(* transpositions *)

definition transpose : nat \to nat \to nat \to nat \def
\lambda i,j,n:nat.
match eqb n i with
  [ true \Rightarrow j
  | false \Rightarrow 
      match eqb n j with
      [ true \Rightarrow i
      | false \Rightarrow n]].

notation < "(❲i↹j❳)n"
  right associative with precedence 71 
for @{ 'transposition $i $j $n}.

notation < "(❲i \atop j❳)n"
  right associative with precedence 71 
for @{ 'transposition $i $j $n}.

interpretation "natural transposition" 'transposition i j n = (transpose i j n).

lemma transpose_i_j_i: \forall i,j:nat. transpose i j i = j.
intros.
unfold transpose.
(*dopo circa 6 minuti, l'esecuzione di autobatch in questo punto non era ancora terminata*)
rewrite > (eqb_n_n i).autobatch.
(*simplify.
reflexivity.*)
qed.

lemma transpose_i_j_j: \forall i,j:nat. transpose i j j = i.
intros.
unfold transpose.
apply (eqb_elim j i)
[ autobatch
  (*simplify.
  intro.
  assumption*)
| rewrite > (eqb_n_n j).
  simplify.
  intros.
  reflexivity
]
qed.
      
theorem transpose_i_i:  \forall i,n:nat. (transpose  i i n) = n.
intros.
unfold transpose.
apply (eqb_elim n i)
[ autobatch
  (*intro.
  simplify.
  apply sym_eq. 
  assumption*)
| intro.
  autobatch
  (*simplify.
  reflexivity*)
]
qed.

theorem transpose_i_j_j_i: \forall i,j,n:nat.
transpose i j n = transpose j i n.
intros.
unfold transpose.
apply (eqb_elim n i)
[ apply (eqb_elim n j)
  [ intros.
    (*l'esecuzione di autobatch in questo punto, dopo circa 300 secondi, non era ancora terminata*)
    simplify.autobatch
    (*rewrite < H.
    rewrite < H1.
    reflexivity*)
  | intros.
    autobatch
    (*simplify.
    reflexivity*)
  ]
| apply (eqb_elim n j)
  [ intros.autobatch
    (*simplify.reflexivity *) 
  | intros.autobatch
    (*simplify.reflexivity*)
  ]
]
qed.

theorem transpose_transpose: \forall i,j,n:nat.
(transpose i j (transpose i j n)) = n.
intros.
unfold transpose.
unfold transpose.
apply (eqb_elim n i)
[ simplify.
  intro.
  apply (eqb_elim j i)
  [ simplify.
    intros.
    autobatch
    (*rewrite > H.
    rewrite > H1.
    reflexivity*)
  | rewrite > (eqb_n_n j).
    simplify.
    intros.
    autobatch
    (*apply sym_eq.
    assumption*)
  ]
| apply (eqb_elim n j)
  [ simplify.
    rewrite > (eqb_n_n i).
    intros.
    autobatch
    (*simplify.
    apply sym_eq.
    assumption*)
  | simplify.
    intros.
    (*l'esecuzione di autobatch in questo punto, dopo piu' di 6 minuti non era ancora terminata*)
    rewrite > (not_eq_to_eqb_false n i H1).
    (*l'esecuzione di autobatch in questo punto, dopo piu' alcuni minuti non era ancora terminata*)
    rewrite > (not_eq_to_eqb_false n j H).autobatch
    (*simplify.
    reflexivity*)
  ]
]
qed.

theorem injective_transpose : \forall i,j:nat. 
injective nat nat (transpose i j).
unfold injective.
intros.autobatch.
(*rewrite < (transpose_transpose i j x).
rewrite < (transpose_transpose i j y).
apply eq_f.
assumption.*)
qed.

variant inj_transpose: \forall i,j,n,m:nat.
transpose i j n = transpose i j m \to n = m \def
injective_transpose.

theorem permut_transpose: \forall i,j,n:nat. i \le n \to j \le n \to
permut (transpose i j) n.
unfold permut.
intros.
split
[ unfold transpose.
  intros.
  elim (eqb i1 i)
  [ (*qui autobatch non chiude il goal*)
    simplify.
    assumption
  | elim (eqb i1 j)
    [ (*aui autobatch non chiude il goal*)
      simplify.
      assumption    
    | (*aui autobatch non chiude il goal*)
      simplify.
      assumption
    ]
  ]
| autobatch
  (*apply (injective_to_injn (transpose i j) n).
  apply injective_transpose*)
]
qed.

theorem permut_fg: \forall f,g:nat \to nat. \forall n:nat.
permut f n \to permut g n \to permut (\lambda m.(f(g m))) n.
unfold permut.
intros.
elim H.
elim H1.
split
[ intros.
  simplify.
  autobatch
  (*apply H2.
  apply H4.
  assumption*)
| simplify.
  intros.
  apply H5
  [ assumption
  | assumption
  | apply H3
    [ autobatch
      (*apply H4.
      assumption*)
    | autobatch
      (*apply H4.
      assumption*)
    | assumption
    ]
  ]
]
qed.

theorem permut_transpose_l: 
\forall f:nat \to nat. \forall m,i,j:nat.
i \le m \to j \le m \to permut f m \to permut (\lambda n.transpose i j (f n)) m.  
intros.
autobatch.
(*apply (permut_fg (transpose i j) f m ? ?)
[ apply permut_transpose;assumption
| assumption
]*)
qed.

theorem permut_transpose_r: 
\forall f:nat \to nat. \forall m,i,j:nat.
i \le m \to j \le m \to permut f m \to permut (\lambda n.f (transpose i j n)) m.  
intros.autobatch.
(*apply (permut_fg f (transpose i j) m ? ?)
[ assumption
| apply permut_transpose;assumption
]*)
qed.

theorem eq_transpose : \forall i,j,k,n:nat. \lnot j=i \to
 \lnot i=k \to \lnot j=k \to
transpose i j n = transpose i k (transpose k j (transpose i k n)).
(* uffa: triplo unfold? *)
intros.unfold transpose.
unfold transpose.
unfold transpose.
apply (eqb_elim n i)
[ intro.
  simplify.
  rewrite > (eqb_n_n k).
  simplify.
  rewrite > (not_eq_to_eqb_false j i H).
  rewrite > (not_eq_to_eqb_false j k H2).
  reflexivity
| intro.
  apply (eqb_elim n j)
  [ intro.
    cut (\lnot n = k)
    [ cut (\lnot n = i)
      [ rewrite > (not_eq_to_eqb_false n k Hcut).
        simplify.
        rewrite > (not_eq_to_eqb_false n k Hcut).
        rewrite > (eq_to_eqb_true n j H4).
        simplify.
        rewrite > (not_eq_to_eqb_false k i)
        [ rewrite > (eqb_n_n k).
          autobatch
          (*simplify.
          reflexivity*)
        | unfold Not.
          intro.autobatch
          (*apply H1.
          apply sym_eq.
          assumption*)
        ]
      | assumption
      ]
    | unfold Not.
      intro.autobatch
      (*apply H2.
      apply (trans_eq ? ? n)
      [ apply sym_eq.
        assumption
      | assumption
      ]*)
    ]
  | intro.
    apply (eqb_elim n k)
    [ intro.
      simplify.
      rewrite > (not_eq_to_eqb_false i k H1).
      rewrite > (not_eq_to_eqb_false i j)
      [ simplify.
        rewrite > (eqb_n_n i).
        autobatch
        (*simplify.
        assumption*)
      | unfold Not.
        intro.autobatch       
        (*apply H.
        apply sym_eq.
        assumption*)
      ]
    | intro.
      simplify.
      rewrite > (not_eq_to_eqb_false n k H5).
      rewrite > (not_eq_to_eqb_false n j H4).
      simplify.
      rewrite > (not_eq_to_eqb_false n i H3).
      rewrite > (not_eq_to_eqb_false n k H5).
      autobatch
      (*simplify.
      reflexivity*)
    ]
  ]
] 
qed.

theorem permut_S_to_permut_transpose: \forall f:nat \to nat. 
\forall m:nat. permut f (S m) \to permut (\lambda n.transpose (f (S m)) (S m)
(f n)) m.
unfold permut.
intros.
elim H.
split
[ intros.
  simplify.
  unfold transpose.
  apply (eqb_elim (f i) (f (S m)))
  [ intro.
    apply False_ind.
    cut (i = (S m))
    [ apply (not_le_Sn_n m).
      rewrite < Hcut.
      assumption
    | apply H2;autobatch
      (*[ apply le_S.
        assumption
      | apply le_n
      | assumption
      ]*)
    ]
  | intro.
    simplify.
    apply (eqb_elim (f i) (S m))
    [ intro.
      cut (f (S m) \lt (S m) \lor f (S m) = (S m))
      [ elim Hcut
        [ apply le_S_S_to_le.
          (*NB qui autobatch non chiude il goal*)
          assumption
        | apply False_ind.
          autobatch
          (*apply H4.
          rewrite > H6.
          assumption*)
        ]
      | autobatch
        (*apply le_to_or_lt_eq.
        apply H1.
        apply le_n*)
      ]
    | intro.simplify.
      cut (f i \lt (S m) \lor f i = (S m))
      [ elim Hcut
        [ autobatch
          (*apply le_S_S_to_le.
          assumption*)
        | apply False_ind.
          autobatch
          (*apply H5.
          assumption*)
        ]
      | apply le_to_or_lt_eq.
        autobatch
        (*apply H1.
        apply le_S.
        assumption*)
      ]
    ]
  ]
| unfold injn.
  intros.  
  apply H2;autobatch
  (*[ apply le_S.
    assumption
  | apply le_S.
    assumption
  | apply (inj_transpose (f (S m)) (S m)).
    apply H5
  ]*)
]
qed.

(* bounded bijectivity *)

definition bijn : (nat \to nat) \to nat \to Prop \def
\lambda f:nat \to nat. \lambda n. \forall m:nat. m \le n \to
ex nat (\lambda p. p \le n \land f p = m).

theorem eq_to_bijn:  \forall f,g:nat\to nat. \forall n:nat.
(\forall i:nat. i \le n \to (f i) = (g i)) \to 
bijn f n \to bijn g n.
intros 4.
unfold bijn.
intros.
elim (H1 m)
[ apply (ex_intro ? ? a).
  rewrite < (H a)
  [ assumption
  | elim H3.
    assumption
  ]
| assumption
]
qed.

theorem bijn_Sn_n: \forall f:nat \to nat. \forall n:nat.
bijn f (S n) \to f (S n) = (S n) \to bijn f n.
unfold bijn.
intros.
elim (H m)
[ elim H3.
  apply (ex_intro ? ? a).
  split
  [ cut (a < S n \lor a = S n)
    [ elim Hcut
      [ autobatch
        (*apply le_S_S_to_le.
        assumption*)
      | apply False_ind.
        apply (not_le_Sn_n n).
        rewrite < H1.
        rewrite < H6.
        rewrite > H5.
        assumption      
      ]
    | autobatch
      (*apply le_to_or_lt_eq.
      assumption*)
    ]
  | assumption
  ]
| autobatch
  (*apply le_S.
  assumption*)
]
qed.

theorem bijn_n_Sn: \forall f:nat \to nat. \forall n:nat.
bijn f n \to f (S n) = (S n) \to bijn f (S n).
unfold bijn.
intros.
cut (m < S n \lor m = S n)
[ elim Hcut
  [ elim (H m)
    [ elim H4.
      apply (ex_intro ? ? a).
      autobatch
      (*split 
      [ apply le_S.
        assumption
      | assumption
      ]*)
    | autobatch
      (*apply le_S_S_to_le.
      assumption*)
    ]
  | autobatch
    (*apply (ex_intro ? ? (S n)).
    split
    [ apply le_n
    | rewrite > H3.
      assumption
    ]*)
  ]
| autobatch
  (*apply le_to_or_lt_eq.
  assumption*)
]
qed.

theorem bijn_fg: \forall f,g:nat\to nat. \forall n:nat.
bijn f n \to bijn g n \to bijn (\lambda p.f(g p)) n.
unfold bijn.
intros.
simplify.
elim (H m)
[ elim H3.
  elim (H1 a)
  [ elim H6.
    autobatch
    (*apply (ex_intro ? ? a1).
    split
    [ assumption
    | rewrite > H8.
      assumption
    ]*)
  | assumption
  ]
| assumption
]
qed.

theorem bijn_transpose : \forall n,i,j. i \le n \to j \le n \to
bijn (transpose i j) n.
intros.
unfold bijn.
unfold transpose.
intros.
cut (m = i \lor \lnot m = i)
[ elim Hcut
  [ apply (ex_intro ? ? j).
    split
    [ assumption
    | apply (eqb_elim j i)
      [ intro.
        (*dopo circa 360 secondi l'esecuzione di autobatch in questo punto non era ancora terminata*)
        simplify.
        autobatch
        (*rewrite > H3.
        rewrite > H4.
        reflexivity*)
      | rewrite > (eqb_n_n j).
        simplify.
        intros.
        autobatch
        (*apply sym_eq.
        assumption*)
      ]
    ]
  | cut (m = j \lor \lnot m = j)
    [ elim Hcut1
      [ apply (ex_intro ? ? i).
        split
        [ assumption
        | (*dopo circa 5 minuti, l'esecuzione di autobatch in questo punto non era ancora terminata*)
          rewrite > (eqb_n_n i).
          autobatch
          (*simplify.
          apply sym_eq. 
          assumption*)
        ]
      | apply (ex_intro ? ? m).
        split
        [ assumption
        | rewrite > (not_eq_to_eqb_false m i)
          [ (*dopo circa 5 minuti, l'esecuzione di autobatch in questo punto non era ancora terminata*)
            rewrite > (not_eq_to_eqb_false m j)
            [ autobatch
              (*simplify. 
              reflexivity*)
            | assumption
            ]
          | assumption
          ]
        ]
      ]
    | apply (decidable_eq_nat m j)
    ]
  ]
| apply (decidable_eq_nat m i)
]
qed.

theorem bijn_transpose_r: \forall f:nat\to nat.\forall n,i,j. i \le n \to j \le n \to
bijn f n \to bijn (\lambda p.f (transpose i j p)) n.
intros.autobatch.
(*apply (bijn_fg f ?)
[ assumption
| apply (bijn_transpose n i j)
  [ assumption
  | assumption
  ]
]*)
qed.

theorem bijn_transpose_l: \forall f:nat\to nat.\forall n,i,j. i \le n \to j \le n \to
bijn f n \to bijn (\lambda p.transpose i j (f p)) n.
intros.
autobatch.
(*apply (bijn_fg ? f)
[ apply (bijn_transpose n i j)
  [ assumption
  | assumption
  ]
| assumption
]*)
qed.

theorem permut_to_bijn: \forall n:nat.\forall f:nat\to nat.
permut f n \to bijn f n.
intro.
elim n
[ unfold bijn.
  intros.
  apply (ex_intro ? ? m).
  split
  [ assumption
  | apply (le_n_O_elim m ? (\lambda p. f p = p))
    [ assumption
    | unfold permut in H.
      elim H.
      apply sym_eq.
      autobatch
      (*apply le_n_O_to_eq.
      apply H2.
      apply le_n*)
    ]
  ]
| apply (eq_to_bijn (\lambda p.
  (transpose (f (S n1)) (S n1)) (transpose (f (S n1)) (S n1) (f p))) f)
  [ intros.
    apply transpose_transpose
  | apply (bijn_fg (transpose (f (S n1)) (S n1)))
    [ apply bijn_transpose
      [ unfold permut in H1.
        elim H1.autobatch
        (*apply H2.
        apply le_n*)
      | apply le_n
      ]
    | apply bijn_n_Sn
      [ apply H.
        autobatch
        (*apply permut_S_to_permut_transpose.
        assumption*)
      | autobatch
        (*unfold transpose.
        rewrite > (eqb_n_n (f (S n1))).
        simplify.
        reflexivity*)
      ]
    ]
  ]
]
qed.

let rec invert_permut n f m \def
  match eqb m (f n) with
  [true \Rightarrow n
  |false \Rightarrow 
     match n with
     [O \Rightarrow O
     |(S p) \Rightarrow invert_permut p f m]].

theorem invert_permut_f: \forall f:nat \to nat. \forall n,m:nat.
m \le n \to injn f n\to invert_permut n f (f m) = m.
intros 4.
elim H
[ apply (nat_case1 m)
  [ intro.
    simplify.
    (*l'applicazione di autobatch in questo punto, dopo alcuni minuti, non aveva ancora dato risultati*)
    rewrite > (eqb_n_n (f O)).
    autobatch
    (*simplify.
    reflexivity*)
  | intros.simplify.
    (*l'applicazione di autobatch in questo punto, dopo alcuni minuti, non aveva ancora dato risultati*)
    rewrite > (eqb_n_n (f (S m1))).
    autobatch
    (*simplify.
    reflexivity*)
  ]
| simplify.
  rewrite > (not_eq_to_eqb_false (f m) (f (S n1)))
  [ (*l'applicazione di autobatch in questo punto, dopo parecchi secondi, non aveva ancora prodotto un risultato*)
    simplify.
    autobatch
    (*apply H2.
    apply injn_Sn_n.
    assumption*)
  | unfold Not.
    intro.
    absurd (m = S n1)
    [ apply H3;autobatch
      (*[ apply le_S.
        assumption
      | apply le_n
      | assumption
      ]*)
    | unfold Not.
      intro.
      apply (not_le_Sn_n n1).
      rewrite < H5.
      assumption
    ]
  ]
]
qed.

theorem injective_invert_permut: \forall f:nat \to nat. \forall n:nat.
permut f n \to injn (invert_permut n f) n.
intros.
unfold injn.
intros.
cut (bijn f n)
[ unfold bijn in Hcut.
  generalize in match (Hcut i H1).
  intro.
  generalize in match (Hcut j H2).
  intro.
  elim H4.
  elim H6.
  elim H5.
  elim H9.
  rewrite < H8.
  rewrite < H11.
  apply eq_f.
  rewrite < (invert_permut_f f n a)
  [ rewrite < (invert_permut_f f n a1)
    [ rewrite > H8.
      rewrite > H11.
      assumption
    | assumption
    | unfold permut in H.elim H.
      assumption
    ]
  | assumption
  | unfold permut in H.
    elim H.
    assumption
  ]
| autobatch
  (*apply permut_to_bijn.
  assumption*)
]
qed.

theorem permut_invert_permut: \forall f:nat \to nat. \forall n:nat.
permut f n \to permut (invert_permut n f) n.
intros.
unfold permut.
split
[ intros.
  simplify.
  elim n
  [ simplify.
    elim (eqb i (f O));autobatch
    (*[ simplify.
      apply le_n
    | simplify.
      apply le_n
    ]*)
  | simplify.
    elim (eqb i (f (S n1)))
    [ autobatch
      (*simplify.
      apply le_n*)
    | simplify.
      autobatch
      (*apply le_S.
      assumption*)
    ]
  ]
| autobatch
  (*apply injective_invert_permut.
  assumption.*)
]
qed.

theorem f_invert_permut: \forall f:nat \to nat. \forall n,m:nat.
m \le n \to permut f n\to f (invert_permut n f m) = m.
intros.
apply (injective_invert_permut f n H1)
[ unfold permut in H1.
  elim H1.
  apply H2.
  cut (permut (invert_permut n f) n)
  [ unfold permut in Hcut.
    elim Hcut.autobatch    
    (*apply H4.
    assumption*)
  | apply permut_invert_permut.
    (*NB qui autobatch non chiude il goal*)
    assumption
  ]
| assumption
| apply invert_permut_f
  [ cut (permut (invert_permut n f) n)
    [ unfold permut in Hcut.
      elim Hcut.
      autobatch
      (*apply H2.
      assumption*)
    | autobatch
      (*apply permut_invert_permut.
      assumption*)
    ]
  | unfold permut in H1.
    elim H1.
    assumption
  ]
]
qed.

theorem permut_n_to_eq_n: \forall h:nat \to nat.\forall n:nat.
permut h n \to (\forall m:nat. m < n \to h m = m) \to h n = n.
intros.
unfold permut in H.
elim H.
cut (invert_permut n h n < n \lor invert_permut n h n = n)
[ elim Hcut
  [ rewrite < (f_invert_permut h n n) in \vdash (? ? ? %)
    [ apply eq_f.
      rewrite < (f_invert_permut h n n) in \vdash (? ? % ?)
      [ autobatch
        (*apply H1.
        assumption*)
      | apply le_n
      | (*qui autobatch NON chiude il goal*)
        assumption
      ]
    | apply le_n
    | (*qui autobatch NON chiude il goal*)
      assumption
    ]
  | rewrite < H4 in \vdash (? ? % ?).
    apply (f_invert_permut h)
    [ apply le_n
    | (*qui autobatch NON chiude il goal*)
      assumption
    ]
  ]
| apply le_to_or_lt_eq.
  cut (permut (invert_permut n h) n)
  [ unfold permut in Hcut.
    elim Hcut.
    autobatch
    (*apply H4.
    apply le_n*)
  | apply permut_invert_permut.
    (*NB aui autobatch non chiude il goal*)
    assumption
  ]
]
qed.

theorem permut_n_to_le: \forall h:nat \to nat.\forall k,n:nat.
k \le n \to permut h n \to (\forall m:nat. m < k \to h m = m) \to 
\forall j. k \le j \to j \le n \to k \le h j.
intros.
unfold permut in H1.
elim H1.
cut (h j < k \lor \not(h j < k))
[ elim Hcut
  [ absurd (k \le j)
    [ assumption
    | apply lt_to_not_le.
      cut (h j = j)
      [ rewrite < Hcut1.
        assumption
      | apply H6;autobatch
        (*[ apply H5.
          assumption
        | assumption  
        | apply H2.
          assumption          
        ]*)
      ]
    ]
  | autobatch
    (*apply not_lt_to_le.
    assumption*)
  ]
| apply (decidable_lt (h j) k)
]
qed.

(* applications *)

let rec map_iter_i k (g:nat \to nat) f (i:nat) \def
  match k with
   [ O \Rightarrow g i
   | (S k) \Rightarrow f (g (S (k+i))) (map_iter_i k g f i)].

theorem eq_map_iter_i: \forall g1,g2:nat \to nat.
\forall f:nat \to nat \to nat. \forall n,i:nat.
(\forall m:nat. i\le m \to m \le n+i \to g1 m = g2 m) \to 
map_iter_i n g1 f i = map_iter_i n g2 f i.
intros 5.
elim n
[ simplify.
  autobatch
  (*apply H
  [ apply le_n
  | apply le_n
  ]*)
| simplify.
  apply eq_f2
  [ autobatch
    (*apply H1
    [ simplify.
      apply le_S.
      apply le_plus_n
    | simplify.
      apply le_n
    ]*)
  | apply H.
    intros.
    apply H1;autobatch
    (*[ assumption
    | simplify.
      apply le_S. 
      assumption
    ]*)
  ]
]
qed.

(* map_iter examples *)

theorem eq_map_iter_i_sigma: \forall g:nat \to nat. \forall n,m:nat. 
map_iter_i n g plus m = sigma n g m.
intros.
elim n
[ autobatch
  (*simplify.
  reflexivity*)
| simplify.
  autobatch
  (*apply eq_f.
  assumption*)
]
qed.

theorem eq_map_iter_i_pi: \forall g:nat \to nat. \forall n,m:nat. 
map_iter_i n g times m = pi n g m.
intros.
elim n
[ autobatch
  (*simplify.
  reflexivity*)
| simplify.
  autobatch
  (*apply eq_f.
  assumption*)
]
qed.

theorem eq_map_iter_i_fact: \forall n:nat. 
map_iter_i n (\lambda m.m) times (S O) = (S n)!.
intros.
elim n
[ autobatch
  (*simplify.
  reflexivity*)
| change with 
  (((S n1)+(S O))*(map_iter_i n1 (\lambda m.m) times (S O)) = (S(S n1))*(S n1)!).
  rewrite < plus_n_Sm.
  rewrite < plus_n_O.
  apply eq_f.
  (*NB: qui autobatch non chiude il goal!!!*)
  assumption
]
qed.


theorem eq_map_iter_i_transpose_l : \forall f:nat\to nat \to nat.associative nat f \to
symmetric2 nat nat f \to \forall g:nat \to nat. \forall n,k:nat. 
map_iter_i (S k) g f n = map_iter_i (S k) (\lambda m. g (transpose (k+n) (S k+n) m)) f n.
intros.
apply (nat_case1 k)
[ intros.
  simplify.
  fold simplify (transpose n (S n) (S n)).
  autobatch
  (*rewrite > transpose_i_j_i.
  rewrite > transpose_i_j_j.
  apply H1*)
| intros.
  change with 
  (f (g (S (S (m+n)))) (f (g (S (m+n))) (map_iter_i m g f n)) = 
  f (g (transpose (S m + n) (S (S m) + n) (S (S m)+n))) 
  (f (g (transpose (S m + n) (S (S m) + n) (S m+n))) 
  (map_iter_i m (\lambda m1. g (transpose (S m+n) (S (S m)+n) m1)) f n))).
  rewrite > transpose_i_j_i.
  rewrite > transpose_i_j_j.
  rewrite < H.
  rewrite < H.
  rewrite < (H1 (g (S m + n))).
  apply eq_f.
  apply eq_map_iter_i.
  intros.
  simplify.
  unfold transpose.
  rewrite > (not_eq_to_eqb_false m1 (S m+n))
  [ rewrite > (not_eq_to_eqb_false m1 (S (S m)+n))
    [ autobatch
      (*simplify.
      reflexivity*)
    | apply (lt_to_not_eq m1 (S ((S m)+n))).
      autobatch
      (*unfold lt.
      apply le_S_S.
      change with (m1 \leq S (m+n)).
      apply le_S.
      assumption*)
    ]
  | apply (lt_to_not_eq m1 (S m+n)).
    simplify.autobatch
    (*unfold lt.
    apply le_S_S.
    assumption*)
  ]
]
qed.

theorem eq_map_iter_i_transpose_i_Si : \forall f:nat\to nat \to nat.associative nat f \to
symmetric2 nat nat f \to \forall g:nat \to nat. \forall n,k,i:nat. n \le i \to i \le k+n \to
map_iter_i (S k) g f n = map_iter_i (S k) (\lambda m. g (transpose i (S i) m)) f n.
intros 6.
elim k
[ cut (i=n)
  [ rewrite > Hcut.
    (*qui autobatch non chiude il goal*)
    apply (eq_map_iter_i_transpose_l f H H1 g n O)
  | apply antisymmetric_le
    [ assumption
    | assumption
    ]
  ]
| cut (i < S n1 + n \lor i = S n1 + n)
  [ elim Hcut
    [ change with 
      (f (g (S (S n1)+n)) (map_iter_i (S n1) g f n) = 
      f (g (transpose i (S i) (S (S n1)+n))) (map_iter_i (S n1) (\lambda m. g (transpose i (S i) m)) f n)).
      apply eq_f2
      [ unfold transpose.
        rewrite > (not_eq_to_eqb_false (S (S n1)+n) i)
        [ rewrite > (not_eq_to_eqb_false (S (S n1)+n) (S i))
          [ autobatch
            (*simplify.
            reflexivity*)
          | simplify.
            unfold Not.
            intro.    
            apply (lt_to_not_eq i (S n1+n))
            [ assumption
            | autobatch
              (*apply inj_S.
              apply sym_eq.
              assumption*)
            ]
          ]
        | simplify.
          unfold Not.
          intro.
          apply (lt_to_not_eq i (S (S n1+n)))
          [ autobatch
            (*simplify.
            unfold lt.
            apply le_S_S.
            assumption*)
          | autobatch
            (*apply sym_eq.
            assumption*)
          ]
        ]
      | apply H2;autobatch
        (*[ assumption
        | apply le_S_S_to_le.
          assumption
        ]*)
      ]
    | rewrite > H5.
      (*qui autobatch non chiude il goal*)
      apply (eq_map_iter_i_transpose_l f H H1 g n (S n1)).     
    ]
  | autobatch
    (*apply le_to_or_lt_eq.
    assumption*)
  ]
]
qed.

theorem eq_map_iter_i_transpose: 
\forall f:nat\to nat \to nat.
associative nat f \to symmetric2 nat nat f \to \forall n,k,o:nat. 
\forall g:nat \to nat. \forall i:nat. n \le i \to S (o + i) \le S k+n \to  
map_iter_i (S k) g  f n = map_iter_i (S k) (\lambda m. g (transpose i (S(o + i)) m)) f n.
intros 6.
apply (nat_elim1 o).
intro.
apply (nat_case m ?)
[ intros.
  apply (eq_map_iter_i_transpose_i_Si ? H H1);autobatch
  (*[ exact H3
  | apply le_S_S_to_le.
    assumption
  ]*)
| intros.
  apply (trans_eq ? ? (map_iter_i (S k) (\lambda m. g (transpose i (S(m1 + i)) m)) f n))
  [ apply H2
    [ autobatch
      (*unfold lt.
      apply le_n*)
    | assumption
    | apply (trans_le ? (S(S (m1+i))))
      [ autobatch
        (*apply le_S.
        apply le_n*)
      | (*qui autobatch non chiude il goal, chiuso invece da assumption*)
        assumption
      ]
    ]
  | apply (trans_eq ? ? (map_iter_i (S k) (\lambda m. g 
    (transpose i (S(m1 + i)) (transpose (S(m1 + i)) (S(S(m1 + i))) m))) f n))
    [ (*qui autobatch dopo alcuni minuti non aveva ancora terminato la propria esecuzione*)
      apply (H2 O ? ? (S(m1+i)))
      [ autobatch
        (*unfold lt.
        apply le_S_S.
        apply le_O_n*)
      | autobatch
        (*apply (trans_le ? i)
        [ assumption
        | change with (i \le (S m1)+i).
          apply le_plus_n
        ]*)
      | (*qui autobatch non chiude il goal*)
        exact H4
      ]
    | apply (trans_eq ? ? (map_iter_i (S k) (\lambda m. g 
       (transpose i (S(m1 + i)) 
       (transpose (S(m1 + i)) (S(S(m1 + i))) 
       (transpose i (S(m1 + i)) m)))) f n))
      [ (*qui autobatch dopo alcuni minuti non aveva ancora terminato la propria esecuzione*)
        apply (H2 m1)
        [ autobatch
          (*unfold lt.
          apply le_n*)
        | assumption
        | apply (trans_le ? (S(S (m1+i))))
          [ autobatch
            (*apply le_S.
            apply le_n*)
          | (*qui autobatch NON CHIUDE il goal*)
            assumption
          ]
        ]
      | apply eq_map_iter_i.
        intros.
        apply eq_f.
        apply sym_eq.
        apply eq_transpose
        [ unfold Not. 
          intro.
          apply (not_le_Sn_n i).
          rewrite < H7 in \vdash (? ? %).
          autobatch
          (*apply le_S_S.
          apply le_S.
          apply le_plus_n*)
        | unfold Not.
          intro.
          apply (not_le_Sn_n i).
          rewrite > H7 in \vdash (? ? %).
          autobatch
          (*apply le_S_S.
          apply le_plus_n*)
        | unfold Not.
          intro.
          autobatch
          (*apply (not_eq_n_Sn (S m1+i)).
          apply sym_eq.
          assumption*)
        ]
      ]
    ]
  ]
]
qed.

theorem eq_map_iter_i_transpose1: \forall f:nat\to nat \to nat.associative nat f \to
symmetric2 nat nat f \to \forall n,k,i,j:nat. 
\forall g:nat \to nat. n \le i \to i < j \to j \le S k+n \to 
map_iter_i (S k) g f n = map_iter_i (S k) (\lambda m. g (transpose i j m)) f n.
intros.
simplify in H3.
cut ((S i) < j \lor (S i) = j)
[ elim Hcut
  [ cut (j = S ((j - (S i)) + i))
    [ rewrite > Hcut1.
      apply (eq_map_iter_i_transpose f H H1 n k (j - (S i)) g i)
      [ assumption
      | rewrite < Hcut1.      
        assumption
      ]
    | rewrite > plus_n_Sm.
      autobatch
      (*apply plus_minus_m_m.
      apply lt_to_le.
      assumption*)
    ]
  | rewrite < H5.
    apply (eq_map_iter_i_transpose_i_Si f H H1 g)
    [ autobatch
      (*simplify.
      assumption*)
    | apply le_S_S_to_le.
      autobatch
      (*apply (trans_le ? j)
      [ assumption
      | assumption
      ]*)
    ]
  ]
| autobatch
  (*apply le_to_or_lt_eq.
  assumption*)
]
qed.

theorem eq_map_iter_i_transpose2: \forall f:nat\to nat \to nat.associative nat f \to
symmetric2 nat nat f \to \forall n,k,i,j:nat. 
\forall g:nat \to nat. n \le i \to i \le (S k+n) \to n \le j \to j \le (S k+n) \to 
map_iter_i (S k) g f n = map_iter_i (S k) (\lambda m. g (transpose i j m)) f n.
intros.
apply (nat_compare_elim i j)
[ intro.
  (*qui autobatch non chiude il goal*)
  apply (eq_map_iter_i_transpose1 f H H1 n k i j g H2 H6 H5)
| intro.
  rewrite > H6.
  apply eq_map_iter_i.
  intros.
  autobatch
  (*rewrite > (transpose_i_i j).
  reflexivity*)
| intro.
  apply (trans_eq ? ? (map_iter_i (S k) (\lambda m:nat.g (transpose j i m)) f n))
  [ apply (eq_map_iter_i_transpose1 f H H1 n k j i g H4 H6 H3)
  | apply eq_map_iter_i.
    intros.
    autobatch
    (*apply eq_f.
    apply transpose_i_j_j_i*)
  ]
]
qed.

theorem permut_to_eq_map_iter_i:\forall f:nat\to nat \to nat.associative nat f \to
symmetric2 nat nat f \to \forall k,n:nat.\forall g,h:nat \to nat.
permut h (k+n) \to (\forall m:nat. m \lt n \to h m = m) \to
map_iter_i k g f n = map_iter_i k (\lambda m.g(h m)) f n.
intros 4.
elim k
[ simplify.
  rewrite > (permut_n_to_eq_n h)
  [ reflexivity
  | (*qui autobatch non chiude il goal*)
    assumption
  | (*qui autobatch non chiude il goal*)
    assumption
  ]
| apply (trans_eq ? ? (map_iter_i (S n) (\lambda m.g ((transpose (h (S n+n1)) (S n+n1)) m)) f n1))
  [ unfold permut in H3.
    elim H3.
    apply (eq_map_iter_i_transpose2 f H H1 n1 n ? ? g)
    [ apply (permut_n_to_le h n1 (S n+n1))    
      [ apply le_plus_n
      | (*qui autobatch non chiude il goal*)
        assumption
      | (*qui autobatch non chiude il goal*)
        assumption
      | apply le_plus_n
      | apply le_n
      ]
    | autobatch
      (*apply H5.
      apply le_n*)
    | apply le_plus_n
    | apply le_n
    ]
  | apply (trans_eq ? ? (map_iter_i (S n) (\lambda m.
     (g(transpose (h (S n+n1)) (S n+n1) 
     (transpose (h (S n+n1)) (S n+n1) (h m)))) )f n1))
    [ simplify.
      fold simplify (transpose (h (S n+n1)) (S n+n1) (S n+n1)).
      apply eq_f2
      [ autobatch
        (*apply eq_f.
        rewrite > transpose_i_j_j.
        rewrite > transpose_i_j_i.
        rewrite > transpose_i_j_j.
        reflexivity.*)
      | apply (H2 n1 (\lambda m.(g(transpose (h (S n+n1)) (S n+n1) m))))
        [ apply permut_S_to_permut_transpose.
          (*qui autobatch non chiude il goal*)
          assumption
        | intros.
          unfold transpose.
          rewrite > (not_eq_to_eqb_false (h m) (h (S n+n1)))
          [ rewrite > (not_eq_to_eqb_false (h m) (S n+n1))
            [ simplify.
              autobatch
              (*apply H4.
              assumption*)
            | rewrite > H4
              [ autobatch  
                (*apply lt_to_not_eq.
                apply (trans_lt ? n1)
                [ assumption
                | simplify.
                  unfold lt.
                  apply le_S_S.
                  apply le_plus_n
                ]*)
              | assumption
              ]
            ]
          | unfold permut in H3.
            elim H3.
            simplify.
            unfold Not.
            intro.
            apply (lt_to_not_eq m (S n+n1))
            [ autobatch
              (*apply (trans_lt ? n1)
              [ assumption
              | simplify.
                unfold lt.
                apply le_S_S.
                apply le_plus_n
              ]*)
            | unfold injn in H7.
              apply (H7 m (S n+n1))
              [ autobatch
                (*apply (trans_le ? n1)
                [ apply lt_to_le.
                  assumption
                | apply le_plus_n
                ]*)
              | apply le_n
              | assumption
              ]
            ]
          ]
        ]
      ]
    | apply eq_map_iter_i.
      intros.
      autobatch
      (*rewrite > transpose_transpose.
      reflexivity*)
    ]
  ]
]
qed.
