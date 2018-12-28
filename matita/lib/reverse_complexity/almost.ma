include "reverse_complexity/speedup.ma".

definition aes : (nat → nat) → (nat → nat) → Prop ≝ λf,g.
  ∃n.∀m. n ≤ m → f m = g m.

lemma CF_almost: ∀f,g,s. CF s g → aes g f → CF s f.
#f #g #s #CFg * #n lapply CFg -CFg lapply g -g
elim n 
  [#g #CFg #H @(ext_CF … g) [#m @H // |//]
  |#i #Hind #g #CFg #H
   @(Hind (λx. if eqb i x then f i else g x))
    [@CF_if 
      [@(O_to_CF … MSC) [@le_to_O @(MSC_in … CFg)] @CF_eqb //
      |@(O_to_CF … MSC) [@le_to_O @(MSC_in … CFg)] @CF_const
      |@CFg
      ]
    |#m #leim cases (le_to_or_lt_eq … leim)
      [#ltim lapply (lt_to_not_eq … ltim) #noteqim 
       >(not_eq_to_eqb_false … noteqim) @H @ltim
      |#eqim >eqim >eqb_n_n //
      ]
    ]
  ]
qed.