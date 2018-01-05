(* (C) 2014 Luca Bressan *)

notation "hvbox(a break \to b)"
 right associative with precedence 20
 for @{ \forall $_:$a.$b }.

notation < "hvbox(Σ ident i : ty break . p)"
 left associative with precedence 20
for @{'sigma (λ${ident i}: $ty. $p) }.
notation < "hvbox(Σ ident i break . p)"
 with precedence 20
for @{'sigma (λ${ident i}. $p) }.

notation > "Σ list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'sigma (λ${ident x}: $T. $acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'sigma (λ${ident x}. $acc)} } }
       }.

notation "hvbox(π1 s)"
 non associative with precedence 70
 for @{ 'sig1 $s) }.
notation "hvbox(π2 s)"
 non associative with precedence 70
 for @{ 'sig2 $s) }.

notation "hvbox(〈 term 19 a, break term 19 b 〉)"
 with precedence 90 for @{ 'mk_sigma $a $b }.

notation "hvbox(B break × C)" 
 left associative with precedence 55
 for @{ 'times $B $C }.

notation "⋆"
 non associative with precedence 90
 for @{ 'star }.

notation "ϵ"
 non associative with precedence 90
 for @{ 'epsilon }.
notation "⌈ l, c ⌉"
 non associative with precedence 90
 for @{ 'cons $l $c }.

notation "hvbox(B break + C)" 
 left associative with precedence 50
 for @{ 'plus $B $C }.

notation "⊥"
 non associative with precedence 90
 for @{ 'falsum }.

notation "hvbox(B break ∨ C)" 
 left associative with precedence 50
 for @{ 'disj $B $C }.

notation "hvbox(B break ∧ C)" 
 left associative with precedence 60
 for @{ 'conj $B $C }.

notation < "hvbox(B break → C)" 
 left associative with precedence 60
 for @{ 'implies $B $C }.

notation < "hvbox(∃ ident i : ty break . p)"
 left associative with precedence 20
for @{'exists (λ${ident i}: $ty. $p) }.
notation < "hvbox(∃ ident i break . p)"
 with precedence 20
for @{'exists (λ${ident i}. $p) }.

notation > "∃ list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'exists (λ${ident x}: $T. $acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'exists (λ${ident x}. $acc)} } }
       }.
notation "hvbox(« term 19 a, break term 19 b »)"
 with precedence 90 for @{ 'mk_exists $a $b }.

notation "⊤"
 non associative with precedence 90
 for @{ 'verum }.

notation "hvbox(a break = b)" 
 non associative with precedence 45
 for @{ 'id $a $b }.

notation "hvbox(a break ≃ b)" 
 non associative with precedence 45
 for @{ 'eq $a $b }.

notation "hvbox(ı x)" 
 non associative with precedence 90
 for @{ 'rfl $x }.
notation "hvbox(d⁻¹)"
 non associative with precedence 80
 for @{ 'sym $d }.
notation "hvbox(d break • d')" 
 left associative with precedence 60
 for @{ 'tra $d $d' }.

notation "hvbox(y break ∘ d)"
 non associative with precedence 50
 for @{ 'subst $d $y }.

notation "hvbox(f ◽ d)"
 non associative with precedence 40
 for @{ 'ap $f $d}.
notation "hvbox(f ˙ d)"
 non associative with precedence 60
 for @{ 'sup_f $f $d}.

