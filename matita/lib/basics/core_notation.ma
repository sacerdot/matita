(* exists *******************************************************************)

notation "hvbox(∃ _ break . p)"
 with precedence 20
for @{'exists $p }.

notation < "hvbox(\exists ident i : ty break . p)"
 right associative with precedence 20
for @{'exists (\lambda ${ident i} : $ty. $p) }.

notation < "hvbox(\exists ident i break . p)"
  with precedence 20
for @{'exists (\lambda ${ident i}. $p) }.

(*
notation < "hvbox(\exists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'exists ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.
*)

notation > "\exists list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'exists (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'exists (λ${ident x}.$acc)} } }
       }.

notation > "hvbox(∃∃ ident x0 break . term 19 P0 break & term 19 P1)"
 non associative with precedence 20
 for @{ 'exists2 (λ${ident x0}.$P0) (λ${ident x0}.$P1) }.

notation < "hvbox(∃∃ ident x0 break . term 19 P0 break & term 19 P1)"
 non associative with precedence 20
 for @{ 'exists2 (λ${ident x0}:$T0.$P0) (λ${ident x0}:$T0.$P1) }.

(* sigma ********************************************************************)

notation < "hvbox(\Sigma ident i : ty break . p)"
 left associative with precedence 20
for @{'sigma (\lambda ${ident i} : $ty. $p) }.

notation < "hvbox(\Sigma ident i break . p)"
 with precedence 20
for @{'sigma (\lambda ${ident i}. $p) }.

(*
notation < "hvbox(\Sigma ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'sigma ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.
*)

notation > "\Sigma list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'sigma (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'sigma (λ${ident x}.$acc)} } }
       }.

notation "hvbox(« term 19 a, break term 19 b»)" 
with precedence 90 for @{ 'dp $a $b }.

(* dependent pairs (i.e. Sigma with predicate in Type[0])  ********************)

notation < "hvbox(𝚺 ident i : ty break . p)"
 left associative with precedence 20
for @{'dpair (\lambda ${ident i} : $ty. $p) }.

notation < "hvbox(𝚺 ident i break . p)"
 with precedence 20
for @{'dpair (\lambda ${ident i}. $p) }.

(*
notation < "hvbox(𝚺 ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'dpair ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.
*)

notation > "𝚺 list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'dpair (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'dpair (λ${ident x}.$acc)} } }
       }.

notation "hvbox(❬ term 19 a, break term 19 b❭)" 
with precedence 90 for @{ 'mk_DPair $a $b }.

(* conguence ****************************************************************)

notation > "hvbox(n break (≅ \sub term 90 p) m)"
  non associative with precedence 45
for @{ 'congruent $n $m $p }.

notation < "hvbox(term 46 n break ≅ \sub p term 46 m)"
  non associative with precedence 45
for @{ 'congruent $n $m $p }.

(* projections **************************************************************)

notation < "\fst \nbsp term 90 x" with precedence 69 for @{'pi1a $x}.
notation < "\snd \nbsp term 90 x" with precedence 69 for @{'pi2a $x}.

notation < "\fst \nbsp term 90 x \nbsp term 90 y" with precedence 69 for @{'pi1b $x $y}.
notation < "\snd \nbsp term 90 x \nbsp term 90 y" with precedence 69 for @{'pi2b $x $y}.

notation > "\fst" with precedence 90 for @{'pi1}.
notation > "\snd" with precedence 90 for @{'pi2}.

(* orders *******************************************************************)

notation "hvbox(a break \leq b)" 
  non associative with precedence 45
for @{ 'leq $a $b }.

notation "hvbox(a break \geq b)" 
  non associative with precedence 45
for @{ 'geq $a $b }.

notation "hvbox(a break \lt b)" 
  non associative with precedence 45
for @{ 'lt $a $b }.

notation "hvbox(a break \gt b)" 
  non associative with precedence 45
for @{ 'gt $a $b }.

(* negated equality *********************************************************)

notation > "hvbox(a break \neq b)" 
  non associative with precedence 45
for @{ 'neq ? $a $b }.

notation < "hvbox(a break maction (\neq) (\neq\sub t) b)" 
  non associative with precedence 45
for @{ 'neq $t $a $b }.

(* negated orders ***********************************************************)

notation "hvbox(a break \nleq b)" 
  non associative with precedence 45
for @{ 'nleq $a $b }.

notation "hvbox(a break \ngeq b)" 
  non associative with precedence 45
for @{ 'ngeq $a $b }.

notation "hvbox(a break \nless b)" 
  non associative with precedence 45
for @{ 'nless $a $b }.

notation "hvbox(a break \ngtr b)" 
  non associative with precedence 45
for @{ 'ngtr $a $b }.

(* divides, negated divides *************************************************)

notation "hvbox(a break \divides b)"
  non associative with precedence 45
for @{ 'divides $a $b }.

notation "hvbox(a break \ndivides b)"
  non associative with precedence 45
for @{ 'ndivides $a $b }.

(* arithmetics **************************************************************)

notation "hvbox(a break + b)" 
  left associative with precedence 55
for @{ 'plus $a $b }.

notation "hvbox(a break - b)" 
  left associative with precedence 55
for @{ 'minus $a $b }.

notation "hvbox(a break \middot b)" 
  left associative with precedence 60
  for @{ 'middot $a $b }.

notation "hvbox(a break \mod b)" 
  left associative with precedence 60
for @{ 'module $a $b }.

(* logical connectives ******************************************************)

notation "hvbox(a break \lor b)" 
  left associative with precedence 30
for @{ 'or $a $b }.

notation "hvbox(a break \land b)" 
  left associative with precedence 35
for @{ 'and $a $b }.

notation "hvbox(\lnot a)" 
  non associative with precedence 40
for @{ 'not $a }.

notation > "hvbox(a break \liff b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.

notation "hvbox(a break \leftrightarrow b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.

(* subsets ******************************************************************)

notation "hvbox(\Omega \sup term 90 A)" non associative with precedence 90
for @{ 'powerset $A }.

notation > "hvbox(\Omega ^ term 90 A)" non associative with precedence 90
for @{ 'powerset $A }.

notation "hvbox(a break ∈ b)" non associative with precedence 45
for @{ 'mem $a $b }.

notation "hvbox(a break ∉ b)" non associative with precedence 45
for @{ 'notmem $a $b }.

notation "hvbox(a break ∩ b)" left associative with precedence 60
for @{ 'intersects $a $b }. (* \cap *)

notation "hvbox(a break ∪ b)" left associative with precedence 55
for @{ 'union $a $b }. (* \cup *)
