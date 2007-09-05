notation < "hvbox(\exists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'exists ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.

notation "hvbox(a break \to b)" 
  right associative with precedence 20
for @{ \forall $_:$a.$b }.

notation < "hvbox(a break \to b)" 
  right associative with precedence 20
for @{ \Pi $_:$a.$b }.

notation "hvbox(a break = b)" 
  non associative with precedence 45
for @{ 'eq $a $b }.

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

notation "hvbox(a break \neq b)" 
  non associative with precedence 45
for @{ 'neq $a $b }.

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

notation "hvbox(a break \divides b)"
  non associative with precedence 45
for @{ 'divides $a $b }.

notation "hvbox(a break \ndivides b)"
  non associative with precedence 45
for @{ 'ndivides $a $b }.

notation "hvbox(a break + b)" 
  left associative with precedence 50
for @{ 'plus $a $b }.

notation "hvbox(a break - b)" 
  left associative with precedence 50
for @{ 'minus $a $b }.

notation "hvbox(a break * b)" 
  left associative with precedence 55
for @{ 'times $a $b }.

notation "hvbox(a break \mod b)" 
  left associative with precedence 55
for @{ 'module $a $b }.

notation "\frac a b" 
  non associative with precedence 90
for @{ 'divide $a $b }.

notation "a \over b" 
  left associative with precedence 55
for @{ 'divide $a $b }.

notation "hvbox(a break / b)" 
  left associative with precedence 55
for @{ 'divide $a $b }.

notation > "- a" 
  right associative with precedence 60
for @{ 'uminus $a }.

notation < "- a" 
  right associative with precedence 75
for @{ 'uminus $a }.

notation "a !"
  non associative with precedence 80
for @{ 'fact $a }.

notation "(a \sup b)"
  right associative with precedence 65
for @{ 'exp $a $b}.

notation "\sqrt a" 
  non associative with precedence 60
for @{ 'sqrt $a }.

notation "hvbox(a break \lor b)" 
  left associative with precedence 30
for @{ 'or $a $b }.

notation "hvbox(a break \land b)" 
  left associative with precedence 35
for @{ 'and $a $b }.

notation "hvbox(\lnot a)" 
  non associative with precedence 40
for @{ 'not $a }.

notation "hvbox(a break => b)" 
  non associative with precedence 45
for @{ 'parred $a $b }.
