

whelp instance \lambda A:Set.\lambda P:A \to A \to Prop.\forall x:A. P x x.
whelp instance \lambda A:Set.\lambda P:A \to A \to Prop.\forall x,y:A. P x y \to P y x.
whelp instance \lambda A:Set.\lambda P:A \to A \to Prop.\forall x,y,z:A. P x y \to P y z \to P y z.
whelp instance \lambda A:Set.\lambda f:A \to A \to A. \forall x,y:A. f x y = f  y x.
whelp instance \lambda A:Set.\lambda r : A \to A \to Prop. \forall x,y,z:A. r x y \to r y z \to r x z.


whelp instance \lambda A:Set.\lambda R:A \to A \to Prop.\forall x:A.\forall y:A.(R x y) \to \forall z:A.(R x z) \to \exists u:A.(R y u) \land (R z u).

whelp instance λA:Set.λR:A→A→Prop.∀x:A.∀y:A.(R x y)→∀z:A.(R x z)→∃u:A.(R y u)∧(R z u).

whelp instance \lambda A:Set. \lambda R:A\to A\to Prop. confluence A R.

whelp instance \lambda A:Set. \lambda f:A\to A\to A. \lambda g:A\to A\to A.  \forall x,y,z : A . f x (g y z) = g (f x y ) (f x z).
