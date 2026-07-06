= Prelude
#let isSet(A) = [$"Set"(#A)$]
#let isAtom(A) = [$"Atom"(#A)$]
#let def = [*Definition:*]
#let axiom(name) = [*Axiom of #name\:*]

Language: $L = ("Set"^1,  in""^2)$

Interpretation:

$isSet(A)$ means that $A$ is a set. \
$in$ is set membership. \
_Both are primitive notions_

_Note: the following propositions are logically equivalent:_

- $p and q -> r$ 
- $p -> (q -> r)$ 

_The latter will be written as_
- $p -> q -> r$

_Thus, instead of_ \
$forall x, P(x) and Q(x) => R(x)$, \
I will try to write  \
$forall x, P(x) => Q(x) => R(x)$

The reason for this is simple: the reason for writing down the  following axiomatization is to formalize it in Lean 4.

Note:
- $forall x in A, P(x) equiv forall x, x in A => P(x)$
- $exists x in A, P(x) equiv exists x, x in A and P(x)$

_Note: In all of the following first-order formulae, quantifier range until the end of the expression. That is_

#pagebreak()

= Axioms
#axiom("Extensionality")

$forall A, B, isSet(A) => isSet(B) => (forall x, x in A <=> x in B) => A = B $

#axiom("Atoms")

$forall x, isAtom(x) => forall y, y in.not x$

_Note:_ $isAtom(A) := not isSet(A)$

#axiom("Universal Set")

$exists V forall x, x in V$

#axiom("Complements")

$forall A, isSet(A) => exists A^c, (isSet(A^c) and (forall x, x in A^c <=> x in.not A))$

#axiom("(Boolean) Unions")

$forall A, B, isSet(A) => isSet(B) => (exists A union B, isSet(A union B) and (forall x, x in A union B <=> x in A or x in B))$

#axiom("Set Union")

$forall A, isSet(A) and (forall x in A, isSet(x)) => exists union.big [A], isSet(union.big [A]), forall x, x in union.big [A] <=> exists y, y in A and x in y $


#axiom("Singletons")

$forall x exists {x}, isSet({x}) and (forall z, z in {x} => z = x)$

#axiom("Ordered Pairs") 

$forall a, b space exists (a, b) space forall c,d, space (a, b) = (c, d) => (a = c) and (b = d) $

#axiom("Cartesian Products")

$forall A, B, isSet(A) => isSet(B) => exists A times B, isSet(A times B) and (forall x, x in A times B => exists a, b, a in A and b in B => x = (a, b)) $

#axiom("Diagonal")

$exists [=], isSet([=]) and forall x in [=] space exists y, x = (y, y)$

#pagebreak()

= Definitions

#def $A inter B := (A^c union B^c)^c$

#def $B - A := B inter A^c$

#def $A Delta B := (B - A) union (A - B)$

#def $A subset.eq B$: $forall A, B, isSet(A) => isSet(B) => A subset.eq B <=> (forall x, x in A => x in B) $

#def $iota (x) := {x}$; $iota ^0 (x) = x$, $iota^(n+1) (x) = iota(iota^n (x))$

#def ${x, y} = {x} union {y}$

#def ${x_1, x_2, ..., x_n} = {x_1} union {x_2, ..., x_n}$

#def (Kuratowski ordered pair) $chevron x, y chevron.r := {{x}, {x, y}}$

#def ($n$-tuple) $(x_1, x_2, ..., x_n) := (x_1, (x_2, ..., x_n))$

#def (Cartesian power) $A^2 = A times A$; $A^(n+1) = A times A^n$


