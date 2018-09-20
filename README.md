# semiKanren

*semiKanren* is a relational programming language using semiunification as a goal constructor. It is currently implemented as a modification of the language described in *The Reasoned Schemer* (2nd ed.) or found in [this repository](https://github.com/TheReasonedSchemer2ndEd/CodeFromTheReasonedSchemer2ndEd).

## Semiunification

Semiunification is a decision problem which asks if *subsumption* relations between terms can be satisfied. Less mysteriously, suppose we have two syntax trees t₁ and t₂ made up of variables (denoted by lower-case letters) and function symbols (denoted by upper-case letters). The *subsumption* relation t₁ ≤ t₂ is satisfied if we can replace the variables of t₁ in a way that makes t₁ and t₂ syntactically equal.

For example, the relation F(x, y) ≤ F(G(z), H()) is satisfiable because the map {x ↦ G(z), y ↦ H()} makes the two terms syntactically equal.

On the other hand, F(x, y) ≰ G(z, w) because F and G are function symbols. Only variables can be replaced by other terms; the mismatched function symbols will be mismatched no matter what variable substitutions we make.

It might help to think of the quantity measured by "≤" as specificity. In other words, if t₁ ≤ t₂, then t₂ is structurally more specific than t₁. With this language, we are trying to evoke the image of variables as being "general" and getting more specific as we make substitutions. With that in mind, here is a chain of terms which goes from less specific to more specific:

a ≤ G(b) ≤ G(G(c)) ≤ G(G(G(d))) ≤ G(G(G(G(H()))))

The semiunification problem asks, for some collection of terms s₁, s₂, t₁, t₂... do the relations s₁ ≤ s₂, t₁ ≤ t₂... hold? This definition is *not* precise and there are some subtleties which I will try to address via examples.

### Examples and clarification

#### Example 1

x ≤ F()\
x ≤ G()

This example is semiunifiable because both F() and G() are more specific than a variable x. We *can* map x ↦ F() in the first relation and x ↦ G() in the second relation. I'm emphasizing the word *can*, because it is merely the *existence* of each substitution that verifies the corresponding relation. The variable x does not get any value─neither substitution is actually performed.

#### Example 2

F() ≤ x

This relation, as written, does not hold. A variable is the most general kind of term. However, if we conclude that x = F(), then the relation holds. This relation is constraining x to be F(). The only way this problem is satisfied is if it were really F() ≤ F().

#### Example 3

F() ≤ x\
G() ≤ x

This problem is *not* semiunifiable. To satisfy the first relation, we conclude that x is F(), as in example 2, but then we have a function symbol mismatch in the second. Contrast this with example 1, where we didn't conclude anything from either relation, i.e. we didn't have to change x to satisfy either relation¹.

*****

## Footnotes

1. The value of x *is* constrained in example 1; namely, the semiunification fails if we later learn that x has any value that is more specific than a variable.

*****

## References

Hemann, Jason; Friedmann, Daniel P. - μKanren: A Minimal Functional Core for Relational Programming. Workshop on Scheme and Functional Programming (2013).

Lushman, Brad; Cormack, Gordon - A larger decidable semiunification problem. 9th ACM Symposium on Principles and Practice of Declarative Programming (2007).

Lushman, Brad; Cormack, Gordon - Constraint-Based typing for ML via Semiunification. Computer Science Tech Report, University of Waterloo (2008).
