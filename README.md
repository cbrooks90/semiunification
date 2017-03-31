# semiKanren

Semiunification is an undecidable problem. However, so-called "R-acyclic" semiunification problems can be solved. Here I've attempted a version of miniKanren which uses semiunification.

The primary goal is to write a relational type inferencer which should aid the program synthesis work of William E. Byrd, Greg Rosenblatt and others. This should be possible since certain type inference problems with let-polymorphism can be translated in a syntax-directed way into a (slight variant of an) R-ASUP instance.

## References

Hemann, Jason; Friedmann, Daniel P. - μKanren: A Minimal Functional Core for Relational Programming. Workshop on Scheme and Functional Programming (2013).

Lushman, Brad; Cormack, Gordon - A larger decidable semiunification problem. 9th ACM Symposium on Principles and Practice of Declarative Programming (2007).

Lushman, Brad; Cormack, Gordon - Constraint-Based typing for ML via Semiunification. Computer Science Tech Report, University of Waterloo (2008).
