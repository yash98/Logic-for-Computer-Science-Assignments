# Assignment 0: Syntax and Semantics of Propositional Logic

Consider the representation of propositions in OCaml as a data type:

type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;



Define the following syntax-directed functions:

- ht: prop -> int, which returns the height of a proposition (considered a syntax tree). A leaf is at height 0.
- size: prop -> int, which returns the number of nodes in a proposition (considered a syntax tree).
- letters: prop -> string set, which returns the set of propositional letters.  This requires you to implement sets (lists are a good built in data type) and member, subset, union, intersection, difference etc.
- A proposition p1 is a sub-proposition of another proposition p2 if the syntax tree of p1 appears as a subtree of the syntax tree of p2.   Define a function subprop_at: prop -> prop -> path set which yields the set of paths in the tree of p2 leading from its root to a position which is the root of an occurrence of p1, assuming p1 is a sub-proposition of p2, and raising an exception NotSubProp otherwise.  You can represent a path as a list of symbols left/right or e.g., code it as a bit-string (0=left, 1=right). 

Define the semantic function, using the standard truth tables for the connectives.

- truth: prop -> (string -> bool) -> bool
(Here truth assignments/valuations are represented as partial functions from strings to OCaml bool values.  Raise an exception to model "don't care" cases.)

Provide at least 6 examples of propositions of ht >= 2 and with at least 2-4 letters, and use at least 2-3 different connectives.  You examples should include tautologies, contradictions and contingencies. 

A proposition is in negation normal form (NNF)  if

1. it does not contain the connectives Impl and Iff 
2. it does not contain sub-propositions of the form "Not T" and "Not F"
3. it does not contain any sub-proposition of the form "Not (Not p)"
4. It does not contain any  path in which an occurrence of Not appears at a position closer to the root than occurrences of And or Or connectives on that path.

A proposition is in Disjunctive normal form (DNF) or Sum of Products Form if 

1. it is in NNF
2. It does not contain any  path in which an occurrence of the And connective appears at a position closer to the root than occurrences of Or connectives on that path.

A proposition is in Conjunctive normal form (CNF) or Product of Sums form if 

1. it is in NNF
2. It does not contain any  path in which an occurrence of the Or connective appears at a position closer to the root than occurrences of And connectives on that path.


Write the following functions that must preserve truth. Show this with 4 examples each and the truth function on at least 3 truth assignments per example.  [Hint: use De Morgan's Laws and any other laws.]

- nnf: prop -> prop,  which converts any proposition into a logically equivalent one in  NNF.
- cnf: prop -> prop,  which converts any proposition into  a logically equivalent one in CNF.
- dnf: prop -> prop,  which converts any proposition into  a logically equivalent one in DNF.
You may use further laws of boolean algebras (Unit laws, idempotence, etc.) to further simplify the propositions in CNF and DNF. 

