# Assignment 4: Normalisation in Natural Deduction Proofs

The **Natural Deduction Proof System** consists of the following Axiom Schema and Inference Rules for Introduction and Elimination of Connectives. (The main formula of each Axiom/Rule Schema is highlighted in bold face).

We write the proof system in terms of **judgments** of the form  Γ |- p, where Γ is a set of **assumption** propositions and p is a **conclusion** proposition.

```OCaml
(* Hyp *)

Γ |- p      if p is in Γ

(* T-I *)

Γ |- T

(* ->-I *)                  (* ->-E *)

 Γ, p  |-  q                Γ |- p -> q      Γ |- p
-------------              -------------------------
 Γ |- p -> q                        Γ |- q

(* ~-Int *)                (* ~-Class *)

 Γ |-  F                    Γ, ~p |-  F
---------                  --------------
 Γ |-  p                      Γ |-  p

(* /\-I *)                    (* /\-EL *)        (* /\-ER *)

Γ |- p      Γ |- q             Γ |- p /\ q            Γ |- p /\ q
-------------------           -------------          --------------
    Γ |- p /\ q                   Γ |- p                 Γ |- q

(*\/-IL *)            (* \/-IR *)             (* V-E *)

   Γ |- p               Γ |- q                Γ |- p \/ q      Γ, p  |- r      Γ, q  |- r 
------------         -------------           ----------------------------------------------
Γ |- p \/ q           Γ |- p \/ q                               Γ |- r
```

Each rule can be considered a proof-tree building constructor that takes the list of judgments in the **numerator**(antecedents)  and the judgment in the **denominator**(consequent).

A proof of a judgment Γ |- p  in the ND style is a tree with the root labelled with judgement  Γ |- p, and each leaf being labelled by an instance of one of the axiom schema, and each internal node being a valid instance of one of the inference rules for introduction or elimination of a main connective. 

We say that an **r-pair** occurs in a ND proof tree if an instance of a connective's introduction rule is immediately "followed by" (closer to the root) an instance of the same connectives's elimination rule, with the main proposition of the introduction rule coinciding with that of the elimination rule.  An r-pair can be eliminated by replacing the proof-trees with "simpler" proof trees (note that simpler does not mean smaller in size or shorter in height)

Define the functions:

- **find_rpair**: ndprooftree -> ndprooftree, which given a ND proof tree returns a subtree which is rooted at an instance of an r-pair, and raises an exception Normalised if there is no such r-pair.  (It is customary to return the left-most r-pair closest to the root of the tree). 
- **simplify1**: ndprooftree -> ndprooftree, that given an ND proof tree with r-pair at the root, returns a valid but "simpler" ND proof tree of the same consequent judgment.
- **normalise**: ndprooftree -> ndprooftree, that given an ND proof tree,  returns a "completely simplified" ND proof tree of the same judgment at the root, which has no r-pairs in it.
