# Assignment 3: Natural Deduction

- The **Natural Deduction Proof System** consists of the following *Axiom Schema* and *Inference Rules* for Introduction and Elimination of Connectives.
- The main formula of each Axiom/Rule Schema is highlighted in bold face.
- We write the proof system in terms of **judgments** of the form  Γ |- p, where Γ is a set of **assumption** propositions and p is a **conclusion** proposition. 

```OCaml

(* Hyp *)

Γ |- p     if p is in Γ 

(* T-I *)

Γ |- T

(* ->-I *)

  Γ,p |- q              (->-E)  Γ |- p -> q     Γ |- p
-------------          --------------------------------
 Γ |- p -> q                       Γ |- q

(* ~-Int *)

 Γ |- F           (~-Class)   Γ,~p |- F
--------                     -----------
 Γ |- p                         Γ |- p

(* /\-I *)

 Γ |- p      Γ |- q          (/\-EL)   Γ |- p /\ q           (/\-ER)   Γ |- p /\ q
--------------------                  -------------                   -------------
     Γ |- p /\ q                          Γ |- p                          Γ |- q

(* \/-IL *)

   Γ |- p          (\/-IR)   Γ |- q           (V-E)  Γ |- p \/ q      Γ, p |- r      Γ, q |- r 
-------------              -------------            -------------------------------------------
 Γ |- p \/ q                Γ |- p \/ q                                 Γ |- r

```

Each rule can be considered a proof-tree building constructor that takes the list of judgments in the **numerator** (antecedents) and the judgment in the **denominator** (consequent).

A proof of a judgment Γ |- p  in the ND style is a tree with the **denominator** (consequent) of the root node labelled with judgement  Γ |- p, and each leaf being labelled by an instance of one of the axiom schema, and each internal node being a valid instance of one of the inference rules for introduction or elimination of a main connective. 

Your assignment involves -
- Defining a data type **ndprooftree** to represent candidate ND-style proofs for a given judgment.
- Defining a function **valid_ndprooftree** that checks if a given tree is indeed a valid instance of a ND-style proof, i.e., check that there is agreement  in the assumptions and propositions w.r.t. the antecedent and consequent judgments, as expected in the rule. 
- Defining a function **pad(π, Δ)**: ndprooftree * (prop set) -> ndprooftree, that given a valid ND-style proof π of judgment  Γ |- p, and a set of propositions Δ, returns a valid ND-style proof of judgment Γ U Δ |- p.
- Defining a function **prune(π)**: ndprooftree  -> ndprooftree, that given a ND-style proof π of judgment  Γ |- p, returns a valid ND-style proof of judgment Δ |- p, where Δ is a finite subset of Γ.
- Defining a function **graft(π, l)**:  ndprooftree * (ndprooftree list) -> ndprooftree, that given a ND-style proof π of judgment Δ |- p, where Δ = {q_1, ..., q_k}, and a list (set) of valid ND-style proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k, returns a valid ND-style proof of judgment Γ |- p.