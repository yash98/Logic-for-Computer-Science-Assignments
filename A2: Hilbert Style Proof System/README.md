# Assignment 2: Hilbert Style Proof System
The Hilbert-style proof system consists of the following Axiom Schema, where Γ is a set of propositions, and p,q,r are propositions.

(Ass) Γ |- p     if p in Γ

(K)     Γ |-  p -> (q -> p)

(S)     Γ |- (p -> (q->r)) -> ((p -> q) -> (p-> r))

(R )    Γ |- (~p -> ~q) -> ((~p -> q) -> p)

and one inference rule 

(MP) \
Γ |- p-> q Γ |- p \
---------------------\
Γ |- q


A proof of a judgment Γ |- p  in the Hilbert style is a tree with the root labelled with judgement  Γ |- p, and each leaf being labelled by an instance of one of the axiom schema, and each internal node being a valid instance of the rule MP. 

Your assignment involves

1. Defining a data type hprooftree to represent candidate Hilbert-style proofs for a given judgment.
2. Defining a function valid_hprooftree that checks if a given tree is indeed a valid instance of a Hilbert-style proof.
3. Defining a function pad(π, Δ): hprooftree * (prop set) -> hprooftree, that given a valid Hilbert-style proof π of judgment  Γ |- p, and a set of propositions Δ, returns a valid Hilbert-style proof of judgment Γ U Δ |- p.
4. Defining a function prune(π): hprooftree  -> hprooftree, that given a Hilbert-style proof π of judgment  Γ |- p, returns a valid Hilbert-style proof of judgment Δ |- p, where Δ is a finite subset of Γ.
5. Defining a function graft(π, l):  hprooftree * (hprooftree list) -> hprooftree, that given a Hilbert-style proof π of judgment Δ |- p, where Δ = {q_1, ..., q_k}, and a list l of proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k, returns a valid Hilbert-style proof of judgment Γ |- p.
6. Defining a function dedthm(π): hprooftree  -> hprooftree, that given a valid Hilbert-style proof π of the judgment Γ U {p}  |- q, returns a valid Hilbert-style proof tree of the judgment Γ  |- p -> q.
