# Assignment 1: Analytic Tableaux

In this assignment, you will implement Analytic Tableaux, which are trees built according to some rules.

A **Node** in a tableau is labelled with  a proposition and the truth value we wish to give it, i.e., as prop * bool.

During the development of a tableau, nodes are introduced and examined.  When a node is examined, it is marked as examined and its analysis may result in:

- closing the paths on which it occurs because a contradiction has been discovered
- adding nodes and/or branches to each path on which this node lies, depending on the kind of node. 

A tableau is developed by selecting some unexamined node on a path which is not already closed due to a contradiction, and then analysing it.  Let p be the proposition and b be the boolean value in the label of the node being analysed:

1. if p is T and b is true, or if p is F and b is false, then the node is marked examined and no extensions are made to the paths on which this node occurs
2. if p is T and b is false, or if p is F and b is true, then the node is marked examined, and the paths on which this node occurs are considered closed  since they contain a contradiction.
3. if another node with p and the negation of b is already on the path leading to this node, the current node is marked examined and the path considered closed as it contains a contradiction. [You can create a back-pointer to that earlier contradicting node]
4. if p is L(s), then the propositional letter s is assigned the truth value b
5. if p is Not(p1) and b is true [respectively false], then the node is marked examined and each open (non-closed) path on which it lies is extended with a node marked (p1, false) [respectively  (p1, true)]
6. if the node is an α-type node, then it is marked examined, and each open (non-closed) path on which it lies is extended with two nodes α_1 and α_2, one below the other.  [See Table 1 below]
7. if the node is an β-type node, then it is marked examined, and each open (non-closed) path on which it lies is extended with two branches: on the first branch the node β_1 is placed, and on the second branch β_2 is placed. [See Table 2 below]
8. if p is of the form Iff(p1, p2) and b is false, then  it is marked examined, and each open (non-closed) path on which it lies is extended with two branches: on the first branch the nodes (p1, false) and (p2, true) are placed one below the other, and on the second branch the nodes (p1, true) and (p2, false) are placed one below the other.  If p is of the form Iff(p1, p2) and b is true, then  it is marked examined, and each open (non-closed) path on which it lies is extended with two branches: on the first branch the nodes (p1, true) and (p2, true) are placed one below the other, and on the second branch the nodes (p1, false) and (p2, false) are placed one below the other.  

### Alpha type nodes

|          α           |        α_1         |    α_2     |
| :------------------: | :----------------: | :--------: |
|  (And(p1,p2), true)  | (Or(p1,p2), false) | (p1, true) |
|     (p1, false)      |     (p2,true)      | (p2,false) |
| (Impl(p1,p2), false) |     (p1,true)      | (p2,false) |


### Beta type nodes

|          β          |    β_1     |    β_2     |
| :-----------------: | :--------: | :--------: |
| (And(p1,p2), false) | (p1,false) | (p2,false) |
|  (Or(p1,p2), true)  | (p1,true)  | (p2,true)  |
|  (Or(p1,p2), true)  | (p1,false) | (p2,true)  |

A tableau is called "fully developed" if it has no unexamined nodes on any open path.

Your assignment is to design an OCaml data structure for representing (partial) tableaux given a root node.

This involves designing a suitable tree/graph structure with nodes labelled by values of type prop*bool.  The nodes data structure has to take into account whether it has been examined, whether it lies on a contradictory path, and its descendants (0,1,2)

Define efficient functions for the following:

- *contrad_path* that given a partially developed tableau detects a contradiction on a path and marks it closed (excluding it from further consideration).
- *valid_tableau* that given a partially (or fully) developed tableau, checks whether or not it is a legitimate development from the root of the tableau, according to the rules specified.
- *select_node* that selects an unexamined node on an open path as a candidate for further development.
- *step_develop* that given a selected node on a path, develops the tableau according to the rules  specified above.
- *find_assignments*, that given a root node, finds all satisfying/falsifying truth assignments (valuations) for that prop-bool pair. 
- *check_tautology* and *check_contradiction*, which return a tableaux proof that a proposition is a tautology [respectively contradiction] if it so, and a counter-example valuation otherwise. 
