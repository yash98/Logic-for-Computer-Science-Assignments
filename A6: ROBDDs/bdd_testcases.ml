(*
 Ordering: x1 < x2 < x3
 *)
let vx1 = L(1);;
let vx2 = L(2)
let vx3 = L(3);;

let p0 = Iff(x1, x2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

(* compute NNF, CNF of p1 and Not(p1) *)
let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

(* build ROBDDs *)
let tt = build T;;
let tf = build F;;

let tvx1 = build vx1;;
let tp2 = build p2;;
let tp0 = build p0;;
let tp1 = build p1;;
let tp1' = build p1';;
let tp1'' = build p1'';;

let tnp1 = build np1;;
let tnp1' = build np1';;
let tnp1'' = build np1'';;

(* Testcase #1 *)
tp1 == tp1';;
tp1 == tp1'';;
tnp1 == tnp1';;
tnp1 == tnp1'';;

(* Testcase #2 *)
let tp1anp1 = apply AND tp1 tnp1;;
tp1anp1 == tf;;
let tp1onp1 = apply OR tp1 tnp1;;
tp1onp1 == tt;;

(* Testcase #3 *)
let tp1rv30 = restrict t1 3 0;;
tp1rv30 == tp0;;
let tp1rv31 = restrict t1 3 1;;
tp1rv31 =  tt;;

(* Testcase #4 *)
allsat t1;; (* 4 solutions: { {x1 = 0, x2 = 0}, {x1 = 1, x2 = 1}, {x1 = 1, x2 = 0, x3 = 1}, {x1 = 0, x2 = 1, x3 = 1}} *)
anysat t1;; (* any of the above *)

(* Testcase #5 *)
let tstp2tp1 = simplify tp2 tp1;;
tstp2tp1 == tt;;
let tstvx1tp1 = simplify tvx1 tp1;;
tstvx1tp1 == tp2;;
