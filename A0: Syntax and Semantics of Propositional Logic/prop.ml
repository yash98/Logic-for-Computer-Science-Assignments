type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type rho = Tbl of (string, bool) Hashtbl.t;;

let rec ht (p: prop): int = match p with
  | T -> 0
  | F -> 0
  | L(s) -> 0
  | Not(p1) -> 1+(ht p1)
  | And(p1, p2) -> max (ht p1) (ht p2)
  | Or(p1, p2) -> max (ht p1) (ht p2)
  | Impl(p1, p2) -> max (ht p1) (ht p2)
  | Iff(p1, p2) -> max (ht p1) (ht p2);;

let rec size (p: prop): int = match p with
  | T -> 1
  | F -> 1
  | L(s) -> 1
  | Not(p1) -> 1+(ht p1)
  | And(p1, p2) -> (ht p1) + (ht p2)
  | Or(p1, p2) -> (ht p1) + (ht p2)
  | Impl(p1, p2) -> (ht p1) + (ht p2)
  | Iff(p1, p2) -> (ht p1) + (ht p2);;

let rec isPresent (sl: string list) (s: string): bool = match sl with
  | [] -> false
  | ss::sx -> if (ss=s) then true else isPresent sx s;;

let rec lettersEfficient (p: prop) (ls: string list): string list = match p with
  | T -> ls
  | F -> ls
  | L(s) -> if (isPresent ls s) then ls else s::ls
  | Not(p1) -> lettersEfficient p ls
  | And(p1, p2) -> let ls1 = lettersEfficient p1 ls in lettersEfficient p2 ls1
  | Or(p1, p2) -> let ls1 = lettersEfficient p1 ls in lettersEfficient p2 ls1
  | Impl(p1, p2) -> let ls1 = lettersEfficient p1 ls in lettersEfficient p2 ls1
  | Iff(p1, p2) -> let ls1 = lettersEfficient p1 ls in lettersEfficient p2 ls1;;


let rec letters (p: prop): string list = lettersEfficient p [];;

let rec subprop_at_h (p: prop) (sp: prop) (csl: string) (sls: string list): string list = 
  if (p=sp) then csl::sls 
  else match p with 
  | T -> sls
  | F -> sls
  | L(s) -> sls
  | Not(p1) -> let csl1 = csl^"B" in subprop_at_h p1 sp csl1 sls
  | And(p1, p2) -> let csl1 = csl^"L" in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = csl^"R" in subprop_at_h p2 sp csl2 f
  | Or(p1, p2) -> let csl1 = csl^"L" in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = csl^"R" in subprop_at_h p2 sp csl2 f
  | Impl(p1, p2) -> let csl1 = csl^"L" in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = csl^"R" in subprop_at_h p2 sp csl2 f
  | Iff(p1, p2) -> let csl1 = csl^"L" in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = csl^"R" in subprop_at_h p2 sp csl2 f;;

exception NotSubProp;;

let rec subprop_at (p: prop) (sp: prop): string list = 
  let sl = subprop_at_h p sp "" [] in 
  match sl with
  | [] -> raise NotSubProp
  | _ -> sl;;

exception NOT_IN_RHO;;

let rec truth (p: prop) (r: rho):  bool = match p with
  | T -> true
  | F -> false
  | Not(p1) -> not(truth p1 r)
  | And(p1, p2) -> (truth p1 r) && (truth p2 r)
  | Or(p1, p2) -> (truth p1 r) || (truth p2 r)
  | Impl(p1, p2) -> let p3 = Or(Not(p1), p2) in truth p3 r
  | Iff(p1, p2) -> let p3 = And(Impl(p1, p2), Impl(p2, p1)) in truth p3 r
  | L(s) -> match r with 
    | Tbl(ht) -> if Hashtbl.mem (ht) (s) then Hashtbl.find (ht) (s) 
      else raise NOT_IN_RHO;;


let rec nnf (p: prop): prop = match p with 
  | Not(T) -> F
  | Not(F) -> T
  | And(p1, p2) -> And(nnf p1, nnf p2)
  | Or(p1, p2) -> Or(nnf p1, nnf p2)
  | Impl(p1, p2) -> Or(nnf(Not(p1)), nnf p2)
  | Iff(p1, p2) -> nnf(And(nnf(Impl(p1, p2)), nnf(Impl(p2, p1))))
  | Not(And(p1, p2)) -> Or(nnf(Not(p1)), nnf(Not(p2)))
  | Not(Or(p1, p2)) -> And(nnf(Not(p1)), nnf(Not(p2)))
  | Not(Not(p1)) -> nnf p1
  | _ -> p;;

exception CantConvert;;

let rec cnf_h (p: prop): prop = match p with
  | Or(p1, And(p2, p3)) -> And(cnf_h(Or(p1, p2)), cnf_h(Or(p1, p3)))
  | Or(And(p1, p2), p3) -> And(cnf_h(Or(p1, p3)), cnf_h(Or(p1, p3)))
  | _ -> p;;

let rec dnf_h (p: prop): prop = match p with
  | And(p1, Or(p2, p3)) -> Or(dnf_h(And(p1, p2)), dnf_h(And(p1, p3)))
  | And(Or(p1, p2), p3) -> Or(dnf_h(And(p1, p3)), dnf_h(And(p1, p3)))
  | _ -> p;;

let rec cnf_i (p: prop): prop = match p with 
  | Or(p1, p2) -> cnf_h(Or(cnf_i(p1), cnf_i(p2)))
  | And(p1, p2) -> And(cnf_i(p1), cnf_i(p2))
  | _ -> p;;

let rec dnf_i (p: prop): prop = match p with
  | And(p1, p2) -> dnf_h(And(dnf_i(p1), dnf_i(p2)))
  | Or(p1, p2) -> Or(dnf_i(p1), dnf_i(p2))
  | _ -> p;;

let rec cnf (p: prop): prop = cnf_i(nnf(p));;

let rec dnf (p: prop): prop = dnf_i(nnf(p));;

(* ****************************************************************************************** *)
(*                                           Examples                                         *)
(* ****************************************************************************************** *)

(* ******************************************************** *)
(*                      ht examples                         *)
(* ******************************************************** *)

let t1 = And(T, F);;
let t2 = Or(T, F);;
let t3 = Impl(t1, t2);;
let t4 = Iff(t3, t1);;
let t5 = Iff(Or(t2, t1), And(T, Impl(L("A"), F)));;

ht t1;;
ht t2;;
ht t3;;
ht t4;;

ht t5;;

(* ******************************************************** *)
(*                     size Examples                        *)
(* ******************************************************** *)

size t1;;
size t2;;
size t3;;
size t4;;

size t5;;

(* ******************************************************** *)
(*                  letters Examples                        *)
(* ******************************************************** *)

let a = Or(L("a"), L("w"));;
let b = And(L("b"), L("x"));;
let c = Impl(L("c"), L("y"));;
let d = Iff(L("d"), L("z"));;

let t6 = Iff(Impl(a, b), Impl(c, Or(L("a"), And(c, d))));;
let l1 = letters (t6);;

(* ******************************************************** *)
(*                   subprop Examples                       *)
(* ******************************************************** *)

let sp1 = subprop_at (Or(And(And(T,T),T), And(And(T,T),T))) (And(T, T));;
let sp2 = subprop_at t6 c;;

(* ******************************************************** *)
(*                   truth Examples                         *)
(* ******************************************************** *)

let h1 = Hashtbl.create 100;;
let h2 = Hashtbl.create 100;;
let h3 = Hashtbl.create 100;;
let h4 = Hashtbl.create 100;;

Hashtbl.add h1 "a" true;;
Hashtbl.add h1 "b" true;;
Hashtbl.add h2 "a" true;;
Hashtbl.add h2 "b" false;;
Hashtbl.add h3 "a" false;;
Hashtbl.add h3 "b" true;;
Hashtbl.add h4 "a" false;;
Hashtbl.add h4 "b" false;;

let tauto1 = Iff(Impl(L("a"), L("b")), Impl(Not(L("b")), Not(L("a"))));;
let truth1 = truth tauto1 (Tbl(h1));;
let truth1 = truth tauto1 (Tbl(h2));;
let truth1 = truth tauto1 (Tbl(h3));;
let truth1 = truth tauto1 (Tbl(h4));;

let tauto2 = Or(L("a"), Not(L("a")));;
let truth2 = truth tauto2 (Tbl(h1));;
let truth2 = truth tauto2 (Tbl(h2));;
let truth2 = truth tauto2 (Tbl(h3));;
let truth2 = truth tauto2 (Tbl(h4));;

let contra1 = Iff(And(L("a"), L("b")), Or(Not(L("a")), Not(L("b"))));;
let truth3 = truth contra1 (Tbl(h1));;
let truth3 = truth contra1 (Tbl(h2));;
let truth3 = truth contra1 (Tbl(h3));;
let truth3 = truth contra1 (Tbl(h4));;

let contra2 = And(L("b"), Not(L("b")));;
let truth4 = truth contra2 (Tbl(h1));;
let truth4 = truth contra2 (Tbl(h2));;
let truth4 = truth contra2 (Tbl(h3));;
let truth4 = truth contra2 (Tbl(h4));;

let conti1 = Impl(L("a"), Not(Impl(L("b"), L("a"))));;
let truth5 = truth conti1 (Tbl(h1));;
let truth5 = truth conti1 (Tbl(h2));;
let truth5 = truth conti1 (Tbl(h3));;
let truth5 = truth conti1 (Tbl(h4));;

let conti2 = Or(L("a"), L("b"));;
let truth6 = truth conti2 (Tbl(h1));;
let truth6 = truth conti2 (Tbl(h2));;
let truth6 = truth conti2 (Tbl(h3));;
let truth6 = truth conti2 (Tbl(h4));;

(* ******************************************************** *)
(*                    cnf, dnf and nnf                      *)
(* ******************************************************** *)

let p1 = And(And(And(And(Or(T, F), F), T), F), T);;
let d1 = dnf p1;;

let p2 = Iff(And(T,F), And(F, F));;
let d2 = dnf p2;;

let p3 = Or(And(T, F), Or(T, F));;
let c1 = cnf p2;;

let p4 = Impl(Iff(T, F), Not(T));;
let c2 = cnf p2;;

let p5 = Not(Not(Or(And(T, Not(F)), Not(And(L("a"), F)))));;
let n1 = nnf p5;;

(* ************************************************************************** *)
