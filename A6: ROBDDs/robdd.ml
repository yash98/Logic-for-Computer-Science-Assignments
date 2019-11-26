type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type triple = Trip of int*int*int;;

type t_tbl = T_tbl of (triple) Array.t;;
type h_tbl = H_tbl of (triple, int) Hashtbl.t;;

type robdd = ROBDD of t_tbl * h_tbl * int ref;;

let init_T (size: int): triple array = Array.make size (Trip(-1, -1, -1));;

let init_H (size: int): (triple, int) Hashtbl.t = Hashtbl.create ~random:false size;;

let member_H (r: robdd) (tr: triple): bool = match r with 
  | ROBDD(_, H_tbl(ht), _) -> Hashtbl.mem ht tr;;

let lookup_H (r: robdd) (tr: triple): int = match r with 
  | ROBDD(_, H_tbl(ht), _) -> Hashtbl.find ht tr;;

let insert_H (r: robdd) (tr: triple) (u: int) = match r with 
  | ROBDD(_, H_tbl(ht), _) -> Hashtbl.add ht tr u;;

let lookup_T (r: robdd) (u: int): triple = match r with 
  | ROBDD(T_tbl(tt), h, s) -> Array.get tt u;;

(* let add_T (r: robdd) (tr: triple): robdd * int = match r with
   | ROBDD(T_tbl(tt), h, p, vl, s) -> let i = s+1 in let _ = Array.set tt s tr in ROBDD(T_tbl(tt), h, p, vl, i), i;; *)

let add_T (r: robdd) (tr: triple): int = match r with
  | ROBDD(T_tbl(tt), h, s) -> let _ = Array.set tt !s tr in s := !s + 1; !s -1;;

let init_robdd (n1: int) (n2: int) (num_vars: int): robdd = 
  let t = init_T n1 in let _ = Array.set t 0 (Trip(num_vars+1, -1, -1)) in let _ = Array.set t 1 (Trip(num_vars+1, -1, -1)) in
  let h = init_H n2 in ROBDD(T_tbl(t), H_tbl(h), ref 2);;

let mk (r: robdd) (i: int) (l: int) (h: int): int = 
  if l = h then l
  else let tr = Trip(i, l, h) in 
    if member_H r tr then lookup_H r tr
    else let u = add_T r tr in let _ = insert_H r tr u in u;;

exception NOT_REPLACED;;

let rec truth (p: prop): bool = match p with
  | T -> true
  | F -> false
  | Not(p1) -> not(truth p1)
  | And(p1, p2) -> (truth p1) && (truth p2)
  | Or(p1, p2) -> (truth p1) || (truth p2)
  | Impl(p1, p2) -> let p3 = Or(Not(p1), p2) in truth p3
  | Iff(p1, p2) -> let p3 = And(Impl(p1, p2), Impl(p2, p1)) in truth p3
  | L(s) -> raise NOT_REPLACED;;

let rec subst1 (p: prop) (v: string) (b: bool): prop = match p with
  |T -> T 
  | F -> F 
  | L(s) -> if s=v then (if b then T else F) else L(s) 
  | Not(p1) -> Not(subst1 p1 v b) 
  | And(p1, p2) -> And(subst1 p1 v b, subst1 p2 v b) 
  | Or(p1, p2) -> Or(subst1 p1 v b, subst1 p2 v b) 
  | Impl(p1, p2) -> Impl(subst1 p1 v b, subst1 p2 v b) 
  | Iff(p1, p2) -> Iff(subst1 p1 v b, subst1 p2 v b);;

let rec build_internal (r: robdd) (p: prop) (vl: string list) (index: int): int = match vl with
  | [] -> if truth p then 1 else 0
  | vls::vlx -> let v0 = build_internal r (subst1 p vls false) vlx (index+1) in 
    let v1 = build_internal r (subst1 p vls true) vlx (index+1) in 
    mk r index v0 v1;;

let build (r: robdd) (p: prop) (ordering: string list) = build_internal r p ordering 0;;

type double = Dou of int * int;;

exception UNEXPECTED;;

let oper_helper3 (i: int): bool = if i=0 then false else true;;

let oper_helper2 (b: bool): int = if b then 1 else 0;;

let rec oper_helper1 (u1: bool) (u2: bool) (op: string): bool= match op with
  | "OR" -> u1 || u2
  | "AND" -> u1 && u2
  | "IMPL" -> not(u1) || u2
  | "IFF" -> (not(u1) || u2) && (not(u2) || u1)
  | _ -> raise UNEXPECTED;;

let oper (u1: int) (u2: int) (op: string): int = oper_helper2 (oper_helper1 (oper_helper3 u1) (oper_helper3 u2) op);;

let lookup_T_spec (r: robdd) (u: int) (opt: int): int = let ilh = lookup_T r u in match ilh with 
  | Trip(i, l, h) -> (match opt with
      | 0 -> i
      | 1 -> l
      | _ -> h);;

let rec apply_internal (r: robdd) (u1: int) (u2: int) (op: string) (g: ((double, int) Hashtbl.t)): int = let d = Dou(u1, u2) in
  if Hashtbl.mem g d then Hashtbl.find g d
  else (if ((u1 = 0)||(u1 = 1)) && ((u2 = 0)||(u2 = 1)) then let u = oper u1 u2 op in Hashtbl.add g d u; u
        else 
          let v1 = lookup_T_spec r u1 0 in let v2 = lookup_T_spec r u2 0 in 
          let l1 = lookup_T_spec r u1 1 in let l2 = lookup_T_spec r u2 1 in 
          let h1 = lookup_T_spec r u1 2 in let h2 = lookup_T_spec r u2 2 in 
          (if v1 = v2 then let u = mk r v1 (apply_internal r l1 l2 op g) (apply_internal r h1 h2 op g) in Hashtbl.add g d u; u 
           else (if v1 < v2 then let u = mk r v1 (apply_internal r l1 u2 op g) (apply_internal r h1 u2 op g) in Hashtbl.add g d u; u 
                 else let u = mk r v2 (apply_internal r u1 l2 op g) (apply_internal r u1 h2 op g) in Hashtbl.add g d u; u)));;

let apply (r: robdd) (u1: int) (u2: int) (op: string) = let g = Hashtbl.create ~random:false 999 in apply_internal r u1 u2 op g;;

let restrict (r: robdd) (u0: int) (j: int) (b: int): int = 
  let rec res (u: int):int = let vlh = lookup_T r u in match vlh with
    | Trip(v, l, h) -> if v>j then u else 
        (if v<j then mk r v (res(l)) (res(h))
         else (if b=0 then res(l) else res(h))) in
  res u0;;

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
  | Or(And(p1, p2), p3) -> And(cnf_h(Or(p1, p3)), cnf_h(Or(p2, p3)))
  | _ -> p;;

let rec dnf_h (p: prop): prop = match p with
  | And(p1, Or(p2, p3)) -> Or(dnf_h(And(p1, p2)), dnf_h(And(p1, p3)))
  | And(Or(p1, p2), p3) -> Or(dnf_h(And(p1, p3)), dnf_h(And(p2, p3)))
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

(* testcases *)

(*
 Ordering: x1 < x2 < x3
 *)
let vx1 = L("1");;
let vx2 = L("2");;
let vx3 = L("3");;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

let order = ["1"; "2"; "3"];;
let global_robdd = init_robdd 40 9999 2;;

(* compute NNF, CNF of p1 and Not(p1) *)

let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

(* build ROBDDs *)
let tt = build global_robdd T order;;
let tf = build global_robdd F order;;

let tvx1 = build global_robdd vx1 order;;
let tp2 = build global_robdd p2 order;;
let tp0 = build global_robdd p0 order;;
let tp1 = build global_robdd p1 order;;
let tp1' = build global_robdd p1' order;;
let tp1'' = build global_robdd p1'' order;;

let tnp1 = build global_robdd np1 order;;
let tnp1' = build global_robdd np1' order;;
let tnp1'' = build global_robdd np1'' order;;

(* Testcase #1 *)
tp1 == tp1';;
tp1 == tp1'';;
tnp1 == tnp1';;
tnp1 == tnp1'';;

global_robdd;;

(* Testcase #2 *)
let tp1anp1 = apply global_robdd tp1 tnp1 "AND";;
tp1anp1 == tf;;
let tp1onp1 = apply global_robdd tp1 tnp1 "OR";;
tp1onp1 == tt;;

global_robdd;;

(* Testcase #3 *)
let tp1rv30 = restrict global_robdd tp1 2 0;;
tp1rv30 == tp0;;
let tp1rv31 = restrict global_robdd tp1 2 1;;
tp1rv31 == tt;;

global_robdd;;
