type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type triple = Trip of int*int*int;;

type t_tbl = T_tbl of (triple) Array.t;;
type h_tbl = H_tbl of (triple, int) Hashtbl.t;;

type robdd = ROBDD of t_tbl * h_tbl * prop * int;;

let init_T (size: int): triple array = Array.make size (Trip(-1, -1, -1));;

let init_H (size: int): (triple, int) Hashtbl.t = Hashtbl.create ~random:false size;;

let member_H (r: robdd) (tr: triple): bool = match r with 
  | ROBDD(_, H_tbl(ht), _, _) -> Hashtbl.mem ht tr;;

let lookup_H (r: robdd) (tr: triple): int = match r with 
  | ROBDD(_, H_tbl(ht), _, _) -> Hashtbl.find ht tr;;

let insert_H (r: robdd) (tr: triple) (u: int) = match r with 
  | ROBDD(_, H_tbl(ht), _, _) -> Hashtbl.add ht tr u;;

let lookup_T (r: robdd) (u: int): triple = match r with 
  | ROBDD(T_tbl(tt), h, p, s) -> Array.get tt u;;

(* let add_T (r: robdd) (tr: triple): robdd * int = match r with
   | ROBDD(T_tbl(tt), h, p, vl, s) -> let i = s+1 in let _ = Array.set tt s tr in ROBDD(T_tbl(tt), h, p, vl, i), i;; *)

let add_T (r: robdd) (tr: triple): int = match r with
  | ROBDD(T_tbl(tt), h, p, vl, s) -> let i = s+1 in let _ = Array.set tt s tr in i;;

let init_robdd (n1: int) (n2: int) (p: prop) (num_vars: int): robdd = 
  let t = init_T n1 in let _ = Array.set t 0 (Trip(num_vars+1, -1, -1)) in let _ = Array.set t 1 (Trip(num_vars+1, -1, -1)) in
  let h = init_H n2 in ROBDD(T_tbl(t), H_tbl(h), p, 2);;

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
  | vls::vlx -> let v0 = build_internal r (subst1 p vls true) vlx index+1 in 
    let v1 = build_internal r (subst1 p vls true) vlx index+1 in 
    mk r index v0 v1;;

let build (r: robdd) (p: prop) (ordering: string list) = build_internal r p ordering 0;;

