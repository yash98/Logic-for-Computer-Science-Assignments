type prop = T | F | V of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type triple = Trip of int*int*int;;

type t_tbl = T_tbl of (triple) Array.t;;
type h_tbl = H_tbl of (triple, int) Hashtbl.t;;

type robdd = ROBDD of t_tbl * h_tbl * prop * (string list) * int;;

let init_T (size: int): triple array = Array.make size (Trip(-1, -1, -1));;

let init_H (size: int): (triple, int) Hashtbl.t = Hashtbl.create ~random:false size;;

let init_robdd (n1: int) (n2: int) (p: prop) (var_order: string list) (num_vars: int): robdd = 
  let t = init_T n1 in let _ = Array.set t 0 (Trip(num_vars+1, -1, -1)) in let _ = Array.set t 1 (Trip(num_vars+1, -1, -1)) in
  let h = init_H n2 in ROBDD(T_tbl(t), H_tbl(h), p, var_order, 2);;

(* let mk (r: robdd) (i: int) * (l: int) * (h: int): int = match r with
   | t_t, h_t -> if l = h then l
    else if (Hashtbl.mem h_t (i, l, h)) then Hashtbl.find h_t (i, l, h)
    else  *)
