type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type side = Lt | R
and rule = Hyp
         | TrueInt
         | ImplInt of node
         | ImplEli of node * node
         | Int of node
         | Class of node
         | AndInt of node * node
         | AndEli of node * side
         | OrInt of node * side
         | OrEli of node * node * node
and node = N of (prop list) * prop * rule;;

let rec is_present (v: 'a) (l: 'a list): bool = match l with
  | [] -> false
  | ls::lx -> if (ls=v) then true else (is_present v lx);;

let rec contains (l1: 'a list) (l2: 'a list): bool = match l1 with
  | [] -> true
  | l1s::l1x -> if (is_present l1s l2) then (contains l1x l2) else false;;

let rec list_equal (l1: 'a list) (l2: 'a list): bool = (contains l1 l2) && (contains l2 l1);;

let rec contains_except (l1: 'a list) (l2: 'a list) (v: 'a): bool  = match l1 with
  | [] -> true
  | l1s::l1x -> (if l1s=v then (contains_except l1x l2 v) 
                 else (if (is_present l1s l2) then (contains_except l1x l2 v) else false));;

let rec same_except (l1: 'a list) (l2: 'a list) (v: 'a): bool = 
  (contains l1 l2) && (contains_except l2 l1 v);;

let rec valid_ndprooftree (n: node): bool = match n with
  | N(pl, p, r) -> (match r with
      | Hyp -> if (is_present p pl) then true else false
      | TrueInt -> if p=T then true else false
      | ImplInt(n1) -> (match p with 
          | Impl(p1, p2) -> (match n1 with N(pl1, p3, r1) -> 
              if (same_except pl pl1 p1) && (p3=p2) && (is_present p1 pl1) then valid_ndprooftree n1
              else false)
          | _ -> false)
      | ImplEli(n1, n2) -> (match n1, n2 with 
          | N(pl1, Impl(p1, p2), r1), N(pl2, p3, r2) -> 
            (if (p1=p3) && (p=p2) && (list_equal pl pl1) && (list_equal pl pl2) 
             then (valid_ndprooftree n1) && (valid_ndprooftree n2)
             else false)
          | _ -> false)
      | Int(n1) -> (match n1 with 
          | N(pl1, p1, r1) -> if (p1=F) && (list_equal pl pl1) then valid_ndprooftree n1 else false)
      | Class(n1) -> (match n1 with
          | N(pl1, p1, r1) -> if (p1=F) && (list_equal pl pl1) then valid_ndprooftree n1 else false)
      | AndInt(n1, n2) -> (match p with 
          | And(p1, p2) -> (match n1, n2 with 
              | N(pl1, p3, r1), N(pl2, p4, r2) -> 
                if (list_equal pl pl1) && (list_equal pl pl2) && (p1=p3) && (p2=p4)
                then (valid_ndprooftree n1) && (valid_ndprooftree n2)  
                else false)
          | _ -> false)
      | AndEli(n1, s) -> (match n1 with 
          | N(pl1, And(p1, p2), r1) -> 
            if (((s=Lt) && (p=p1)) || ((s=R) && (p=p2)) && (list_equal pl pl1)) 
            then valid_ndprooftree n1 else false
          | _ -> false)
      | OrInt(n1, s) -> (match p with 
          | Or(p1, p2) -> (match n1 with 
              | N(pl1, p3, r1) -> 
                if (((s=Lt) && (p3=p1)) || ((s=R) && (p3=p2)) && (list_equal pl pl1)) 
                then valid_ndprooftree n1 else false)
          | _ -> false)
      | OrEli(n1, n2, n3) -> (match n1, n2, n3 with 
          | N(pl1, p1, r1), N(pl2, p2, r2), N(pl3, p3, r3) -> (match p1 with 
              | Or(p4, p5) -> 
                if (list_equal pl pl1) && (same_except pl pl2 p4) && (same_except pl pl3 p5) 
                   && (p2=p) && (p3=p)
                then (valid_ndprooftree n1) && (valid_ndprooftree n2) && (valid_ndprooftree n3)
                else false
              | _ -> false))
    )

let rec union_internal (l1: 'a list) (l2: 'a list): 'a list = match l1 with
  | [] -> l2
  | l1s::l1x -> if (is_present l1s l2) then (union_internal l1x l2) else (union_internal l1x (l1s::l2));;

let union (l1: 'a list) (l2: 'a list): 'a list = 
  let big_small r1 r2 = if ((List.length l1)>(List.length l2)) then (l1, l2) else (l2, l1) in 
  let l3, l4 = (big_small l1 l2) in
  union_internal l4 l3;;

let rec pad (n: node) (dpl: prop list): node = match n with
  | N(pl, p, r) -> (match r with 
      | Hyp -> N(union dpl pl, p, r)
      | TrueInt -> N(union dpl pl, p, r)
      | ImplInt(n1) -> N(union dpl pl, p, ImplInt(pad n1 dpl))
      | ImplEli(n1, n2) -> N(union dpl pl, p, ImplEli(pad n1 dpl, pad n2 dpl))
      | Int(n1) -> N(union dpl pl, p, Int(pad n1 dpl))
      | Class(n1) -> N(union dpl pl, p, Class(pad n1 dpl))
      | AndInt(n1, n2) -> N(union dpl pl, p, AndInt(pad n1 dpl, pad n2 dpl))
      | AndEli(n1, s) -> N(union dpl pl, p, AndEli(pad n1 dpl, s))
      | OrInt(n1, s) -> N(union dpl pl, p, OrInt(pad n1 dpl, s))
      | OrEli(n1, n2, n3) -> N(union dpl pl, p, OrEli(pad n1 dpl, pad n2 dpl, pad n3 dpl)))

let rec set_push (v: 'a) (l: 'a list): 'a list = if is_present v l then l else v::l;;

let rec prune_get_smallest (n: node) (apl: prop list) (opl: prop list): prop list = match n with
  | N(pl, p, r) -> (match r with 
      | Hyp -> if (is_present p opl) then set_push p apl else apl
      | TrueInt -> apl
      | ImplInt(n1) -> prune_get_smallest n1 apl opl
      | ImplEli(n1, n2) -> let apl1 = prune_get_smallest n1 apl opl in prune_get_smallest n2 apl1 opl
      | Int(n1) -> prune_get_smallest n1 apl opl
      | Class(n1) -> prune_get_smallest n1 apl opl
      | AndInt(n1, n2) -> let apl1 = prune_get_smallest n1 apl opl in prune_get_smallest n2 apl1 opl
      | AndEli(n1, s) -> prune_get_smallest n1 apl opl
      | OrInt(n1, s) -> prune_get_smallest n1 apl opl
      | OrEli(n1, n2, n3) -> let apl1 = prune_get_smallest n1 apl opl in 
        let apl2 = prune_get_smallest n2 apl1 opl in prune_get_smallest n3 apl2 opl);;

exception InvalidTree;;

let rec prune_place (n: node) (ppl: prop list): node = match n with
  | N(pl, p, r) -> (match r with 
      | Hyp -> N(ppl, p, r)
      | TrueInt -> N(ppl, p, r)
      | ImplInt(n1) -> (match p with 
          | Impl(p1, p2) -> N(ppl, p, ImplInt(prune_place n1 (set_push p1 ppl)))
          | _ -> raise InvalidTree)
      | ImplEli(n1, n2) -> N(ppl, p, ImplEli(prune_place n1 ppl, prune_place n2 ppl))
      | Int(n1) -> N(ppl, p, Int(prune_place n1 ppl))
      | Class(n1) -> N(ppl, p, Class(prune_place n1 (set_push (Not(p)) ppl)))
      | AndInt(n1, n2) -> N(ppl, p, AndInt(prune_place n1 ppl, prune_place n2 ppl))
      | AndEli(n1, s) -> N(ppl, p, AndEli(prune_place n1 ppl, s))
      | OrInt(n1, s) -> N(ppl, p, OrInt(prune_place n1 ppl, s))
      | OrEli(n1, n2, n3) -> (match n1 with 
          | N(pl1, Or(p1, p2), r1) -> 
            N(ppl, p, OrEli(prune_place n1 ppl, 
                            prune_place n2 (set_push p1 ppl), prune_place n3 (set_push p2 ppl)))
          | _ -> raise InvalidTree));;

let prune (n: node): node = match n with
  | N(pl, p, r) -> let ppl = prune_get_smallest n [] pl in prune_place n ppl;;

let rec get_proof (nl: node list) (p: prop): node = match nl with 
  | [] -> raise Not_found
  | nls::nlx -> (match nls with 
      | N(pl1, p1, r1) -> if (p1=p) then nls else get_proof nlx p);;


let rec graft_internal (n: node) (nl: node list) (ppl: prop list): node = match n with
  | N(pl, p, r) -> (match r with 
      | Hyp -> (try (pad (get_proof nl p) ppl) with Not_found -> N(ppl, p, r))
      | TrueInt -> N(ppl, p, r)
      | ImplInt(n1) -> (match p with
          | Impl(p1, p2) -> N(pl, p, ImplInt(graft_internal n1 nl (set_push p1 ppl)))
          | _ -> raise InvalidTree)
      | ImplEli(n1, n2) -> N(pl, p, 
                             ImplEli(graft_internal n1 nl ppl, graft_internal n2 nl ppl))
      | Int(n1) -> N(pl, p, Int(graft_internal n1 nl ppl))
      | Class(n1) -> N(pl, p, Class(graft_internal n1 nl (set_push (Not(p)) ppl)))
      | AndInt(n1, n2) -> N(pl, p, 
                            AndInt(graft_internal n1 nl ppl, graft_internal n2 nl ppl))
      | AndEli(n1, s) -> N(pl, p, AndEli(graft_internal n1 nl ppl, s))
      | OrInt(n1, s) -> N(pl, p, OrInt(graft_internal n1 nl ppl, s))
      | OrEli(n1, n2, n3) -> (match n1 with 
          | N(pl1, Or(p1, p2), r1) -> N(pl, p, 
                                        OrEli(graft_internal n1 nl ppl, 
                                              graft_internal n2 nl (set_push p1 ppl), 
                                              graft_internal n3 nl (set_push p2 ppl)))
          | _ -> raise InvalidTree));;

let graft (n: node) (nl: node list): node = match nl with
  | nls::nlx -> (match nls with 
      | N(pl1, p1, r1) -> graft_internal n nl pl1)
  | [] -> n;;

(* Test cases *)

(* Test Case 1 - Hyp, TrueInt ImplInt*)
let a = N([], Impl(L("x"), L("x")), ImplInt(N([L("x")], L("x"), Hyp)));;
valid_ndprooftree a;;
let b = pad a [L("y")];;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;

(* Test Case 2 - ImplEli, OrEli*)
let d = N([L("y"); Impl(L("y"), L("x"))], L("x"), 
          ImplEli(
            N([L("y"); Impl(L("y"), L("x"))], Impl(L("y"), L("x")), Hyp), 
            N([L("y"); Impl(L("y"), L("x"))], L("y"), Hyp)));;

valid_ndprooftree d;;
let e = pad d [L("z")];;
valid_ndprooftree e;;
let f = prune e;;
valid_ndprooftree f;;

let gamma1 = [Or(L("p"),L("q")); L("p"); L("q"); Impl(L("p"), L("y"));
              Impl(L("q"), L("y")); Impl(L("p"), L("x"))];;
let gr = N(gamma1, L("y"), 
           OrEli(
             N(gamma1, Or(L("p"),L("q")), Hyp), 
             N(gamma1, L("y"), ImplEli(N(gamma1, Impl(L("p"), L("y")), Hyp), N(gamma1, L("p"), Hyp))), 
             N(gamma1, L("y"), ImplEli(N(gamma1, Impl(L("q"), L("y")), Hyp), N(gamma1, L("q"), Hyp)))));;

valid_ndprooftree gr;;

let gamma_t = [L("y")]@gamma1;;
let gr2 = N(gamma1, Impl(L("y"), L("x")), 
            ImplInt(
              N(gamma_t, L("x"), ImplEli(
                  N(gamma_t, Impl(L("p"), L("x")) , Hyp),
                  N(gamma_t, L("p"), Hyp)
                ))));;
let g = graft e [gr;gr2];;
valid_ndprooftree g;;

(* Test Case 3 - AndInt, OrInt L, TrueInt *)
let gamma2 = [L("p");L("q")];;

let h = N(gamma2, And(Or(L("p"), L("q")), And(T, L("q"))), 
          AndInt(N(gamma2, Or(L("p"), L("q")), 
                   OrInt(N(gamma2, L("p"), Hyp), Lt)), 
                 N(gamma2, And(T, L("q")), 
                   AndInt(
                     N(gamma2, T, TrueInt), 
                     N(gamma2, L("q"), Hyp)
                   ))));;


valid_ndprooftree h;;
let i = pad h ([L("z")]);;
valid_ndprooftree i;;
let j = prune i;;
valid_ndprooftree j;;

(* Test Case 4 - AndELi L, AndEli R *)
let gamma3 = [And(L("r"),And(L("p"), L("q")))];;
let k = N(gamma3, L("p"), 
          AndEli(
            N(gamma3, And(L("p"), L("q")), 
              AndEli(N(gamma3, And(L("r"), And(L("p"), L("q"))), Hyp), 
                     R)), 
            Lt)
         );;

valid_ndprooftree k;;
let l = pad k ([L("z")]);;
valid_ndprooftree l;;
let m = prune l;;
valid_ndprooftree m;;

(* Test Case 5 - OrInt R, Int *)
let gamma4 = [L("p"); Impl(L("p"), F)];;
let n = N(gamma4, Or(L("r"), L("q")), 
          OrInt(N(gamma4, L("q"), 
                  Int(N(gamma4, F, 
                        ImplEli(
                          N(gamma4, Impl(L("p"), F), Hyp),
                          N(gamma4, L("p"), Hyp)
                        )))), 
                R));;
valid_ndprooftree n;;
let o = pad n ([L("z")]);;
valid_ndprooftree o;;
let p = prune o;;
valid_ndprooftree p;;
