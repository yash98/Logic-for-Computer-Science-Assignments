type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type node = N of prop * n_info
and n_info = Ass | K | S | R | MP of node * node;;

type gamma = G of prop list;;
type hsproof = P of node * gamma;;

let rec is_present (v: 'a) (l: 'a list):bool = match l with
  | [] -> false
  | ls::lx -> if (ls=v) then true else (is_present v lx);;

let rec v_nodes_acc_to_gamma (n: node) (pl: prop list): bool = match n with
  | N(p1, Ass) -> (is_present p1 pl)
  | N(Impl(p1, Impl(p2, p3)), K) -> if (p1=p3) then true else false
  | N(Impl(Impl(p1, Impl(p2, p3)), Impl(Impl(p4, p5), Impl(p6, p7))), S) ->
    if (p1=p4) && (p1=p6) && (p2=p7) && (p3=p5) then true else false
  | N(Impl(Impl(Not(p1), Not(p2)), Impl(Impl(Not(p3), p4), p5)), R) ->
    if (p1=p3) && (p1=p5) && (p2=p4) then true else false
  | N(p1, MP(n1, n2)) -> (match n1, n2 with 
      | N(Impl(p2, p3), _), N(p4, _) ->
        if (p2=p4) && (p1=p3) then (v_nodes_acc_to_gamma n1 pl) && (v_nodes_acc_to_gamma n2 pl) else false
      | _, _ -> false)
  | _ -> false;;

let valid_hprooftree (pr: hsproof): bool = match pr with
  | P(n, G(pl)) -> (v_nodes_acc_to_gamma n pl);;

let rec union_internal (l1: 'a list) (l2: 'a list): 'a list = match l1 with
  | [] -> l2
  | l1s::l1x -> if (is_present l1s l2) then (union_internal l1x l2) else (union_internal l1x (l1s::l2));;

let union (l1: 'a list) (l2: 'a list): 'a list = 
  let big_small r1 r2 = if ((List.length l1)>(List.length l2)) then (l1, l2) else (l2, l1) in 
  let l3, l4 = (big_small l1 l2) in
  union_internal l4 l3;;

let pad (pr: hsproof) (g: gamma): hsproof = match pr, g with
  | P(n, G(pl1)), G(pl2) -> P(n, G(union pl1 pl2));;

let rec smallest_gamma (n: node): prop list = match n with
  | N(p, Ass) -> [p]
  | N(p, MP(n1, n2)) -> union (smallest_gamma n1) (smallest_gamma(n2))
  | _ -> [];;

let prune (pr: hsproof): hsproof = match pr with
  | P(n, G(pl)) -> P(n, G(smallest_gamma n));;

let rec place (n: node) (nl: node list): node = match n with
  | N(p, Ass) -> 
    let f (n1: node):bool = (match n1 with | N(p1, _) -> (p1=p)) in List.find (f) nl
  | N(p, MP(n1, n2)) -> N(p, MP(place n1 nl, place n2 nl))
  | _ -> n;;

let rec proof_list_to_node_list (prl: hsproof list) (nl: node list): node list = match prl with
  | [] -> nl
  | P(n, _)::prlx -> proof_list_to_node_list prlx (n::nl);;

let graft (pr: hsproof) (prl: hsproof list): hsproof = match pr, prl with
  | pr1, [] -> pr1
  | P(n, G(pl)), P(n1, g)::prlx -> P(place n (proof_list_to_node_list prl []), g);;

let rec remove_from_list (v: 'a) (l: 'a list) (r: 'a list): 'a list = match l with
  | [] -> r
  | ls::lx -> if (ls=v) then remove_from_list v lx r else remove_from_list v lx (ls::r);;

exception Invalid_proof_tree;;

let rec dedthm_internal (n: node) (p: prop) (pl: prop list): node = match n with
  | N(p1, MP(n1, n2)) -> (match n1, n2 with 
      | N(Impl(p2, p3), _), N(p4, _) -> if (p1=p3) && (p2=p4) then 
          N(Impl(p, p1), 
            MP(
              N(Impl(Impl(p, p2), Impl(p, p1)), 
                MP(
                  N(Impl(Impl(p, Impl(p2, p1)), Impl(Impl(p, p2), Impl(p, p1))), S),
                  (dedthm_internal n1 p pl))), 
              (dedthm_internal n2 p pl))) 
        else raise Invalid_proof_tree
      | _ -> raise Invalid_proof_tree)  
  | N(p1, t) -> (if (p1=p) then
                   let pp = Impl(p, p) in
                   let qp = Impl(p, Impl(L("q"), p)) in
                   let rp = Impl(p, Impl(Impl(L("q"), p), p)) in
                   N(pp , MP(N(Impl(qp, pp), MP(N(Impl(rp, Impl(qp, pp)), S), N(rp, K))), N(qp, K)))
                 else 
                   (if (is_present p1 pl) then N(Impl(p, p1), MP(N(Impl(p1, Impl(p, p1)), K), N(p1, t))) 
                    else raise Invalid_proof_tree));;

let dedthm (pr: hsproof) (p: prop): hsproof = match pr with 
  | P(n, G(pl)) -> 
    let rem_p_pl = (remove_from_list p pl []) in P((dedthm_internal n p rem_p_pl), G(rem_p_pl));;