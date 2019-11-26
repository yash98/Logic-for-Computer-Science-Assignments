type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop 
          | Impl of prop * prop | Iff of prop * prop;;

type value = V of prop * bool;;
type status = Examined | Unexamined | Closed;;
(* Node is valule, status, children list, Unexplored propositions till now, assignment till now *)
type node = N of value * status * (node list) * (value list) * ((string*bool) list);;

exception ShouldNotOccur;;

let rec getPreExisting (bsl: (string*bool) list) (s: string): bool*bool = match bsl with
  | [] -> (false, false)
  | ss::sx -> match ss with (rs, b) -> if (rs=s) then (true, b) else getPreExisting sx s;;

let rec contrad_path (n: node) (assig: (string*bool) list) (nl: node list): node*(node list) = match n with
  | N(_, Closed, _, _, _) -> (n, nl)
  | N(V(T, false), _, _, _, assigL) -> (N(V(T, false), Closed, [], [], assigL), n::nl)
  | N(V(F, true), _, _, _, assigL) -> (N(V(F, true), Closed, [], [], assigL), n::nl)
  | N(V(T, true), st, childL, vl, assigL) -> (match childL with
      | child1::[] -> let modChild, nl1 = contrad_path child1 assigL nl in
        (N(V(T, true), st, [modChild], vl, assigL), nl1)
      | [] -> (N(V(T, true), st, [], vl, assigL), nl)
      | _-> raise ShouldNotOccur)
  | N(V(F, false), st, childL, vl, assigL) -> (match childL with
      | child1::[] -> let modChild, nl1 = contrad_path child1 assigL nl in
        (N(V(F, false), st, [modChild], vl, assigL), nl1)
      | [] -> (N(V(T, true), st, [], vl, assigL), nl)
      | _ -> raise ShouldNotOccur)
  | N(V(L(s), b), _, childL, vl, assigL) ->
    (let (p1, b1) = getPreExisting assigL s in
     match childL with
     | child1::[] ->
       if p1 then 
         if (b1=b) then  
           let (modChild, nl1) = contrad_path child1 assigL nl in
           (N(V(L(s), b), Examined, [modChild], vl, assigL), nl1)
         else
           (N(V(L(s), b), Closed, [], vl, (s, b)::assigL), n::nl)
       else 
         let (modChild, nl1) = contrad_path child1 ((s, b)::assigL) nl in
         (N(V(L(s), b), Examined, [modChild], vl, (s, b)::assigL), nl1)
     | [] ->
       if p1 then 
         if (b1=b) then  
           (N(V(L(s), b), Examined, [], vl, assigL), nl)
         else
           (N(V(L(s), b), Closed, [], vl, (s, b)::assigL), n::nl)
       else 
         (N(V(L(s), b), Examined, [], vl, (s, b)::assigL), nl)
     | _-> raise ShouldNotOccur)
  | N(v, st, childL, vl, assigL) -> (let rec dfs (nl1: node list) (assig1: (string*bool) list) (rnl1: (node list)*(node list)): (node list)*(node list) = (match nl1, rnl1 with
      | ([], _) -> rnl1
      | (nlx::nls, (r1, r2)) -> let (n2, nl2) = contrad_path nlx assig1 [] in
        let (rnl21, rnl22) = (dfs nls assig1 (r1, r2)) in ([n2]@rnl21, nl2@rnl22)) in
     let nl2, nl3 = (dfs childL assigL ([], [])) in 
     (N(v, st, nl2, vl, assigL), nl3@nl)
    );;

let rec select_node (n: node) (nl: node list): node list = 
  match n with 
  | N(_, Unexamined, _, _, _) -> n::nl
  | N(_, Closed, _, _, _) -> nl
  | N(V(L(s), b), Examined, _, _, _) -> nl
  | N(V(Not(p1), b), Examined, c0::[], _, _) -> select_node c0 nl
  | N(V(And(p1, p2), b), Examined, c0::c1::[], _, _) -> 
    let nl1 = select_node c0 nl in select_node c1 nl1
  | N(V(Or(p1, p2), b), Examined, c0::c1::[], _, _) -> 
    let nl1 = select_node c0 nl in select_node c1 nl1
  | N(V(Impl(p1, p2), b), Examined, c0::c1::[], _, _) -> 
    let nl1 = select_node c0 nl in select_node c1 nl1
  | N(V(Iff(p1, p2), b), Examined, c0::c1::[], _, _) -> 
    let nl1 = select_node c0 nl in select_node c1 nl1
  | _ -> raise ShouldNotOccur;;


let rec getPreExisting (bsl: (string*bool) list) (s: string): bool*bool = match bsl with
  | [] -> (false, false)
  | ss::sx -> match ss with (rs, b) -> if (rs=s) then (true, b) else getPreExisting sx s;;

let rec find_assignments (n: node) (bsll: (((string*bool) list)*status) list): node*((((string*bool) list)*status) list) = 
  match n with
  (* base cases *) 

  (* Closed and Examined with nothing else left *)
  | N(V(T, false), _, _, _, assignL) -> (N(V(T, false), Closed, [], [], assignL), (assignL, Closed)::bsll)
  | N(V(F, true), _, _, _, assignL) -> (N(V(F, true), Closed, [], [], assignL), (assignL, Closed)::bsll)

  (*unexplored is empty *)
  (* Variable *) 
  | N(V(L(s), b), 
      Unexamined, 
      childL, 
      [], 
      assignL) -> 
    let (p1, b1) = getPreExisting assignL s in 
    if p1 then 
      if (b1=b) then  
        (N(V(L(s), b), Examined, [], [], assignL), (assignL, Examined)::bsll)
      else
        let bsl1 = (s, b)::assignL in
        (N(V(L(s), b), Closed, [], [], bsl1), (bsl1, Closed)::bsll)
    else 
      let bsl1 = (s, b)::assignL in
      (N(V(L(s), b), Examined, [], [], bsl1), (bsl1, Examined)::bsll)

  (* T *)
  | N(V(T, true), 
      Unexamined, 
      childL, 
      [], 
      assignL) -> (N(V(T, true), Examined, [], [], assignL), (assignL, Examined)::bsll)

  (* F *)
  | N(V(F, false), 
      Unexamined, 
      childL, 
      [], 
      assignL) -> (N(V(F, false), Examined, [], [], assignL), (assignL, Examined)::bsll)

  (* continuation cases *)

  (* Variable *) 
  | N(V(L(s), b), 
      Unexamined, 
      childL, 
      nextV::restVL, 
      assignL) -> 
    let (p1, b1) = getPreExisting assignL s in 
    if p1 then 
      if (b1=b) then  
        let (retN, retBSL) = (find_assignments (N(nextV, Unexamined, [], restVL, assignL)) bsll) in
        (N(V(L(s), b), Examined, [retN], restVL, assignL), retBSL)
      else
        let bsl1 = (s, b)::assignL in
        (N(V(L(s), b), Closed, [], [], bsl1), (bsl1, Closed)::bsll)
    else 
      let (retN, retBSL) = (find_assignments (N(nextV, Unexamined, [], restVL, (s, b)::assignL)) bsll) in
      (N(V(L(s), b), Examined, [retN], restVL, (s, b)::assignL), retBSL)

  (* T *)
  | N(V(T, true), 
      Unexamined, 
      childL, 
      nextV::restVL, 
      assignL) ->
    let (retN, retBSL) = (find_assignments (N(nextV, Unexamined, [], restVL, assignL)) bsll) in
    (N(V(T, true), Examined, [retN], nextV::restVL, assignL), retBSL)

  (* F *)
  | N(V(F, false), 
      Unexamined, 
      childL, 
      nextV::restVL, 
      assignL) ->
    let (retN, retBSL) = (find_assignments (N(nextV, Unexamined, [], restVL, assignL)) bsll) in
    (N(V(F, false), Examined, [retN], nextV::restVL, assignL), retBSL)

  (* Not *)
  | N(V(Not(p), b), 
      Unexamined, 
      childL, 
      uxvl, 
      assignL) ->
    let (retN, retBSL) = (find_assignments (N(V(p, not(b)), Unexamined, [], uxvl, assignL)) bsll) in
    (N(V(Not(p), b), Examined, [retN], uxvl, assignL), retBSL)

  (* non branching binary nodes i.e. alpha *)
  (* And *)
  | N(V(And(p1, p2), true),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) ->
    let (retN, retBSL) = (find_assignments (N(V(p1, true), Unexamined, [], V(p2, true)::uxvl, assignL)) bsll) in
    (N(V(And(p1, p2), true), Examined, [retN], uxvl, assignL), retBSL)

  (* Or *)
  | N(V(Or(p1, p2), false),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) ->
    let (retN, retBSL) = (find_assignments (N(V(p1, false), Unexamined, [], V(p2, false)::uxvl, assignL)) bsll) in
    (N(V(Or(p1, p2), false), Examined, [retN], uxvl, assignL), retBSL)

  (* Impl *)
  | N(V(Impl(p1, p2), false),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) ->
    let (retN, retBSL) = (find_assignments (N(V(p1, false), Unexamined, [], V(p2, true)::uxvl, assignL)) bsll) in
    (N(V(Impl(p1, p2), false), Examined, [retN], uxvl, assignL), retBSL)

  (* branching binary nodes i.e. beta *)
  (* And *)
  | N(V(And(p1, p2), false),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) -> 
    let (retN1, retBSL1) = (find_assignments (N(V(p1, false), Unexamined, [], uxvl, assignL)) bsll) in
    let (retN2, retBSL2) = (find_assignments (N(V(p2, false), Unexamined, [], uxvl, assignL)) retBSL1) in
    (N(V(And(p1, p2), false), Examined, retN1::[retN2], uxvl, assignL), retBSL2)

  (* Or *)
  | N(V(Or(p1, p2), true),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) -> 
    let (retN1, retBSL1) = (find_assignments (N(V(p1, true), Unexamined, [], uxvl, assignL)) bsll) in
    let (retN2, retBSL2) = (find_assignments (N(V(p2, true), Unexamined, [], uxvl, assignL)) retBSL1) in
    (N(V(Or(p1, p2), false), Examined, retN1::[retN2], uxvl, assignL), retBSL2)

  (* Impl *)
  | N(V(Impl(p1, p2), true),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) -> 
    let (retN1, retBSL1) = (find_assignments (N(V(p1, false), Unexamined, [], uxvl, assignL)) bsll) in
    let (retN2, retBSL2) = (find_assignments (N(V(p2, true), Unexamined, [], uxvl, assignL)) retBSL1) in
    (N(V(Impl(p1, p2), false), Examined, retN1::[retN2], uxvl, assignL), retBSL2)

  (* Iff *)
  | N(V(Iff(p1, p2), true),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) -> 
    let (retN1, retBSL1) = (find_assignments (N(V(p1, false), Unexamined, [], V(p2, false)::uxvl, assignL)) bsll) in
    let (retN2, retBSL2) = (find_assignments (N(V(p1, true), Unexamined, [], V(p2, true)::uxvl, assignL)) retBSL1) in
    (N(V(Iff(p1, p2), false), Examined, retN1::[retN2], uxvl, assignL), retBSL2)

  (* Iff *)
  | N(V(Iff(p1, p2), false),
      Unexamined, 
      childL, 
      uxvl, 
      assignL) -> 
    let (retN1, retBSL1) = (find_assignments (N(V(p1, true), Unexamined, [], V(p2, false)::uxvl, assignL)) bsll) in
    let (retN2, retBSL2) = (find_assignments (N(V(p1, false), Unexamined, [], V(p2, true)::uxvl, assignL)) retBSL1) in
    (N(V(Iff(p1, p2), false), Examined, retN1::[retN2], uxvl, assignL), retBSL2)

  | _ -> raise ShouldNotOccur;;


let rec step_develop (n: node): node = let (reqN, assig) = find_assignments n [] in
  reqN;;


let rec check_tautology (p: prop): bool*(((string * bool) list) list) = 
  let (n, leafAssign) = find_assignments (N(V(p, true), Unexamined, [], [], [])) [] in
  let rec seeAndFindCounter (la: (((string*bool)list)*status) list) (acc: bool*(((string * bool) list) list)): bool*(((string * bool) list) list) = 
    match la, acc with
    | [], _ -> acc
    | las::lax, (b, al) -> match las with
      | (assign, stat) -> 
        if (stat=Examined) then (true&&b, al)
        else (false&&b, assign::al)
  in
  seeAndFindCounter leafAssign (true, []);;

let rec check_contradiction (p: prop): bool*(((string * bool) list) list) = 
  let (n, leafAssign) = find_assignments (N(V(p, false), Unexamined, [], [], [])) [] in
  let rec seeAndFindCounter (la: (((string*bool)list)*status) list) (acc: bool*(((string * bool) list) list)): bool*(((string * bool) list) list) = 
    match la, acc with
    | [], _ -> acc
    | las::lax, (b, al) -> match las with
      | (assign, stat) -> 
        if (stat=Examined) then (true&&b, al)
        else (false&&b, assign::al)
  in
  seeAndFindCounter leafAssign (true, []);;

let p = Iff(Impl(L("a"), L("b")), Impl(Not(L("b")), Not(L("a"))));;
let (a, b) = find_assignments (N(V(p, true), Unexamined, [], [], [])) [];;
(* let p = Impl(Impl(L "p1", Impl(L "p2", L "p3")), Impl(Impl(L "p1", L "p2"), Impl(L "p1", L "p3")));; *)
(* let p = Iff(L("a"), Not(L("a")));; *)
(* let p = Impl(L "p", Impl(L "q", L "p"));;
   let (a, b) = find_assignments (N(V(p, false), Unexamined, [], [], [])) [];; *)
(* 
let p1 = Iff(Impl(L("a"), L("b")), Impl(Not(L("b")), Not(L("a"))));;
let (n, leafAssign) = find_assignments (N(V(p, true), Unexamined, [], [], [])) []
let b1 = check_tautology p1;;
let b3 = check_contradiction p1;;

let p2 = Iff(Impl(L("a"), L("b")), Not(Impl(Not(L("b")), Not(L("a")))));;
let (n, leafAssign) = find_assignments (N(V(p, true), Unexamined, [], [], [])) []
let b2 = check_contradiction p2;;
let b4 = check_tautology p2;; *)
