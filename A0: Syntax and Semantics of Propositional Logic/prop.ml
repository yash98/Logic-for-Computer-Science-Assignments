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
  | Not(p1) -> let csl1 = "B"^csl in subprop_at_h p1 sp csl1 sls
  | And(p1, p2) -> let csl1 = "L"^csl in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = "R"^csl in subprop_at_h p1 sp csl2 f
  | Or(p1, p2) -> let csl1 = "L"^csl in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = "R"^csl in subprop_at_h p1 sp csl2 f
  | Impl(p1, p2) -> let csl1 = "L"^csl in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = "R"^csl in subprop_at_h p1 sp csl2 f
  | Iff(p1, p2) -> let csl1 = "L"^csl in let f = subprop_at_h p1 sp csl1 sls in 
    let csl2 = "R"^csl in subprop_at_h p1 sp csl2 f;;

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
  | Not(p1) -> not(truth p r)
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

let rec cnf (p: prop): prop = let pm = cnf_i(nnf(p)) in
  match pm with 
  | Or(p1, p2) -> raise CantConvert
  | _ -> pm;;

let rec dnf (p: prop): prop = let pm = dnf_i(nnf(p)) in
  match pm with 
  | And(p1, p2) -> raise CantConvert
  | _ -> pm;;