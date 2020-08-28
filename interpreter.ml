type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
           Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
           Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
           Letrec of ide * exp * exp 
(* MOD: estensione dei tipi *) 
         | Insert of ide * exp * exp
         | Delete of ide * exp
         | Haskey of ide * exp
         | Iterate of exp * exp
         | Fold of exp * exp
         | Filter of (ide list) * exp 
(* un dizionario è una tripla <chiave, valore, DictItem> *)
         | Edict of dicttype
and dicttype = Empty | DictItem of ide * exp * dicttype;; 

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun 
(* MOD: estensione dei tipi esprimibili *)
         | Dict of (ide * evT) list
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
    "int" -> (match v with
        Int(_) -> true |
        _ -> false) |
    "bool" -> (match v with
        Bool(_) -> true |
        _ -> false) |
(* MOD: estensione del typechecker dinamico *) 
    "dict" -> (match v with
        Dict(_) -> true |
        _ -> false) | 
    "fun" -> (match v with
        FunVal(_) -> true |
        RecFunVal(_) -> true |
        _ -> false) |
    _ -> failwith("not a valid type")
;; 

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n+u))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n-u))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u))
  else failwith("Type error");;

let minus x = if (typecheck "int" x) 
  then (match x with
        Int(n) -> Int(-n))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Bool(n=0))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> (Bool(b||e)))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> Bool(b&&e))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
        Bool(true) -> Bool(false) |
        Bool(false) -> Bool(true))
  else failwith("Type error");; 

(* MOD - estensione delle funzioni di rts *)
(* controlla l'esistenza di una chiave nel dizionario *)
let rec has_key (i : ide) (lst : evT) : bool = 
  if (typecheck "dict" lst)
  then (match lst with 
        Dict([]) -> false |
        Dict((x, v)::tl)-> 
          if (x = i)
       (* se ho trovato la chiave restituisco true *)
          then true 
      (* altrimenti procedo alla chiave successiva *)
          else has_key i (Dict(tl)))
  else failwith("Type error");;
 
(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
    Eint n -> Int n |
    Ebool b -> Bool b |
    IsZero a -> iszero (eval a r) |
    Den i -> applyenv r i |
    Eq(a, b) -> eq (eval a r) (eval b r) |
    Prod(a, b) -> prod (eval a r) (eval b r) |
    Sum(a, b) -> sum (eval a r) (eval b r) |
    Diff(a, b) -> diff (eval a r) (eval b r) |
    Minus a -> minus (eval a r) |
    And(a, b) -> et (eval a r) (eval b r) |
    Or(a, b) -> vel (eval a r) (eval b r) |
    Not a -> non (eval a r) |
    Ifthenelse(a, b, c) -> 
      let g = (eval a r) in
      if (typecheck "bool" g) 
      then (if g = Bool(true) then (eval b r) else (eval c r))
      else failwith ("nonboolean guard") |
    Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
    Fun(i, a) -> FunVal(i, a, r) |
    FunCall(f, eArg) -> 
      let fClosure = (eval f r) in
      (match fClosure with
         FunVal(arg, fBody, fDecEnv) -> 
           eval fBody (bind fDecEnv arg (eval eArg r)) |
         RecFunVal(g, (arg, fBody, fDecEnv)) -> 
           let aVal = (eval eArg r) in
           let rEnv = (bind fDecEnv g fClosure) in
           let aEnv = (bind rEnv arg aVal) in
           eval fBody aEnv |
         _ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
      (match funDef with
         Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
           eval letBody r1 |
         _ -> failwith("non functional def")) | 
    (* MOD: estensione dell'interprete *) 
    (* restituisci la valutazione del dizionario *) 
    Edict(e1) -> let rec evaldict (list : dicttype) (r : evT env) : (ide * evT) list =
                   (match list with 
                    | Empty -> [] 
                       (* valuta il valore nell'ambiente statico e
                    continua la valutazione del dizionario rimanente *)
                    | DictItem(i, e1, e2) -> (i, eval e1 r)::(evaldict e2 r)
                    | _ -> failwith("non dictionary value"))
      in Dict(evaldict e1 r) | 
    (* inserisci una coppia nel dizionario*)
    (* prima valuta b *)
    Insert(i, e1, e2) -> let value = eval e1 r in 
      (* valuta il dizionario *)
      let dict = (eval e2 r) in
      (* effettua il controllo sul tipo *)
      if (typecheck "dict" dict) 
      then (match dict with
         (* se il parametro è corretto aggiungi in fondo alla lista *)
            Dict(list) -> Dict(list@[(i, value)]))
      else failwith("insert called on a non-dictionary value") | 
    (* rimuovi una coppia dal dizionario*) 
    (* valuta il dizionario *)
    Delete(i, e1) -> let dict = (eval e1 r) in
      (* effettua il controllo sul tipo *)
      if (typecheck "dict" dict) 
          (* cerca la coppia da eliminare *)
      then let rec delete (x : ide) (list : evT) : (ide * evT) list = 
             (match list with 
                Dict([]) -> [] |
                Dict((x, v)::tl)->
                  (* se ho trovato la coppia restituisco il resto della lista *)
                  if (x = i)
                  then tl
                      (* altrimenti lascio intatta la lista e procedo
              alla coppia successiva *)
                  else (x, v)::(delete i (Dict(tl))))
        in Dict(delete i dict) 
      else failwith("delete called on a non-dictionary value") |
    (* cerca una chiave dal dizionario*) 
    (* valuta il dizionario *)
    Haskey(i, e1) -> let dict = (eval e1 r) in
      (* effettua il controllo sul tipo *)
      if (typecheck "dict" dict) 
(* usa la funzione di rts *)
      then Bool(has_key i dict)
      else failwith("has_key called on a non-dictionary value") | 
    (* applica la funzione a tutte le coppie del dizionario *) 
    (* valuta il dizionario *)
    Iterate(f, e1) -> let dict = (eval e1 r) in
      let func = (eval f r) in
      (* effettua il controllo sul tipo *)
      if (typecheck "fun" func && typecheck "dict" dict) 
          (* cerca la chiave *)
      then let rec iterate (list : evT) : (ide * evT) list = 
             (match list with 
                Dict([]) -> [] |
                Dict((x, v)::tl)-> ("a", Int 1)::(iterate (Dict(tl))))
        in Dict(iterate dict) 
      else failwith("iterate called on a non-function or non-dictionary value")
          
;;  

(* =============================  TESTS  ================= *)

(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

(* MOD: estensione dei test *)

(* crea un dizionario vuoto *)
let e3 = Edict(Empty);; 
eval e3 env0;;

(* crea un dizionario con elementi di default *) 
let e4 = Edict(DictItem("mele", Eint 430, DictItem("banane", Eint 312, DictItem("arance", Eint 525, DictItem("pere", Eint 217, Empty)))));; 
eval e4 env0;; 

(* inserisci un elemento nel dizionario *)
let e5 = Insert("kiwi", Eint 300, e4);;
eval e5 env0;;

(* rimuovi un elemento dal dizionario *)
let e6 = Delete("pere", e4);;
eval e6 env0;;

(* controlla l'esistenza di una chiave nel dizionario *)
let e7 = Haskey("banane", e4);;
eval e7 env0;;

(* applica la funzione a tutte le coppie del dizionario *)
let e8 = Iterate(Fun("val", Sum(Den "val", Eint 1)), e4);;
eval e8 env0;;
