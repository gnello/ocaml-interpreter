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

(* verifica se un elemento è presente in una lista *)
let rec contains i = 
  function a::tl -> if i = a 
    then Bool(true)
    else (contains i tl) 
         | [] -> Bool(false);;

(* verifica se una chiave è presente in una lista di coppie chiave valore *)
let rec containsKey i = 
  function (a, b)::tl -> if i = a 
    then Bool(true)
    else (containsKey i tl) 
         | [] -> Bool(false);;

(* controlla l'esistenza di una chiave nel dizionario *)
let rec has_key (i : ide) lst : evT = 
  if (typecheck "dict" lst)
  then (match lst with 
        Dict([]) -> Bool(false) |
        Dict((x, v)::tl)-> 
          if (x = i)
       (* se ho trovato la chiave restituisco true *)
          then Bool(true) 
      (* altrimenti procedo alla chiave successiva *)
          else has_key i (Dict(tl)))
  else failwith("Type error");; 

(* inserisci una coppia in un dizionario *)
let insert (i : ide) (e1 : evT) (e2 : evT) : evT =
  if (typecheck "int" e1) && (typecheck "dict" e2)
  then 
    (* controlla che la chiave non esista *)
    if (has_key i e2 = Bool(false)) then
      (match e2 with
         (* se il parametro è corretto aggiungi in fondo alla lista *)
         Dict(list) -> Dict(list@[(i, e1)]))
    else failwith("key already exists")
  else failwith("Type error");;

(* rimuovi una coppia da un dizionario *)
let delete (i : ide) (e1 : evT) : evT = 
  if (typecheck "dict" e1) then 
    let rec f (i : ide) (e1 : evT) : (ide * evT) list = 
      (match e1 with 
         Dict([]) -> [] |
         Dict((x, v)::tl) -> 
          (* se ho trovato la coppia restituisco il resto della lista *)
           if (i = x) then tl
        (* altrimenti lascio intatta la lista e procedo
     alla coppia successiva *)
           else (x, v)::(f i (Dict(tl))))
    in Dict(f i e1)
  else failwith("Type error");;

(* filtra il dizionario *)
let filter (e1 : ide list) (e2 : evT) : evT = 
  if (typecheck "dict" e2) then
    let rec f (e1 : ide list) (e2 : evT) : (ide * evT) list = 
      (match e2 with 
         Dict([]) -> [] |
         Dict((x, v)::tl) -> if (contains x e1 = Bool(true))
           then (x, v)::(f e1 (Dict(tl)))
           else (f e1 (Dict(tl))))
    in Dict(f e1 e2)
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
                    | DictItem(i, e1, e2) -> let tl = (evaldict e2 r) in 
                        (* controlla che non ci siano chiavi duplicate *)
                        if ((containsKey i tl) = Bool(false))
                        then let value = (eval e1 r) in
                          if (typecheck "int" value) 
                          then (i, value)::tl
                          else failwith("Type error")
                        else failwith("Duplicate keys"))
      in Dict(evaldict e1 r) | 
    (* inserisci una coppia nel dizionario*)
    (* prima valuta il valore da inserire *)
    Insert(i, e1, e2) -> let value = eval e1 r in 
      (* valuta il dizionario *)
      let dict = (eval e2 r) in 
      (* chiama la funzione di rts *)
      insert i value dict | 
    (* rimuovi una coppia dal dizionario*) 
    (* valuta il dizionario *)
    Delete(i, e1) -> let dict = (eval e1 r) in
      (* chiama la funzione di rts *)
      delete i dict |
    (* cerca una chiave dal dizionario*) 
    (* valuta il dizionario *)
    Haskey(i, e1) -> let dict = (eval e1 r) in 
      (* chiama la funzione di rts *)
      (has_key i dict) | 
    (* applica la funzione a tutte le coppie del dizionario *) 
    (* valuta il dizionario e la funzione *)
    Iterate(f, e1) -> let dict = (eval e1 r) in
      let fClosure = (eval f r) in
      (* effettua il controllo sul tipo *)
      if (typecheck "fun" fClosure && typecheck "dict" dict) 
          (* applica la funzione a tutti gli elementi del dizionario *)
      then let rec iterate (list : dicttype) : (ide * evT) list = 
             (match list with 
                Empty -> [] |
                DictItem(i, e1, e2) -> (i, eval (FunCall(f, e1)) r)::(iterate e2))
        in (match e1 with
              Edict(x)-> Dict(iterate x)) 
      else failwith("Type error") |
    (* calcola il valore ottenuto applicando sequenzialmente 
      la funzione a tutte le coppie del dizionario *) 
    (* valuta il dizionario e la funzione *)
    Fold(f, e1) -> let dict = (eval e1 r) in
      let fClosure = (eval f r) in
      (* effettua il controllo sul tipo *)
      if (typecheck "fun" fClosure && typecheck "dict" dict) 
          (* applica la funzione a tutti gli elementi del dizionario *)
      then let rec fold (list : dicttype) : evT = 
             (match list with 
                Empty -> Int 0 |
                DictItem(_, e1, e2) -> sum (eval (FunCall(f, e1)) r) (fold e2))
        in (match e1 with
              Edict(x)-> fold x) 
      else failwith("Type error") | 
       (* filtra il dizionario *) 
    (* valuta il dizionario *)
    Filter(xlist, e1) -> let dict = (eval e1 r) in 
      (* chiama la funzione di rts *) 
      (filter xlist dict)
     
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
let e16 = Haskey("bananajoe", e4);;
eval e16 env0;;

(* applica la funzione a tutte le coppie del dizionario *)
let e8 = Iterate(Fun("val", Sum(Den "val", Eint 1)), e4);;
eval e8 env0;;

(* calcola il valore ottenuto applicando sequenzialmente 
      la funzione a tutte le coppie del dizionario *) 
let e9 = Fold(Fun("val", Sum(Den "val", Eint 1)), e4);;
eval e9 env0;;

(* filtra il dizionario *) 
let e10 = Filter(["mele"; "pere"], e4);;
eval e10 env0;; 

(* test avanzati *)

(* testa che non si possa instanziare un dizionario con chiavi duplicate *)
let e11 = Edict(DictItem("mele", Eint 430, DictItem("mele", Eint 312, DictItem("arance", Eint 525, DictItem("pere", Eint 217, Empty)))));; 
eval e11 env0;; 

(* testa che non si possano inserire chiavi duplicate *) 
let e12 = Insert("kiwi", Eint 300, e4);;
let e13 = Insert("kiwi", Eint 300, e12);;
eval e13 env0;;

(* testa che non si possa instanziare un dizionario 
con valori diversi da int (type checking dinamico) *) 
let e14 = Edict(DictItem("mele", Eint 430, DictItem("banane", Ebool true, DictItem("arance", Eint 525, DictItem("pere", Eint 217, Empty)))));; 
eval e14 env0;; 

(* testa che non si possano inserire valori 
diversi da int (type checking dinamico) *) 
let e15 = Insert("kiwi", Ebool true, e4);;
eval e15 env0;;

(* testa che non si possa usare iterate con 
   un parametro diverso da una funzione
   (type checking dinamico) *)
let e17 = Iterate(Eint 100, e4);;
eval e17 env0;;

(* testa che non si possa usare fold con 
   un parametro diverso da una funzione
   (type checking dinamico) *)
let e18 = Fold(Eint 100, e4);;
eval e18 env0;;