#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val macro_expand : sexpr -> sexpr
  val macro_expansion_letrec : sexpr -> sexpr
end;; 

module Tag_Parser : TAG_PARSER = struct

let rec improper_scm_list_to_list = function
    | ScmPair(a,b) -> a::(improper_scm_list_to_list b)
    | s -> [s];;

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;


let rec lambda_body_to_expr body =
    if (List.length body) > 1 then ScmSeq(body)
    else if (List.length body) = 1 then (List.hd body)
    else raise X_proper_list_error;;

let rec check_if_duplicate_in_list = function
    | [] -> false
    | hd::tl -> List.exists ((=) hd) tl || check_if_duplicate_in_list tl;;

let unique_error_raise lst = match (check_if_duplicate_in_list lst) with
    | true -> raise X_proper_list_error
    | false -> lst;;

let improper_arglist_to_lambdaOpt args body=
    let check_non_symbols = (function | ScmSymbol(sym) -> sym | _ -> raise(X_syntax_error(args,"bad arguments"))) in
    let lst = List.map check_non_symbols (improper_scm_list_to_list args) in
    let lst = unique_error_raise lst in
    let lst_last = List.hd (List.rev lst) in
    let lst_without_last = List.rev (List.tl (List.rev lst)) in
    ScmLambdaOpt (lst_without_last, lst_last, body);;

let rec list_to_scm_list lst= 
  match lst with
  | [] -> ScmNil
  | hd::tl-> ScmPair(hd,list_to_scm_list tl)

let make_quoted_symbol sym = ScmPair(ScmSymbol "quote", ScmPair(sym, ScmNil))
let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr 
in
match sexpr with 
(* Implement tag parsing here *)
| ScmNil -> ScmConst(ScmNil)
| ScmBoolean(x) -> ScmConst(ScmBoolean(x))
| ScmChar(x) -> ScmConst(ScmChar(x))
| ScmNumber(x) -> ScmConst(ScmNumber(x))
| ScmString(x) -> ScmConst(ScmString(x))
| ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol(x), ScmNil)) -> ScmConst(ScmSymbol(x))
| ScmPair(ScmSymbol "quote", ScmPair(x, ScmNil)) -> ScmConst(x)
| ScmSymbol(x) ->
      if List.mem x reserved_word_list then raise (X_syntax_error (ScmSymbol(x), "is a reserved word"))
      else ScmVar(x)
(*If handling ------------------------------------------------ *)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) ->
      ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil))) ->
      ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst(ScmVoid))

(*Or handling ------------------------------------------------ *)
| ScmPair (ScmSymbol "or", ScmNil) -> ScmConst(ScmBoolean(false))
| ScmPair (ScmSymbol "or", ScmPair (arg, ScmNil)) -> tag_parse_expression(arg)
| ScmPair(ScmSymbol ("or"), args) ->
      ScmOr(List.map tag_parse_expression (scm_list_to_list args))

(*Lambda handling ------------------------------------------------ *)
| ScmPair(ScmSymbol("lambda"), ScmPair(args,body)) ->
    (match args with
    (* No arguments *)
    | ScmNil -> ScmLambdaSimple([],ScmSeq(List.map tag_parse_expression (scm_list_to_list body)))
    (* With arguments  , and lambdaopt tag parsing *)
    | ScmPair(_,_) -> if scm_is_list args then ScmLambdaSimple
                (unique_error_raise (List.map (function | ScmSymbol(sym) -> sym | _ -> raise(X_syntax_error(args,"lambda argument is not a symbol"))) (scm_list_to_list args)),
                lambda_body_to_expr (List.map tag_parse_expression (scm_list_to_list body)))
                else improper_arglist_to_lambdaOpt args (lambda_body_to_expr (List.map tag_parse_expression (scm_list_to_list body)))
    (* Variadic lambda *)
    | ScmSymbol(arg) -> ScmLambdaOpt([],arg,lambda_body_to_expr (List.map tag_parse_expression (scm_list_to_list body)))
    | _ -> raise (X_not_implemented))

(*Define handling ------------------------------------------------ *)
| ScmPair(ScmSymbol ("define"), ScmPair(varname, ScmPair(value,ScmNil))) ->
    (
      match varname with
      | ScmSymbol(var) -> ScmDef(tag_parse_expression (varname),tag_parse_expression value)
      | _ -> raise(X_syntax_error(varname,"Expected variable on LHS of define"))
    )

(*Assignment handling ------------------------------------------------ *)
| ScmPair(ScmSymbol ("set!"), ScmPair(varname, ScmPair(value,ScmNil))) ->
      (
      match varname with
      | ScmSymbol(var) -> ScmSet(tag_parse_expression (varname),tag_parse_expression value)
      | _ -> raise(X_syntax_error(varname,"Expected variable on LHS of set!"))
    )

(*Sequence handling -------------------------------------------------- *)

(*Case were nothing is provided (results in void)*)
| ScmPair(ScmSymbol ("begin"), ScmNil) ->
      ScmConst(ScmVoid)

(*Case were one expression is provided *)
| ScmPair(ScmSymbol ("begin"), ScmPair(sexpr, ScmNil)) ->
      tag_parse_expression sexpr

(*Case were multiple expressions are provided *)
| ScmPair(ScmSymbol ("begin"), ScmPair(a,b)) ->
      ScmSeq(List.map tag_parse_expression (scm_list_to_list (ScmPair(a,b))))

(*Application handling ----------------------------------------------- *)
| ScmPair(proc,args) -> 
    ScmApplic(tag_parse_expression proc,List.map tag_parse_expression (scm_list_to_list args))

| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))


(* Handle let macro expansion *)
and macro_expansion_let args body =
(* Extract a scheme list of the values binded to each variable in the let expression *)
let rec values_to_scm_list arguments =
      match arguments with
      | ScmNil -> ScmNil
      | ScmPair(ScmPair(ScmSymbol(_), ScmPair(value,ScmNil)), ScmNil) -> ScmPair(value, ScmNil)
      | ScmPair(ScmPair(ScmSymbol(_), ScmPair(value,ScmNil)), tail) -> ScmPair(value,values_to_scm_list tail)
      | _-> raise(X_syntax_error(arguments,"invalid let arguments")) in
(* Extract a scheme list of the variable symbols in the let expression *)
let rec vars_to_scm_list arguments =
    match arguments with
    | ScmNil -> ScmNil
    | ScmPair(ScmPair(ScmSymbol(var), ScmPair(_,ScmNil)), ScmNil) -> ScmPair(ScmSymbol(var), ScmNil)
    | ScmPair(ScmPair(ScmSymbol(var), ScmPair(_,ScmNil)), tail) -> ScmPair(ScmSymbol(var),vars_to_scm_list tail)
    | _-> raise(X_syntax_error(arguments,"invalid let arguments")) in
(* Generate a Lambda Sexpression and values to apply *)
let vars_sexpr = vars_to_scm_list args in
let lambda_sexpr = ScmPair(ScmSymbol("lambda"),ScmPair(vars_sexpr, body)) in
let values_sexpr = values_to_scm_list args in
(* Generate an application Sexpression*)
    ScmPair(lambda_sexpr, values_sexpr)

(*Handle letstar macro expansion*)
and macro_expansion_letstar args body =
 let convert_to_let args body =
      match args with
      | ScmNil -> ScmPair
   (ScmSymbol "let",
    ScmPair
     (ScmNil,
      ScmPair
       (body,
        ScmNil)))
      | ScmPair(ScmPair(ScmSymbol(var), ScmPair(value,ScmNil)), ScmNil) -> 
                ScmPair
   (ScmSymbol "let",
    ScmPair
     (ScmPair
       (ScmPair
         (ScmSymbol var, ScmPair (value, ScmNil)),
        ScmNil),body))
      | ScmPair(ScmPair(ScmSymbol(var), ScmPair(value,ScmNil)), tail) ->
            ScmPair
 (ScmSymbol "let",
  ScmPair
   (ScmPair
     (ScmPair (ScmSymbol var, ScmPair (value, ScmNil)),
      ScmNil),
    ScmPair (macro_expand(ScmPair(ScmSymbol("let*"),ScmPair(tail,body))), ScmNil)))
      | _-> raise(X_syntax_error(args,"invalid let syntax")) in
 let converted_to_let =  convert_to_let args body in
    macro_expand converted_to_let

(* Handle and macro expansion *)
and macro_expansion_and args  = 
  match args with
    | ScmNil -> (ScmBoolean true)
    | ScmPair(expr,ScmNil) -> expr
    | ScmPair(expr,tail) -> 
        ScmPair
   (ScmSymbol "if",
    ScmPair
     (expr,
      ScmPair
       (macro_expand(ScmPair(ScmSymbol("and"),tail)),
        ScmPair (ScmBoolean false, ScmNil))))
    | _ -> raise( X_syntax_error(args,"not a valid and statement"))

and macro_expand_cond_ribs ribs =
  match ribs with
  | ScmPair (ScmPair (ScmSymbol "else", exprs), _ribs) -> ScmPair (ScmSymbol "begin", exprs)
  | ScmPair
   (ScmPair
     (expr,
      ScmPair (ScmSymbol "=>", ScmPair (proc, ScmNil))),
    remaining) ->
    let remaining = macro_expand_cond_ribs remaining in
    let converted_let_sexpr =
    ScmPair
   (ScmSymbol "let",
    ScmPair
     (ScmPair
       (ScmPair (ScmSymbol "value", ScmPair (expr, ScmNil)),
        ScmPair
         (ScmPair
           (ScmSymbol "f",
            ScmPair
             (ScmPair
               (ScmSymbol "lambda",
                ScmPair (ScmNil, ScmPair (proc, ScmNil))),
              ScmNil)),
          ScmPair
           (ScmPair
             (ScmSymbol "rest",
              ScmPair
               (ScmPair
                 (ScmSymbol "lambda",
                  ScmPair (ScmNil, ScmPair (remaining, ScmNil))),
                ScmNil)),
            ScmNil))),
      ScmPair
       (ScmPair
         (ScmSymbol "if",
          ScmPair
           (ScmSymbol "value",
            ScmPair
             (ScmPair
               (ScmPair (ScmSymbol "f", ScmNil),
                ScmPair (ScmSymbol "value", ScmNil)),
              ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
        ScmNil))) in
        let call_let_expand sexpr =
        match sexpr with
        | ScmPair(ScmSymbol("let"),ScmPair(args,body)) -> macro_expansion_let args body
        | _ -> raise(X_syntax_error(sexpr,"invalid cond expression")) in
        call_let_expand converted_let_sexpr
      | ScmPair (ScmPair (test, exprs), remaining) -> 
        let remaining = macro_expand_cond_ribs remaining in
          ScmPair
            (ScmSymbol "if",
              ScmPair
              (test,
                ScmPair
                (ScmPair (ScmSymbol "begin", exprs),
                 ScmPair (remaining, ScmNil))))
      |  _ -> raise(X_syntax_error(ribs,"invalid ribs"))

and macro_expansion_letrec sexpr = 
    match sexpr with
    | ScmPair(ScmSymbol("letrec"),ScmPair(args,body)) ->
      let rec make_sets_as_exp_list args =
        match args with
        | ScmNil-> []
        | ScmPair(ScmPair(ScmSymbol(var), ScmPair(value,ScmNil)), ScmNil)-> [ScmPair(ScmSymbol "set!",ScmPair (ScmSymbol var, ScmPair (value, ScmNil)))]
        | ScmPair(ScmPair(ScmSymbol(var), ScmPair(value,ScmNil)), tail) -> [ScmPair(ScmSymbol "set!",ScmPair (ScmSymbol var, ScmPair (value, ScmNil)))]@(make_sets_as_exp_list tail)
        | _ -> raise( X_syntax_error(args,"invalid letrec args")) in
      let rec make_whatever args =
        match args with
        | ScmNil-> ScmNil
        | ScmPair(ScmPair(ScmSymbol(var), ScmPair(value,ScmNil)), ScmNil) -> ScmPair(ScmPair(ScmSymbol(var), ScmPair(make_quoted_symbol(ScmSymbol("whatever")),ScmNil)), ScmNil)
        | ScmPair(ScmPair(ScmSymbol(var), ScmPair(value,ScmNil)), tail) ->ScmPair(ScmPair(ScmSymbol(var), ScmPair(make_quoted_symbol(ScmSymbol("whatever")),ScmNil)),make_whatever tail)
        | _ -> raise(X_syntax_error(args,"invalid letrec args")) in
      let declarations = make_whatever args in
      let setexprs = list_to_scm_list (make_sets_as_exp_list args) in
      let rec concat_setbangs_to_let = function
        | ScmNil -> ScmPair(ScmSymbol("let"),ScmPair(ScmNil,body))
        | ScmPair(x,ScmNil) -> ScmPair(x,ScmPair(ScmPair(ScmSymbol("let"),ScmPair(ScmNil,body)),ScmNil))
        | ScmPair(x,y)-> ScmPair(x,concat_setbangs_to_let y)
        | _ -> ScmNil in
      let expanded_to_let =
        ScmPair
          (ScmSymbol "let",
           ScmPair
            (declarations,
             concat_setbangs_to_let setexprs)) in
      let call_let_expand sexpr =
        match sexpr with
        | ScmPair(ScmSymbol("let"),ScmPair(args,body)) -> macro_expansion_let args body
        | _ -> raise(X_syntax_error(sexpr,"invalid letrec expression")) in
        call_let_expand expanded_to_let
          
    | _ -> raise(X_syntax_error(sexpr,"invalid letrec expression"))


and macro_expand_quasiquote quasiquote_list =
  let rec generate_quasiquote qq_list=
  match qq_list with
  | ScmNil -> ScmPair(ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil)),ScmNil)
  | ScmPair(ScmPair (ScmSymbol "unquote", ScmPair (value, ScmNil)),tail) -> 
    ScmPair(
      ScmPair
      (ScmSymbol "cons",
       ScmPair
        (value, generate_quasiquote tail)),ScmNil)
  | ScmPair(ScmPair (ScmSymbol "unquote-splicing", ScmPair (value, ScmNil)),tail) ->
     ScmPair(
      ScmPair
      (ScmSymbol "append",
       ScmPair
        (value, generate_quasiquote tail)),ScmNil)
  | ScmPair(ScmSymbol sym,tail) -> 
      ScmPair(
      ScmPair
      (ScmSymbol "cons",
       ScmPair
        (ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol sym, ScmNil)), generate_quasiquote tail)),ScmNil)
  | ScmPair(x,tail) -> 
      ScmPair(
      ScmPair
      (ScmSymbol "cons",
       ScmPair
        (x, generate_quasiquote tail)),ScmNil)
  | _ -> raise(X_syntax_error(qq_list,"invalid quasiquote syntax")) in
  let extract_qq qq =
  match qq with
  | ScmPair(x,ScmNil) -> x
  | _ -> qq in 
  extract_qq (generate_quasiquote quasiquote_list)
 
and macro_expand_mit_define var args exprs =
  ScmPair
 (ScmSymbol "define",
  ScmPair
   (ScmSymbol var,
    ScmPair
     (ScmPair
       (ScmSymbol "lambda",
        ScmPair
         (args,
          exprs)),
      ScmNil)))
and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
| ScmPair(ScmSymbol("let"),ScmPair(args,body)) -> macro_expansion_let args body
| ScmPair(ScmSymbol("let*"),ScmPair(args,body)) -> macro_expansion_letstar args body
| ScmPair(ScmSymbol("and"), args) -> macro_expansion_and args
| ScmPair(ScmSymbol("cond"),ribs) -> macro_expand_cond_ribs ribs
| ScmPair(ScmSymbol("letrec"),rest) -> macro_expansion_letrec (ScmPair(ScmSymbol("letrec"),rest))
| ScmPair(ScmSymbol "quasiquote",ScmPair(quasiquote_list,ScmNil)) -> macro_expand_quasiquote quasiquote_list
| ScmPair(ScmSymbol "define",ScmPair(ScmPair (ScmSymbol var, args),exprs)) -> macro_expand_mit_define var args exprs
| _ -> sexpr
end;; 

