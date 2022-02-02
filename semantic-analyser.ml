(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception Problem_in_read_check;;
exception Problem_in_write_check;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major-1, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmConst(x) -> ScmConst'(x)
      | ScmVar(x) -> ScmVar'(tag_lexical_address_for_var x params env)
      | ScmIf(test,dit,dif) -> ScmIf'(run test params env,
                                      run dit params env,
                                      run dif params env)
      | ScmSeq(exprs) -> ScmSeq'(List.map (fun expr -> run expr params env) exprs)
      | ScmSet(ScmVar(varname),value) -> ScmSet'(tag_lexical_address_for_var varname params env,
                                         run value params env)
      | ScmDef(ScmVar(varname),value) -> ScmDef'(tag_lexical_address_for_var varname params env,
                                        run value params env)
      | ScmOr(exprs) -> ScmOr'(List.map (fun expr -> run expr params env) exprs)
      | ScmLambdaSimple(paramlist,body) -> ScmLambdaSimple'(paramlist,run body paramlist ([paramlist]@env))
      | ScmLambdaOpt(paramlist,opt,body) -> ScmLambdaOpt'(paramlist,opt,run body (paramlist@[opt]) ([paramlist@[opt]]@env))
      | ScmApplic(proc,args) -> ScmApplic'(run proc params env,List.map (fun arg -> run arg params env) args)
      | _-> raise X_not_implemented

   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
    match pe,in_tail with
    | ScmVar'(pe),_ -> ScmVar'(pe)
    | ScmConst'(pe),_ -> ScmConst'(pe)

    | ScmOr'(exprs),_ ->
      (match exprs with
       | [] -> ScmOr'[]
       | exprs ->
         let lst = List.rev exprs in
         let exprs_reversed = (run (List.hd lst) in_tail)::List.map (fun expr -> run expr false) (List.tl lst) in
         ScmOr'(List.rev exprs_reversed))

    | ScmSeq'(exprs),_ ->
      (match exprs with
       | [] -> ScmSeq'[]
       | exprs ->
         let lst = List.rev exprs in
         let exprs_reversed = (run (List.hd lst) in_tail)::List.map (fun expr -> run expr false) (List.tl lst) in
         ScmSeq'(List.rev exprs_reversed))

    | ScmIf'(test,dit,dif),_ -> ScmIf'(run test false,run dit in_tail,run dif in_tail)
    | ScmDef'(var',expr),_ -> ScmDef'(var',run expr false)
    | ScmSet'(var',expr),_ -> ScmSet'(var',run expr false)

    | ScmLambdaSimple'(arglist,body),_ -> ScmLambdaSimple'(arglist, run body true)
    | ScmLambdaOpt'(arglist,opt,body),_ -> ScmLambdaOpt'(arglist, opt,run body true)

    | ScmApplic'(proc,args),true -> ScmApplicTP'(run proc false,List.map (fun e -> run e false) args)
    | ScmApplic'(proc,args),false -> ScmApplic'(run proc false,List.map (fun e -> run e false) args)

    | _ -> raise X_not_implemented
   in 
   run pe false;;

  (*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ boxing ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let check_param_bound varname1 varname2 var = 
  if varname1 = varname2 then ScmBoxGet'(var)
  else ScmVar'(var);;

let check_eq_vars varname1 varname2 =
  if varname1 = varname2 then true
  else false;;

let rec make_boxing_param param body = (match body with
  | ScmConst'(expr) -> ScmConst'(expr)
  | ScmVar'(var) -> (match var with
                    | VarParam(name, _) -> check_param_bound name param var
                    | VarBound(name, _, _) -> check_param_bound name param var
                    | _ -> ScmVar'(var))
  | ScmBox'(var) -> ScmBox'(var)
  | ScmBoxGet'(var) -> ScmBoxGet'(var)
  | ScmBoxSet'(var, expr) -> ScmBoxSet'(var, make_boxing_param param expr)
  | ScmIf'(test, dit, dif) -> ScmIf'(make_boxing_param param test, make_boxing_param param dit, make_boxing_param param dif)
  | ScmSeq'(exprs) -> ScmSeq'(List.map (make_boxing_param param) exprs)
  | ScmSet'(varname, value) -> (match varname with
                              | VarParam(name, _) -> if check_eq_vars name param then ScmBoxSet'(varname, make_boxing_param param value)
                                                    else ScmSet'(varname, make_boxing_param param value)
                              | VarBound(name, _, _) -> if check_eq_vars name param then ScmBoxSet'(varname, make_boxing_param param value)
                                                        else ScmSet'(varname, make_boxing_param param value)
                              | _ -> ScmSet'(varname, make_boxing_param param value))
  | ScmDef'(varname, value) -> ScmDef'(varname, make_boxing_param param value)
  | ScmOr'(exprs) -> ScmOr'(List.map (make_boxing_param param) exprs)
  | ScmLambdaSimple'(vars, body) -> if List.exists (fun (str) -> str = param) vars
                                    then ScmLambdaSimple'(vars, body)
                                    else ScmLambdaSimple'(vars, make_boxing_param param body)
  | ScmLambdaOpt'(vars, opt, body) -> if List.exists (fun (str) -> str = param) (vars@[opt])
                                      then ScmLambdaOpt'(vars, opt, body)
                                      else ScmLambdaOpt'(vars, opt, make_boxing_param param body)
  | ScmApplic'(proc, args) -> ScmApplic'(make_boxing_param param proc, (List.map (make_boxing_param param) args))
  | ScmApplicTP'(proc, args) -> ScmApplicTP'(make_boxing_param param proc, (List.map (make_boxing_param param) args)));
  ;;

(**check if param has been written in lambda's body *)  
let rec check_write param body = match body with 
  | ScmConst'(var) -> []
  | ScmIf'(test, dit, dif) -> check_write param test @ check_write param dit @ check_write param dif  
  | ScmSeq'(exprs) -> (List.fold_right(fun acc lst -> lst @ check_write param acc) exprs []) 
  | ScmSet'(VarParam(varname, _), value) -> if varname=param then [true]
                                            else []
  | ScmSet'(VarBound(varname, _, _), value) -> if varname=param then [true]
                                              else []
  | ScmDef'(varname, value) -> check_write param value
  | ScmOr'(exprs) -> (List.fold_right(fun acc lst -> lst @ check_write param acc) exprs [])
  | ScmLambdaSimple'(vars, body) -> if List.exists (fun (name) -> name = param) vars then []
                                    else check_write param body 
  | ScmLambdaOpt'(vars, opt, body) -> if List.exists (fun (name) -> name = param) (vars@[opt]) then []
                                      else check_write param body
  | ScmApplic'(proc, args) -> check_write param proc @ (List.fold_right(fun acc lst -> lst @ check_write param acc) args [])
  | ScmApplicTP'(proc, args) -> check_write param proc @ (List.fold_right(fun acc lst -> lst @ check_write param acc) args []) 
  | _ -> [false];; 

 
(**check if param is been read in lambda's body *)  
let rec check_read param body = match body with
  | ScmConst'(var) -> []
  | ScmVar'(var) -> (match var with
                    | VarParam(varname, _) -> if varname=param then [true]
                                              else []
                    | VarBound(varname, _, _) -> if varname=param then [true]
                                                else []
                    | _ -> [])
  | ScmIf'(test, dit, dif) -> check_read param test @ check_read param dit @ check_read param dif  
  | ScmSeq'(exprs) -> (List.fold_right(fun acc lst -> lst @ check_read param acc) exprs []) 
  | ScmSet'(varname, value) -> check_read param value (**checking read, varname is the var that we write to so no need to check *)
  | ScmDef'(varname, value) -> check_read param value
  | ScmOr'(exprs) -> (List.fold_right(fun acc lst -> lst @ check_read param acc) exprs [])
  | ScmLambdaSimple'(vars, body) -> if List.exists (fun (name) -> name = param) vars then []
                                    else check_read param body 
  | ScmLambdaOpt'(vars, opt, body) -> if List.exists (fun (name) -> name = param) (vars@[opt]) then []
                                      else check_read param body
  | ScmApplic'(proc, args) -> check_read param proc @ (List.fold_right(fun acc lst -> lst @ check_read param acc) args [])
  | ScmApplicTP'(proc, args) -> check_read param proc @ (List.fold_right(fun acc lst -> lst @ check_read param acc) args []) 
  | _ -> [false];;                                                                                     

let count_read_write lst = (List.fold_right (fun acc sum -> if acc = true then 1 + sum else 0 + sum) lst 0)
  
let rec check_if_box_param param body = 
  let read_lst = [] @ (check_read param body) in (**if param was read at least once in body read_lst = [true;...] *)
  let write_lst = [] @ check_write param body in (**if param was written at least once in body read_lst = [true;...] *)
  let read_count = count_read_write read_lst in
  let write_count = count_read_write write_lst in
    if (read_count >= 1 && write_count >= 1) then true 
    else false;; 

let rec box_set_rec expr = match expr with
  | ScmConst'(expr) -> ScmConst'(expr)
  | ScmVar'(expr) -> ScmVar'(expr)
  | ScmBox'(expr) -> ScmBox'(expr)
  | ScmBoxGet'(expr) -> ScmBoxGet'(expr)
  | ScmBoxSet'(var,exp) -> ScmBoxSet'(var, (box_set_rec exp))
  | ScmIf'(test,dit,dif) -> ScmIf'((box_set_rec test),(box_set_rec dit),(box_set_rec dif))
  | ScmSeq'(exprs) -> ScmSeq'(List.map box_set_rec exprs)
  | ScmDef'(var,exp) -> ScmDef'(var, (box_set_rec exp)) 
  | ScmSet'(var,exp) -> ScmSet'(var, (box_set_rec exp)) 
  | ScmOr'(exprs) -> ScmOr'(List.map box_set_rec exprs)
  | ScmLambdaSimple'(vars,body) -> ScmLambdaSimple'(vars, (box_set_rec(boxing_lambda (List.rev vars) body ((List.length vars)-1))))
  | ScmLambdaOpt'(vars,opt,body) -> ScmLambdaOpt'(vars, opt, (box_set_rec(boxing_lambda (List.rev(vars@[opt])) body ((List.length vars)))))
  | ScmApplic'(proc,args) -> ScmApplic'((box_set_rec proc), (List.map box_set_rec args))
  | ScmApplicTP'(proc,args) -> ScmApplicTP'((box_set_rec proc), (List.map box_set_rec args));
  
and boxing_lambda args body index = match args with
  | hd :: tl -> (if (check_if_box_param hd body) then (
    let boxed_body1 = (make_boxing_param hd body) in
    let boxed_body = (match boxed_body1 with
      | ScmSeq'(ScmSet'((VarParam(varname1, minor1)), ScmBox'(VarParam(varname2, minor2))) :: exprs) when (varname1 = varname2) ->
          (ScmSeq'([ScmSet'(VarParam(hd, index), ScmBox'(VarParam(hd, index)));
                          ScmSet'(VarParam(varname1, minor1), ScmBox'(VarParam(varname2, minor2)))]@exprs)) 
      | ScmSeq'(exprs) -> (ScmSeq'([ScmSet'(VarParam(hd, index), ScmBox'(VarParam(hd, index)))]@exprs))
      | _ -> ScmSeq'([ScmSet'(VarParam(hd, index), ScmBox'(VarParam(hd, index)))]@[boxed_body1])) in 
    (boxing_lambda tl boxed_body  (index-1)))
    else (boxing_lambda tl body (index-1)))
  | [] -> body
  ;;
     
  let rec box_set expr = box_set_rec expr;;

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))


end;; (* end of module Semantic_Analysis *)


  