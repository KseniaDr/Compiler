#use "semantic-analyser.ml";;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  (* Start CONST TABLE implementation *)
  let list_to_string lst =
    String.concat "" (List.map (fun str ->  str) lst);;

  let rec find_const_in_table table sexpr =
      List.fold_left
                (fun acc (sexpr_cst, (offset,  _s1)) ->
                    if (acc > (-1))
                     then acc
                     else if (sexpr_eq sexpr sexpr_cst)
                     then offset
                     else acc) (-1) table

  let add_to_table : (sexpr*(int*string)) list -> (sexpr*(int*string)) -> int -> ((sexpr*(int*string)) list * int) =
    fun table (sexpr,(offset,assembly_string)) offsetToAdd ->
      let offset_in_table = find_const_in_table table sexpr in
      if (offset_in_table = (-1)) then (table @ [(sexpr, (offset,assembly_string))], offset+offsetToAdd) 
      else (table, offset)
  ;;
  (* Generates a constant expression (sexpr,(int,string)) and then calls add_to_table to put it in the const table *)
  let rec constant_of_sexpr sexpr table offset =
    match sexpr with
      | ScmNil | ScmBoolean _ -> (table, offset)
      | ScmNumber (ScmRational (num,nom)) -> let constant = (sexpr,(offset,"MAKE_LITERAL_RATIONAL(" ^ (string_of_int num) ^","^(string_of_int nom)^")")) in (add_to_table table constant 17)
      | ScmNumber (ScmReal f) -> let constant = (sexpr,(offset,"MAKE_LITERAL_FLOAT(" ^ (string_of_float f) ^ ")")) in (add_to_table table constant 9)
      | ScmChar c -> let constant = (sexpr,(offset,"MAKE_LITERAL_CHAR(" ^ string_of_int (Char.code c) ^ ")")) in (add_to_table table constant 2)
      | ScmString str -> let constant = (sexpr,(offset, "MAKE_LITERAL_STRING \"" ^ str ^ "\","^(string_of_int(String.length str)) )) in (add_to_table table constant (9+(String.length str)))
      | ScmSymbol sym ->
        let offset_str_of_sym = find_const_in_table table (ScmString sym) in
        let (offset_str_of_sym,(table,offset_after_str_of_sym)) = 
          if (offset_str_of_sym=(-1)) then (offset,(constant_of_sexpr (ScmString sym) table offset)) 
          else (offset_str_of_sym,(table,offset)) in
        let constant = (sexpr,(offset_after_str_of_sym,"MAKE_LITERAL_SYMBOL(const_tbl + " ^ (string_of_int offset_str_of_sym) ^ ")")) in
        add_to_table table constant 9
      | ScmPair (sexpr1, sexpr2) ->
        let (table, offset) = constant_of_sexpr sexpr1 table offset in 
        let (table, offset) = constant_of_sexpr sexpr2 table offset in
        let constPair = 
          (sexpr,
          (offset,
            "MAKE_LITERAL_PAIR(const_tbl + " ^ (string_of_int (find_const_in_table table sexpr1)) ^ ",const_tbl + " ^ (string_of_int (find_const_in_table table sexpr2)) ^ ")"))
        in (add_to_table table constPair 17)
      | ScmVector(sexprs) -> 
         let (table,offset) = List.fold_left (fun (table,offset) sexpr -> constant_of_sexpr sexpr table offset) (table,offset) sexprs in
         let vector_asm_string = "MAKE_LITERAL_VECTOR " ^ (string_of_int (List.length sexprs)) ^ "," ^
            (list_to_string(
              List.map 
              (fun(sexpr) -> "const_tbl+" ^ string_of_int (find_const_in_table table sexpr) ^ ",") 
                sexprs )
                ) in
         let vector_asm_string_fixed = (String.sub vector_asm_string 0 ((String.length vector_asm_string)-1)) in
         let vector_constant = 
         (sexpr,(offset,vector_asm_string_fixed))  in
            add_to_table table vector_constant (9+(List.length sexprs)*8)
      | _ -> raise X_this_should_not_happen
  ;;

  let rec add_sexpr_to_const_tbl ast table offset =
    match ast with
    | ScmConst' c -> constant_of_sexpr c table offset
    | ScmVar' _ | ScmBox' _ | ScmBoxGet' _ -> (table, offset)
    | ScmBoxSet' (var, expr') -> add_sexpr_to_const_tbl expr' table offset
    | ScmIf' (test, dit, dif) -> List.fold_left (fun (table,offset) ast -> add_sexpr_to_const_tbl ast table offset) (table,offset) [test; dit; dif]
    | ScmSeq' exprlist -> List.fold_left (fun (table,offset) ast -> add_sexpr_to_const_tbl ast table offset) (table,offset) exprlist
    | ScmSet' (var, expr) -> add_sexpr_to_const_tbl expr table offset
    | ScmDef' (var, expr) -> add_sexpr_to_const_tbl expr table offset
    | ScmOr' exprlist -> List.fold_left (fun (table,offset) ast -> add_sexpr_to_const_tbl ast table offset) (table,offset) exprlist
    | ScmLambdaSimple' (_params, body) -> add_sexpr_to_const_tbl body table offset
    | ScmLambdaOpt' (_params, _opt, body) -> add_sexpr_to_const_tbl body table offset
    | ScmApplic' (expr, exprlst) | ScmApplicTP' (expr, exprlst) ->
      List.fold_left (fun (table,offset) ast -> add_sexpr_to_const_tbl ast table offset) (table,offset) (exprlst@[expr])
  ;;
  let init_const_table = ([(ScmVoid, (0, "db T_VOID"));
          (ScmNil, (1, "db T_NIL"));
          (ScmBoolean false, (2, "db T_BOOL,0"));
          (ScmBoolean true, (4, "db T_BOOL,1"))],6)

  (* The method to call for const table *)
  let make_consts_tbl asts = 
    fst (List.fold_left (fun (table ,offset) ast -> (add_sexpr_to_const_tbl ast table offset)) init_const_table
        asts)
  (* End CONST TABLE implementation*)



  (* Start FREE VARS implementation *)
  let rec add_to_table fvar_tbl offset ast =
    let add_var'_to_fvar_tbl var = (**if the variable is of type VarFree and does not exists in fvar_tbl, add it*)
      (match var with
       | VarParam _ | VarBound _ -> (fvar_tbl, offset) (**should not add to list *)
       | VarFree name ->
                      if List.exists (fun (str, _) -> str = name) fvar_tbl then (fvar_tbl, offset) (**should not add to list *)
                      else (fvar_tbl @ [(name, offset)], offset + 8)) (**add to list *)
    in
    match ast with
    | ScmConst' _ -> (fvar_tbl, offset)
    | ScmVar' varname ->  add_var'_to_fvar_tbl varname
    | ScmBox' varname -> add_var'_to_fvar_tbl varname
    | ScmBoxGet' varname -> add_var'_to_fvar_tbl varname
    | ScmBoxSet' (varname, value) -> 
                                    let (fvar_tbl, offset) = add_var'_to_fvar_tbl varname in
                                    add_to_table fvar_tbl offset value 
    | ScmIf' (test, dit, dif) -> (List.fold_left (fun (fvar_tbl, offset) cur -> add_to_table fvar_tbl offset cur) (fvar_tbl, offset) [test; dit; dif])
    | ScmSeq' exprs -> (List.fold_left (fun (fvar_tbl, offset) cur -> add_to_table fvar_tbl offset cur) (fvar_tbl, offset) exprs)
    | ScmSet' (varname, value) -> 
                                    let (fvar_tbl, offset) = add_var'_to_fvar_tbl varname in
                                    add_to_table fvar_tbl offset value 
    | ScmDef' (varname, value) -> 
                                    let (fvar_tbl, offset) = add_var'_to_fvar_tbl varname in
                                    add_to_table fvar_tbl offset value 
    | ScmOr' exprs -> (List.fold_left (fun (fvar_tbl, offset) cur -> add_to_table fvar_tbl offset cur) (fvar_tbl, offset) exprs)
    | ScmLambdaSimple' (params, body) -> add_to_table fvar_tbl offset body
    | ScmLambdaOpt' (params, optional, body) -> add_to_table fvar_tbl offset body
    | ScmApplic' (proc, args) -> List.fold_left (fun (fvar_tbl, offset) cur -> add_to_table fvar_tbl offset cur) (fvar_tbl, offset) (args @ [proc])
    | ScmApplicTP' (proc, args) -> List.fold_left (fun (fvar_tbl, offset) cur -> add_to_table fvar_tbl offset cur) (fvar_tbl, offset) (args @ [proc])
    
  
  (*returns a list of (sting_name, index of sring_name) -> ("map",0)*)
  let make_fvars_tbl asts = 
    let proc_list = [
      (* Type queries  *)
      "boolean?", "boolean?"; "flonum?", "flonum?"; "rational?", "rational?";
      "pair?", "pair?"; "null?", "null?"; "char?", "char?"; "string?", "string?";
      "procedure?", "procedure?"; "symbol?", "symbol?";
      (* String procedures *)
      "string-length", "string_length"; "string-ref", "string_ref"; "string-set!", "string_set";
      "make-string", "make_string"; "symbol->string", "symbol_to_string";
      (* Type conversions *)
      "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "exact->inexact", "exact_to_inexact";
      (* Identity test *)
      "eq?", "eq?";
      (* Arithmetic ops *)
      "+", "add"; "*", "mul"; "/", "div"; "=", "eq"; "<", "lt";
      (* Additional rational numebr ops *)
      "numerator", "numerator"; "denominator", "denominator"; "gcd", "gcd";
      (* user defined ops *)
      "car","car"; "cdr","cdr";"cons","cons"; "set-car!","set_car"; "set-cdr!","set_cdr";"apply","apply";
      ] in
    (**first - add the primitive procedures from proc_list to fvar_tbl *)
    let (fvar_tbl, offset) = (List.fold_left (fun (fvar_tbl, offset) (proc, label) -> (fvar_tbl @ [(proc, offset)], offset + 8)) ([], 0) proc_list) in
    (**then - add all of the expr' from asts (expr' list) to fvar_list only if they don't exists *)
    let (fvar_tbl, offset) = (List.fold_left (fun (fvar_tbl, offset) ast -> (add_to_table fvar_tbl offset ast)) (fvar_tbl, offset) asts) in 
    fvar_tbl
  ;;
  (* End FREE VARS implementation*)

  
  
  let asm_label_generate str =
    let counter = ref (-1)
    in
    fun inc_flag ->
      if inc_flag
      then incr counter;
      str ^ string_of_int !counter 
  ;;

  (*label generators *)
  let asm_label_else = asm_label_generate "else"
  and asm_label_exit = asm_label_generate "exit"
  and asm_label_closure_code = asm_label_generate "code"
  and asm_label_continue = asm_label_generate "cont"
  and asm_label_copy_env = asm_label_generate "copy_env_loop"
  and asm_label_copy_params = asm_label_generate "copy_params_loop"
  and asm_label_after_env_copy = asm_label_generate "after_env_copy"
  and asm_label_make_closure = asm_label_generate "make_closure"
  and asm_label_applic_check = asm_label_generate "applic_proc_is_colsure"
  and asm_label_applic_copy_args = asm_label_generate "copy_args_loop"
  and asm_label_define = asm_label_generate "define"
  and asm_label_deal_with_less_args_on_stack = (asm_label_generate "deal_with_less_args_on_stack")
  and asm_label_deal_with_more_args_on_stack = (asm_label_generate "deal_with_more_args_on_stack")
  and asm_label_opt_make_pairs_loop = (asm_label_generate "make_opt_pairs_loop")
  and asm_label_opt_end_pairs_loop = (asm_label_generate "end_opt_pairs_loop")
  and asm_label_opt_shift_args_loop = (asm_label_generate "opt_shift_args_loop")
  and asm_label_opt_end_shift_args_loop = (asm_label_generate "opt_end_shift_args_loop")
  and asm_label_exit_stack_fix_opt  = (asm_label_generate "exit_stack_fix_opt")
  ;;



  let rec generate_asm_from_expr consts fvars e envSize =
    match e with
    | ScmConst' constant ->
        "mov rax, const_tbl + " ^ string_of_int (find_const_in_table consts constant) ^ "\n"

    (* for parameters , get from the stack *)
    | ScmVar' (VarParam (_, minor)) -> "mov rax, qword [rbp + WORD_SIZE * (4 + " ^ string_of_int minor ^ ")]\n"
    | ScmVar' (VarFree varname) -> "mov rax, [fvar_tbl + " ^ string_of_int (List.assoc varname fvars) ^ "]\n"

    (* for bound variables look up in the extended enviroment *)
    | ScmVar' (VarBound (_, major, minor)) ->
      "mov rax, qword [rbp + WORD_SIZE * 2]\n" ^
      "mov rax, qword [rax + WORD_SIZE * " ^ string_of_int major ^ "]\n" ^
      "mov rax, qword [rax + WORD_SIZE * " ^ string_of_int minor ^ "]\n"

    | ScmBox' var ->
      generate_asm_from_expr consts fvars (ScmVar'(var)) envSize ^
      "MALLOC rbx, WORD_SIZE\n" ^
      "mov [rbx], rax\n" ^
      "mov rax, rbx\n"   (*return the box*)
    | ScmBoxGet' var ->
      generate_asm_from_expr consts fvars (ScmVar'(var)) envSize ^
      "mov rax, qword [rax]\n"
    | ScmBoxSet' (var, e) ->
      generate_asm_from_expr consts fvars e envSize ^
      "push rax\n" ^
      generate_asm_from_expr consts fvars (ScmVar'(var)) envSize ^
      "pop qword [rax]\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"


    | ScmSeq' exprs -> List.fold_left (fun acc expr -> acc ^ generate_asm_from_expr consts fvars expr envSize) "" exprs

    (* generate code for set! *)
    (*in scheme ,set and define returns void *)
    | ScmSet' (VarParam(_, minor), expr) ->
      generate_asm_from_expr consts fvars expr envSize ^
      "mov qword [rbp + WORD_SIZE * (4 + " ^ string_of_int minor ^ ")], rax\n" ^ (*put new sob in the param location on stack *)
      "mov rax, SOB_VOID_ADDRESS\n"
    | ScmSet' (VarFree(varname), expr) ->
      generate_asm_from_expr consts fvars expr envSize ^
      "mov qword [fvar_tbl + " ^ string_of_int (List.assoc varname fvars) ^ "], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"
    | ScmSet'(VarBound(_, major, minor), expr) ->
      (generate_asm_from_expr consts fvars expr envSize) ^
      "mov rbx, qword [rbp + WORD_SIZE * 2]\n" ^
      "mov rbx, qword [rbx + WORD_SIZE * " ^ string_of_int major ^ "]\n" ^
      "mov qword [rbx + WORD_SIZE * " ^ string_of_int minor ^ "], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n" 

    | ScmIf'(test ,dit,dif) -> 
      let else_label = asm_label_else true in
      let exit_label = asm_label_exit true in 
      generate_asm_from_expr consts fvars test envSize ^
      "cmp rax , SOB_FALSE_ADDRESS \n" ^ (* evaluate test and check if its false *)
      "je " ^ else_label ^ "\n" ^
      generate_asm_from_expr consts fvars dit envSize ^
      "jmp " ^ exit_label ^ "\n" ^
      else_label ^ ":\n" ^
      generate_asm_from_expr consts fvars dif envSize ^
      exit_label ^ ":\n"

    | ScmOr' exprs -> 
      let exit_label = asm_label_exit true in
      let or_code = List.fold_left 
                      (fun total_code expr -> total_code ^ 
                        generate_asm_from_expr consts fvars expr envSize ^
                        "cmp rax , SOB_FALSE_ADDRESS \n" ^
                        "jne " ^ exit_label ^ "\n") "" exprs in
      or_code ^ exit_label ^ ":\n"
      
    | ScmDef' ((VarFree varname), expr) -> 
        (asm_label_define true) ^ ":\n" ^ 
        generate_asm_from_expr consts fvars expr envSize ^ (*make code for expression *)
        "mov qword [fvar_tbl + " ^ string_of_int (List.assoc varname fvars) ^ "], rax\n" ^ (*put the scheme object in the freevars table *)
        "mov rax, SOB_VOID_ADDRESS\n" (* define returning void *)
    | ScmLambdaSimple' (params, body) ->
      let label_copy_env = asm_label_copy_env true
      and label_copy_params = asm_label_copy_params true
      and label_closure_code = asm_label_closure_code true
      and label_continue = asm_label_continue true
      and label_done_env_copy = asm_label_after_env_copy true
      and label_make_closure = asm_label_make_closure true
      in
      let prepare_closure =
        "MALLOC rax, WORD_SIZE * " ^ string_of_int (envSize + 1) ^ "\n" ^ (* rax = the address to the extended env*) 
        (*copy env*)
        "mov rbx, [rbp + 2 * WORD_SIZE]\n" ^ (*rbx = current env*)
        "mov rcx, " ^ string_of_int envSize ^"\n" ^
        "cmp rcx, 0\n" ^
        "jle " ^ label_done_env_copy ^ "\n" ^
        label_copy_env ^ ":\n" ^ 
        "\tmov rdx, [rbx + WORD_SIZE * rcx - WORD_SIZE]\n" ^
        "\tmov [rax + WORD_SIZE * rcx], rdx\n" ^
        "\tloop " ^ label_copy_env ^ "\n" ^
        label_done_env_copy ^ ":\n" ^
        "mov rbx, rax\n" ^ 
        "mov rcx, [rbp + 3 * WORD_SIZE]  ;rcx<-n from the stack\n" ^
        "lea rcx, [rcx*WORD_SIZE]   ;rcx <- n * WORD_SIZE\n" ^
        "MALLOC rdx, rcx\n" ^ 
        "mov [rbx], rdx\n" ^ 
        "mov rcx, [rbp + 3 * WORD_SIZE]\n" ^  
        "cmp rcx, 0\n" ^
        "jle " ^ label_make_closure ^ "\n" ^
        label_copy_params ^ ":\n" ^  
        "\tmov rax, [rbp + 4 * WORD_SIZE + WORD_SIZE * rcx - WORD_SIZE]\n" ^ 
        "\tmov [rdx + WORD_SIZE * rcx - WORD_SIZE], rax\n" ^ 
        "\tloop " ^ label_copy_params ^ "\n" ^
        label_make_closure ^ ":\n MAKE_CLOSURE(rax, rbx, " ^ label_closure_code ^ ")\n"
      in
      prepare_closure ^
      "jmp " ^ label_continue ^ "\n" ^ (* we run the below code only when applying the closure *)
      label_closure_code ^ ":\n" ^
      "\tpush rbp\n" ^  (* calling convention *)
      "\tmov rbp, rsp\n" ^
      generate_asm_from_expr consts fvars body (envSize + 1) ^ (* the actual closure code *)
      "\tleave\n" ^  (* returning convention *)
      "\tret\n" ^ 
      label_continue ^ ":\n" (*jump to here after making the closure object *)

    | ScmLambdaOpt'(params,opt,body) ->
      let label_copy_env = asm_label_copy_env true
      and label_copy_params = asm_label_copy_params true
      and label_closure_code = asm_label_closure_code true
      and label_continue = asm_label_continue true
      and label_done_env_copy = asm_label_after_env_copy true
      and label_make_closure = asm_label_make_closure true in
        (*assembly code to handle lambdaopt stack manipulation *)
  let asm_opt_fix_stack_string num_params =
      let label_deal_with_less_args_on_stack = asm_label_deal_with_less_args_on_stack true
      and label_deal_with_more_args_on_stack = asm_label_deal_with_more_args_on_stack true
      and label_opt_make_pairs_loop =          asm_label_opt_make_pairs_loop true
      and label_opt_end_pairs_loop =           asm_label_opt_end_pairs_loop true
      and label_opt_shift_args_loop =          asm_label_opt_shift_args_loop true
      and label_opt_end_shift_args_loop =      asm_label_opt_end_shift_args_loop true
      and label_exit_stack_fix_opt  =          asm_label_exit_stack_fix_opt true in
      "
      mov rax,"^num_params^" ;rax has actual closure parameter count \n" ^
      "cmp rax,[rsp+WORD_SIZE*2] ;this is the current args we pushed through apply
      jl " ^ label_deal_with_more_args_on_stack^" \n" ^
      label_deal_with_less_args_on_stack ^ ":\n" ^
        "jmp " ^label_exit_stack_fix_opt^ "\n" ^
      label_deal_with_more_args_on_stack ^ ":\n" ^
        "mov rbx,"^num_params^"\n" ^
        "mov rcx,[rsp+WORD_SIZE*2]
        lea rsi,[rcx+2] ; rsi -> pointer to top of stack
        sub rcx,rbx;rcx-> total loop reps
        mov rdi,rcx ;rdi->save total reps for later
        mov rdx,SOB_NIL_ADDRESS
        mov rbx,[rsp+rsi*WORD_SIZE]
        MAKE_PAIR(rax,rbx,rdx) ;make first pair, then continue if needed
        dec rcx
        cmp rcx,0
        jle " ^label_opt_end_pairs_loop ^"\n" ^
      label_opt_make_pairs_loop ^":\n"^
        "dec rsi
        mov rdx,rax
        mov rbx,[rsp+rsi*WORD_SIZE]
        MAKE_PAIR(rax,rbx,rdx) ;rax will have pointer to the list \n" ^
        "loop "^ label_opt_make_pairs_loop ^"\n" ^
      label_opt_end_pairs_loop ^":\n" ^
 "
        mov rbx,[rsp+WORD_SIZE*2]
        add rbx,2
        lea rbx, [rsp+rbx*WORD_SIZE]
        mov [rbx],rax ;put the list into highest arg
       mov rbx ,[rsp+WORD_SIZE*2]
       dec rbx 
       sub rbx ,"^num_params^" ;rbx=argcnt-1-originalargs
       cmp rbx ,0 \n" ^
       "jle "^ label_opt_end_shift_args_loop ^"\n"^
       "lea rdx,[rsp + rbx*WORD_SIZE] ;points to start location
        mov rbx,3
        lea rbx,[rsp + rbx*WORD_SIZE] ;where to start copying from
        mov rcx,"^num_params^" ;argcnt
       dec rcx
       cmp rcx,0 \n" ^
      "jle " ^label_opt_end_shift_args_loop ^"\n" ^
      label_opt_shift_args_loop ^":\n" ^
        "
        mov rsi ,[rbx]
        mov [rdx],rsi
        add rdx,WORD_SIZE
        add rbx,WORD_SIZE\n" ^
      "
      loop " ^ label_opt_shift_args_loop ^ "\n" ^
      label_opt_end_shift_args_loop ^ ":\n" ^
        "  
        mov rax,[rsp] ;ret addr
        mov rbx,[rsp+WORD_SIZE*1] ;env
        mov rcx,"^string_of_int((int_of_string num_params)+1)^" ;argcnt+1
        mov rdi,[rsp+WORD_SIZE*2]
        add rdi,3
        sub rdi,rcx
        lea rsp ,[rsp+WORD_SIZE*rdi]
        push rcx ;-> argcnt
        push rbx ;-> env
        push rax ;-> ret addr \n" ^
      label_exit_stack_fix_opt ^":\n" 
      in
      let prepare_closure =
        (* allocate new env, so rax <- the address to the extended env*)
        "MALLOC rax, WORD_SIZE * " ^ string_of_int (envSize + 1) ^ "\n" ^ (*rax <- address to ExtEnv*)
        (*copy env*)
        "mov rbx, [rbp + 2 * WORD_SIZE]\n" ^ (*now rbx holds the pointer to the previous env*)
        "mov rcx, " ^ string_of_int envSize ^"\n" ^
        "cmp rcx, 0\n" ^
        "jle " ^ label_done_env_copy ^ "\n" ^
        label_copy_env ^ ":\n" ^ (*rcx will go from n...1*)
        "\tmov rdx, [rbx + WORD_SIZE * rcx - WORD_SIZE]\n" ^
        "\tmov [rax + WORD_SIZE * rcx], rdx\n" ^
        "\tloop " ^ label_copy_env ^ "\n" ^
        (* now we'll peform ExtEnv[0] -> vector with params *)
        label_done_env_copy ^ ":\n" ^
        "mov rbx, rax\n" ^ (* rbx <- ExtEnv*)
        "mov rcx, [rbp + 3 * WORD_SIZE]  ;rcx<-n from the stack\n" ^
        "lea rcx, [rcx*WORD_SIZE]   ;rcx <- n * WORD_SIZE\n" ^
        "MALLOC rdx, rcx\n" ^ (* rdx <- address to new vector*)
        "mov [rbx], rdx\n" ^ (* ExtEnv[0] -> new vector *)
        "mov rcx, [rbp + 3 * WORD_SIZE]\n" ^  (* rcx<-n from the stack*)
        "cmp rcx, 0\n" ^
        "jle " ^ label_make_closure ^ "\n" ^
        label_copy_params ^ ":\n" ^  (*rcx will go from n...1*)
        "\tmov rax, [rbp + 4 * WORD_SIZE + WORD_SIZE * rcx - WORD_SIZE]\n" ^ (* rax <- param(rcx-1) *)
        "\tmov [rdx + WORD_SIZE * rcx - WORD_SIZE], rax\n" ^ (* new vector[rcx - 1] <- param(rcx-1) *)
        "\tloop " ^ label_copy_params ^ "\n" ^
        (* Allocate closure object *)
        (* Closure → Env ≔ ExtEnv *)
        (* Closure → Code ≔ Lcode *)
        label_make_closure ^ ":\n MAKE_CLOSURE(rax, rbx, " ^ label_closure_code ^ ")\n"
      in
      prepare_closure ^
      "jmp " ^ label_continue ^ "\n" ^ (* we run the below code only when applying the closure *)
      label_closure_code ^ ":\n" ^
      asm_opt_fix_stack_string (string_of_int(List.length params))^
      "\tpush rbp\n" ^  (* calling convention *)
      "\tmov rbp, rsp\n" ^
      generate_asm_from_expr consts fvars body (envSize + 1) ^ (* the actual closure code *)
      "\tleave\n" ^  (* returning convention *)
      "\tret\n" ^ 
      label_continue ^ ":\n" (*jump to here after making the closure object *)

    | ScmApplic' (proc, args) ->
      let label_check_closure = asm_label_applic_check true in
      let label_exit_applic = asm_label_exit true in 
      "push SOB_NIL_ADDRESS \n" ^
      List.fold_right (fun arg acc -> acc ^
                                      generate_asm_from_expr consts fvars arg envSize ^
                                      "push rax\n") args "" ^ (*generate code for all args then push them onto stack *)
      "push " ^ string_of_int (List.length args) ^ "\n" ^(*push number of args to stack *)
      generate_asm_from_expr consts fvars proc envSize ^ (*get the sob we are applying on to rax  *)
      "cmp byte [rax], T_CLOSURE\n" ^
      "je " ^ label_check_closure ^ "\n" ^
      "pop rcx \n" ^  
      "lea rcx, [rcx*WORD_SIZE] \n" ^
      "add rsp, rcx \n" ^
      "jmp " ^ label_exit_applic ^ "\n" ^
      label_check_closure ^ ":\n" ^ (*if sob is a closure then apply args to it *)
      "\tCLOSURE_ENV rbx, rax\n" ^ (*get closure extended env onto ecx *)
      "\tpush rbx\n" ^
      "\tCLOSURE_CODE rbx, rax\n" ^
      "\tcall rbx \n" ^ (*call the closure code *)
      "\tadd rsp, WORD_SIZE \n" ^ (*pop the env pointer from stack *)
      "\tpop rcx \n" ^  (*here we pop args from the stack after the call *)
      "\tinc rcx \n" ^
      "\tlea rcx, [rcx*8] \n" ^
      "\tadd rsp, rcx \n" ^
      label_exit_applic ^ ":\n"
    | ScmApplicTP'(proc , args) -> 
            let label_check_closure = asm_label_applic_check true in
      let label_exit_applic = asm_label_exit true in 
      "push SOB_NIL_ADDRESS \n" ^
      List.fold_right (fun arg acc -> acc ^
                                      generate_asm_from_expr consts fvars arg envSize ^
                                      "push rax\n") args "" ^ (*generate code for all args then push them onto stack *)
      "push " ^ string_of_int (List.length args) ^ "\n" ^(*push number of args to stack *)
      generate_asm_from_expr consts fvars proc envSize ^ (*get the sob we are applying on to rax  *)
      "cmp byte [rax], T_CLOSURE\n" ^
      "je " ^ label_check_closure ^ "\n" ^
      "pop rcx \n" ^  
      "lea rcx, [rcx*WORD_SIZE] \n" ^
      "add rsp, rcx \n" ^
      "jmp " ^ label_exit_applic ^ "\n" ^
      label_check_closure ^ ":\n" ^ (*if sob is a closure then apply args to it *)
      "\tCLOSURE_ENV rbx, rax\n" ^ (*get closure extended env onto ecx *)
      "\tpush rbx\n" ^
      "\tpush qword [rbp + WORD_SIZE] \n" ^
      "\tSHIFT_FRAME(" ^ string_of_int ((List.length args)+5) ^ ")\n" ^
      "\tCLOSURE_CODE rbx, rax \n" ^
      "\tjmp rbx \n" ^ (*call the closure code *)
      label_exit_applic ^ ":\n"
    | _ -> ""


  let generate consts fvars e = generate_asm_from_expr consts fvars e 0;;
end;;


