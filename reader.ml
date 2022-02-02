(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

type interpolated_string_part = 
|Dynamic of sexpr
|Static of sexpr;;  
type static_string_part = 
|StaticChar of char;;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
   
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;
open Char;;
open Scanf;;
open Stdlib;;

let nt_digit = range '0' '9';;
let unitify nt = pack nt (fun _ -> ());;

(*vars for meta & literal & hexa string*)
let s_single_backslash = char '\\';;
let s_hexa = word "\\x";;
let s_double_backslash = word "\\\\";;
let s_backslah_dquote = word "\\\"";;
let s_tab = word "\\t";;
let s_form = word "\\f";; 
let s_new_line = word "\\n";;
let s_return = word "\\r";;
let s_tilde = word "\\~~";;

let bad_char = 
disj_list [s_single_backslash; (*'\'*)
    (char '"'); 
    (char '~');
  ];;

let hex_char = (**for char req *) 
  let hex_char = range_ci 'a' 'f' in
  disj_list [hex_char; nt_digit];;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
(**//////////////////////////////////////////////////// COMMENT//////////////////////////////////////////////////////////////////// *)  
and nt_line_comment str = let nt1 = char ';' in 
                          let nt2 = diff nt_any nt_end_of_line_or_file in
                          let nt2 = star nt2 in 
                          let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
                          (unitify nt1) str
and nt_paired_comment str = 
  let nt1 = char '{' in
  let nt2 = char '}' in
  let nt3 = star nt_sexpr in
  let nt4 = caten nt1 (caten nt3 nt2) in
  let nt1 = unitify nt4 in 
  nt1 str
and nt_sexpr_comment str = 
  let nt1 = word "#;" in
  let nt2 = caten nt1 nt_sexpr in
  (unitify nt2) str
and nt_comment str = (**TODO - check this *)
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
(**//////////////////////////////////////////////////// COMMENT//////////////////////////////////////////////////////////////////// *) 
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
(**//////////////////////////////////////////////////// NUMBER//////////////////////////////////////////////////////////////////// *)  
and nt_digit = range '0' '9'
and nt_sign str= 
let nt_plus = char '+' in
let nt_minus = char '-' in
let nt1 = pack nt_plus (fun (_) -> 1) in
let nt2 = pack nt_minus (fun (_) -> -1) in
let nt1 = disj nt1 nt2 in
nt1 str
and nt_make_number str = 
let nt_num = plus nt_digit in
let nt1 = pack nt_num (fun (num) -> int_of_string(list_to_string num)) in
nt1 str 
and nt_int str = 
  let nt1 = maybe nt_sign in 
  let nt2 = nt_make_number in
  let nt1 = caten nt1 nt2 in 
  let nt1 = pack nt1 (fun (sign, num) -> match sign with
                          |Some(-1) -> (num * (-1))
                          |Some(plus) -> num
                          |None -> num) in
  nt1 str
and nt_num_no_zero str = 
  let digit = range '1' '9' in
  let nt_num = plus digit in
  let nt1 = pack nt_num (fun (num) -> int_of_string(list_to_string num)) in
  nt1 str    
and nt_frac str = 
  let nt_slash = char '/' in
  let nt_natural = nt_num_no_zero in
  let nt1 = caten nt_int (caten nt_slash nt_natural) in
  let nt1 = pack nt1 (fun (intval,(slash,num)) -> ScmRational(intval/(gcd intval num), num/(gcd intval num))) in
  nt1 str
and nt_integer_part str = 
  let nt_natural = nt_make_number in
  nt_natural str
and nt_mantissa str = 
  let nt_mantissa = plus nt_digit in
  nt_mantissa str
and nt_exponent str = 
  let nt_exponent_token = disj_list [(word "e");(word "E");(word "*10^");(word "*10**")] in
  let nt_exponent = caten nt_exponent_token nt_int in
  let nt_exponent = pack nt_exponent (fun (token,integer) -> integer) in
  nt_exponent str
and string_to_mantissa x = float_of_int(int_of_string(list_to_string(x))) *. (10.**(-1.*. float_of_int(String.length(list_to_string(x)))))    
and nt_float_A str = 
  let nt1 = caten nt_integer_part (caten (char '.') (caten (maybe nt_mantissa) (maybe nt_exponent))) in 
  let nt1 = pack nt1 (fun (integer,(dot,(mantissa,exponent))) -> (match mantissa,exponent with
                     | Some(x),Some(y) -> (
                                          (float_of_int(integer) +. string_to_mantissa(x)) 
                                          *.(10.**float_of_int(y)))
                     | None , Some(y) -> (float_of_int(integer) *. (10.**float_of_int(y)))
                     | Some(x),None -> (float_of_int(integer)+. float_of_int(int_of_string(list_to_string(x))) *. (10.**(-1.*. float_of_int(String.length(list_to_string(x))))))
                     | None, None -> ( float_of_int(integer))
                     )) in
  nt1 str
and nt_float_B str = 
  let nt1 = caten (char '.') (caten nt_mantissa (maybe nt_exponent)) in
  let nt1 = pack nt1 (fun (dot_token,(mantissa,exponent)) -> match exponent with
                     | Some(x) -> (string_to_mantissa(mantissa) *. 10.**float_of_int(x))
                     | None -> (string_to_mantissa(mantissa))
                     ) in
  nt1 str
and nt_float_C str = 
  let nt1 = caten nt_make_number nt_exponent in
  let nt1 = pack nt1 (fun (integer,exponent) -> (float_of_int(integer) *. 10.**float_of_int(exponent))) in
  nt1 str

and nt_float str = 
  let nt1 = maybe nt_sign in
  let nt2 = disj_list[nt_float_A ; nt_float_B ; nt_float_C] in
  let nt2 = caten nt1 nt2 in
  let nt2 = pack nt2 (fun (sign,num) -> match sign with 
                      |Some(-1) -> (num *. float_of_int(-1))
                      |Some(plus) -> num
                      |None -> num) in
  let nt1 = pack nt2 (fun (num) -> ScmReal(num)) in
  nt1 str
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str  
(**//////////////////////////////////////////////////// NUMBER//////////////////////////////////////////////////////////////////// *)  
and nt_boolean str = let nt1 = word_ci "#t" in
                     let nt1 = pack nt1 (fun _ -> true) in
                     let nt2 = word_ci "#f" in
                     let nt2 = pack nt2 (fun _ -> false) in
                     let nt1 = disj nt1 nt2 in
                     let nt1 = pack nt1 (fun b -> ScmBoolean b) in
                     nt1 str
(**//////////////////////////////////////////////////// CHAR/////////////////////////////////////////////////////////////////////// *)                     
and nt_char_simple str = let nt1 = const (fun ch -> ch > ' ') in (**take all chars that are greater that space-char *)
                         let nt1= pack nt1 (fun c -> ScmChar(c)) in
                         nt1 str
and make_named_char char_name ch = let nt_phrase = word char_name in
                                   let nt1 = pack nt_phrase (fun word -> ScmChar(ch)) in
                                   nt1 
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str = (** *)
  let nt1 = char 'x' in 
  let nt2 = plus hex_char in
  let nt3 = pack nt2 (fun hex -> char_of_int(int_of_string("0x" ^ (list_to_string hex)))) in
  let nt2 = caten nt1 nt3 in
  let nt1 = pack nt2 (fun (x, hex) -> ScmChar(hex)) in
  nt1 str 
and nt_char str =
  let nt1 = word "#\\" in
  let nt2 = 
    disj_list [nt_char_hex;
              nt_char_named;
              nt_char_simple] in
  let nt3 = caten nt1 nt2 in
  let nt1 = pack nt3 (fun (prefix,char)-> char) in
  nt1 str
(**//////////////////////////////////////////////////// CHAR/////////////////////////////////////////////////////////////////////// *)
and nt_symbol_char str = let nt1 = disj_list [
  (range '0' '9');
  (range_ci 'a' 'z');
  (char '!');
  (char '$');
  (char '^');
  (char '*');
  (char '-');
  (char '_');
  (char '=');
  (char '+');
  (char '<');
  (char '>');
  (char '?');
  (char '/');
  (char ':');
] in
  nt1 str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str
(**//////////////////////////////////////////////////// STRING//////////////////////////////////////////////////////////////////// *)  
and interpolated_format myExpr = ScmPair(ScmSymbol "format", ScmPair(ScmString "~a", ScmPair(myExpr, ScmNil)))
and nt_string_literal_char str =
  let nt1 = diff nt_any (one_of "\\\"~") in
  let nt1 = pack nt1 (fun st -> StaticChar st) in
  nt1 str
  
and nt_string_meta_char str =
  let meta_char = disj_list [
   pack s_double_backslash (fun _ -> '\092');
   pack s_backslah_dquote (fun _ -> '\034');
   pack s_tab (fun _ -> '\009');
   pack s_form (fun _ -> '\012');
   pack s_new_line (fun _ -> '\010');
   pack s_return (fun _ -> '\013');
   pack s_tilde (fun _ -> '\126');
  ] in 
  let nt1 = pack meta_char (fun st -> StaticChar st) in 
  nt1 str
 
and nt_string_hex_char str = 
  let nt2 = plus hex_char in
  let nt3 = word ";" in
  let nt1 = caten s_hexa (caten nt2 nt3) in
  let nt2 = pack nt1 (fun (_,(b,_)) -> char_of_int (int_of_string ("0x" ^ list_to_string b))) in
  let nt1 = pack nt2 (fun st -> StaticChar st) in 
  nt1 str 

  and nt_string_interpolate str = 
  let nt1 = word "~{" in
  let nt2 = word "}" in
  let nt3 = caten nt1 nt_skip_star in
  let nt4 = caten nt_sexpr nt2 in
  let nt2 = caten nt3 nt4 in
  let nt1 = pack nt2 (fun ((leftBracket, skipStar), (myExpr, rightBracket)) -> Dynamic myExpr) in
  nt1 str

and nt_string_options str =
  let nt1 = disj_list[
    nt_string_literal_char;
    nt_string_meta_char;
    nt_string_hex_char;] in
  nt1 str

and nt_static_string str = (**take care of static strings *)
  let nt1 = plus nt_string_options in
  let nt2 = pack nt1 (fun lst -> match lst with 
  | [] -> ScmString ""
  | [StaticChar hd] -> ScmString (String.make 1 hd)
  | _ -> ScmString (List.fold_left (fun first nextChar -> match nextChar with
                                    |StaticChar nextChar -> first ^ (String.make 1 nextChar))"" lst)) in
  let nt1 = pack nt2 (fun scmstr -> Static scmstr) in                                  
  nt1 str        
and nt_get_sexpr a = match a with
                    | Static s -> s (*already ScmString*)
                    | Dynamic s -> interpolated_format s                            
and nt_string str =
  let nt1 = (char '\"') in
  let nt2 = disj nt_static_string nt_string_interpolate in
  let nt2 = star nt2 in
  let nt3 = caten nt1 (caten nt2 nt1) in (**(leftp,(sexpLst, rightp)) *)
  let nt2 = pack nt3 (fun (leftp,(sexpLst, rightp)) -> match sexpLst with
  | [] -> ScmString ""
  | [Static hd] -> hd (**already a ScmString *)
  | [Dynamic hd] -> interpolated_format hd
  | hd::tl -> (List.fold_left (fun first nextExpr -> match nextExpr with
                                    |Dynamic nextExpr -> ScmPair(ScmSymbol "string-append", 
                                      ScmPair(first,ScmPair(ScmSymbol "format", ScmPair(ScmString "~a", ScmPair(interpolated_format nextExpr, ScmNil)))))
                                    | _ -> raise X_no_match) (nt_get_sexpr hd) tl)
)in
  nt2 str
(**//////////////////////////////////////////////////// STRING//////////////////////////////////////////////////////////////////// *)
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
(**//////////////////////////////////////////////////// LIST//////////////////////////////////////////////////////////////////// *)  
and nt_proper_list str = (**TODO - works *)
  let nt1 = char '(' in
  let space = star nt_whitespace in
  let nt1 = caten space (caten nt1 space) in (**(space, (rightP, space)) *)
  let nt2 = char ')' in
  let nt2_space = caten space nt2 in (**(space, leftP) *)
  let nt2 = caten nt2_space space in (**((space, leftP),space) *)
  let nt3 = star nt_sexpr in
  let nt2 = caten nt1 (caten nt3 nt2) in (**((space, (rightP, space)),(exprLst,((space, leftP),space))) *)
  let nt3 = pack nt2 (fun ((space1, (rightP, space2)),(exprLst,((space3, leftP),space4))) -> exprLst) in 
  let nt1 = pack nt3 (fun lst -> match lst with
    |_ -> List.fold_right (fun head tail -> ScmPair(head, tail)) lst ScmNil) in
  nt1 str  
and nt_improper_list str = (**TODO - works *)
  let nt1 = char '(' in
  let nt2 = char ')' in
  let nt3 = plus nt_sexpr in
  let nt4 = char '.' in
  let nt5 = caten nt1 (caten nt3 nt4) in (* (left,(sexp,point))* *)
  let nt3 = caten nt5 (caten nt_sexpr nt2) in (* ((left,(sexp1,point)),(sexp2, right))* *)
  let nt1 = pack nt3 (fun ((left,(sexp1,point)),(sexp2, right)) -> List.fold_right(fun head tail -> ScmPair (head, tail))sexp1 sexp2) in
  nt1 str  
and nt_list str = 
  let nt1 = disj nt_proper_list nt_improper_list in
  nt1 str
(**//////////////////////////////////////////////////// LIST//////////////////////////////////////////////////////////////////// *)
(**//////////////////////////////////////////////////// QUOTE/////////////////////////////////////////////////////////////////// *)  
and nt_quoted str =
  let nt1 = char '\'' in
  let nt2 = caten nt1 nt_sexpr in
  let nt1 = pack nt2 (fun (quote, sexp) -> ScmPair(ScmSymbol "quote", ScmPair(sexp, ScmNil))) in
  nt1 str
and nt_quasi_quoted str =
  let nt1 = char '`' in
  let nt2 = caten nt1 nt_sexpr in
  let nt1 = pack nt2 (fun (qquote, sexp) -> ScmPair(ScmSymbol "quasiquote", ScmPair(sexp, ScmNil))) in
  nt1 str
and nt_unquoted str =
  let nt1 = char ',' in
  let nt2 = caten nt1 nt_sexpr in
  let nt1 = pack nt2 (fun (unquote, sexp) -> ScmPair(ScmSymbol "unquote", ScmPair(sexp,ScmNil))) in
  nt1 str
and nt_unquote_and_spliced str =
  let nt1 = word ",@" in
  let nt2 = caten nt1 nt_sexpr in
  let nt1 = pack nt2 (fun (unqs, sexp) -> ScmPair(ScmSymbol "unquote-splicing", ScmPair(sexp, ScmNil))) in 
  nt1 str    
and nt_quoted_forms str = (**works *)
  let nt1 = disj_list[nt_quoted; nt_quasi_quoted; nt_unquoted; nt_unquote_and_spliced] in
  nt1 str
(**//////////////////////////////////////////////////// QUOTE/////////////////////////////////////////////////////////////////// *)  
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;
end;; (* end of struct Reader *)



let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;