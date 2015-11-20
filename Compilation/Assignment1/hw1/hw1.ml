(* hw1.ml *)

#use "pc.ml";;

(* *)

type reg = Reg of int;;

type imm = Imm of int;;

type opcode = Add | Sub | Mul | Div | Mov;;

type inst =
  | InstRR of opcode * reg * reg
  | InstRI of opcode * reg * imm;;

type scm_op = ScmAdd | ScmSub | ScmMul | ScmDiv;;
  
type expr =
  | ScmInt of int
  | ScmOp of scm_op * expr list;;

type expr' =
  | Uninitialized
  | ScmInt' of int
  | ScmOp' of scm_op * expr' list;;

exception X_This_should_not_happen;;
exception X_Not_yet_implemented;;
exception X_Expression_includes_uninitialized_values;;
exception X_Cannot_parse_expr_string;;
exception X_Cannot_parse_assembly_program_string;;

module type PARSERS = sig
  val nt_assembly_program : char list -> inst list * char list
  val nt_expr : char list -> expr * char list
end;; (* end of signature PARSERS *)

module Parsers : PARSERS = struct 
open PC;;
  
let make_char_value base_char displacement =
  let base_char_value = Char.code base_char in
  fun ch -> (Char.code ch) - base_char_value + displacement;;

let nt_digit_0_9 = pack (range '0' '9') (make_char_value '0' 0);;
  
let nt_digit_1_9 = pack (range '0' '9') (make_char_value '0' 0);;
  
let nt_nat =
  let nt = range '1' '9' in
  let nt = pack nt (make_char_value '0' 0) in
  let nt' = range '0' '9' in
  let nt' = pack nt' (make_char_value '0' 0) in
  let nt' = star nt' in
  let nt = caten nt nt' in
  let nt = pack nt (fun (d, ds) -> (d :: ds)) in
  let nt = pack nt (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in
  let nt' = char '0' in
  let nt'' = char '0' in
  let nt''' = range '0' '9' in
  let nt'' = caten nt'' nt''' in
  let nt' = diff nt' nt'' in
  let nt' = pack nt' (fun e -> 0) in
  let nt = disj nt nt' in
  nt;;

let nt_register =
  let nt = char_ci 'r' in
  let nt = caten nt nt_nat in
  let nt = pack nt (fun (_r, n) -> (Reg n)) in
  nt;;

let nt_int =
  let nt = char '-' in
  let nt = pack nt (fun e -> -1) in
  let nt' = char '+' in
  let nt' = pack nt' (fun e -> 1) in
  let nt = disj nt nt' in
  let nt = maybe nt in
  let nt = pack nt (function | None -> 1 | Some(mult) -> mult) in
  
  let nt' = range '0' '9' in
  let nt' = pack nt' (make_char_value '0' 0) in
  let nt' = plus nt' in
  let nt' = pack nt' (fun s -> List.fold_left (fun a b -> a * 10 + b) 0 s) in

  let nt = caten nt nt' in
  let nt = pack nt (fun (mult, n) -> (mult * n)) in
  nt;;

let nt_imm = pack nt_int (fun n -> (Imm n));;

let nt_opcode =
  let nt = word_ci "add" in
  let nt = pack nt (fun _ -> Add) in
  let nt' = word_ci "sub" in
  let nt' = pack nt' (fun _ -> Sub) in
  let nt'' = word_ci "mul" in
  let nt'' = pack nt'' (fun _ -> Mul) in
  let nt''' = word_ci "div" in
  let nt''' = pack nt''' (fun _ -> Div) in
  let nt'''' = word_ci "mov" in
  let nt'''' = pack nt'''' (fun _ -> Mov) in
  let nt = disj nt (disj nt' (disj nt'' (disj nt''' nt''''))) in
  nt;;

(* add your own code here after this comment *)

(* 2.2 *)
let nt_scmop =
  let nt_add = char '+' in
  let nt_add = pack nt_add (fun o -> (ScmAdd)) in
  let nt_sub = char '-' in
  let nt_sub = pack nt_sub (fun o -> (ScmSub)) in
  let nt_mul = char '*' in
  let nt_mul = pack nt_mul (fun o -> (ScmMul)) in
  let nt_div = char '/' in
  let nt_div = pack nt_div (fun o -> (ScmDiv)) in
  let nt = disj nt_add (disj nt_sub (disj nt_mul nt_div)) in
  nt;;

let nt_scmint =
  pack nt_int (fun n -> (ScmInt n));;

let nt_clear_ws_left_bracket =
  let nt_star_ws = star nt_whitespace in
  let nt_left_bracket = char '(' in
  let nt_lb_with_ws = caten nt_star_ws (caten nt_left_bracket nt_star_ws) in
  let nt = pack nt_lb_with_ws (fun (_,(e,_)) -> e) in
  nt;;

let nt_clear_ws_right_bracket =
  let nt_star_ws = star nt_whitespace in
  let nt_right_bracket = char ')' in
  let nt_rb_with_ws = caten nt_star_ws (caten nt_right_bracket nt_star_ws) in
  let nt = pack nt_rb_with_ws (fun (_,(e,_)) -> e) in
  nt;;

let nt_clear_ws_num =
  let nt_star_ws = star nt_whitespace in
  let nt_num_with_ws = caten nt_star_ws (caten nt_scmint nt_star_ws) in
  let nt = pack nt_num_with_ws (fun (_,(e,_)) -> e) in
  nt;;


let rec nt_expr_rec () =
  disj
    (pack
       (caten nt_clear_ws_left_bracket
	      (caten nt_scmop 
		(caten (plus (delayed nt_expr_rec)) nt_clear_ws_right_bracket)))
                   (fun (lb,(op,(rec_expr,rb))) -> ScmOp(op,rec_expr)))
    nt_clear_ws_num;;

let nt_expr = 
    nt_expr_rec ();;

  (* 2.5 *)
let nt_clear_ws_op = 
  let nt_star_ws = star nt_whitespace in
  let nt_op_with_ws = caten nt_star_ws (caten nt_opcode nt_star_ws) in
  let nt = pack nt_op_with_ws (fun (_,(e,_)) -> e) in
  nt;;

let nt_clear_ws_reg =
  let nt_star_ws = star nt_whitespace in
  let nt_reg_with_ws = caten nt_star_ws nt_register in
  let nt = pack nt_reg_with_ws (fun (_,reg) -> reg) in
  nt;;

let nt_reg_second_param =
  let nt_comma = char ',' in
  let nt_star_ws = star nt_whitespace in
  let nt_with_register = caten nt_comma (caten nt_star_ws (caten nt_register nt_star_ws)) in
  let nt = pack nt_with_register (fun (comma,(_,(reg,_))) -> reg) in
  nt;;

let nt_imm_second_param = 
  let nt_comma = char ',' in
  let nt_star_ws = star nt_whitespace in
  let nt_dollar = char '$' in
  let nt_imm_second_param = caten nt_comma (caten nt_star_ws (caten nt_dollar (caten nt_imm nt_star_ws))) in
  let nt = pack nt_imm_second_param (fun (comma,(_,(dollar,(imm,_)))) -> imm) in
  nt;;

let nt_nl = char '\n';;
let nt_star_nl = star nt_nl;;

let nt_create_inst_ri =
  (*let nt_new_line = char '\n' in*)
  let nt' = caten nt_clear_ws_op (caten nt_clear_ws_reg nt_imm_second_param) in
  let nt = pack nt' (fun (op,(reg,imm)) -> InstRI (op, reg, imm)) in
  nt;;

let nt_create_inst_rr =
  let nt' = caten nt_clear_ws_op (caten nt_clear_ws_reg nt_reg_second_param) in
  let nt = pack nt' (fun (op,(reg1,reg2)) -> InstRR (op, reg1, reg2)) in
  nt;;

let nt_assembly_program =
  let nt = star (disj nt_create_inst_ri nt_create_inst_rr) in
  nt;;
  
end;; (* end of struct Parsers *)

module type FULL_CYCLE = sig
  val compile_arith : expr -> inst list
  val assembly_program_to_string : inst list -> string
  val decompile_assembly_program : inst list -> expr'
  val expr'_to_string : expr' -> string
  val full_cycle : string -> string
end;; (* end of signature FULL_CYCLE *)

module Full_Cycle : FULL_CYCLE = struct

let apply_append s = List.fold_right (@) s [];;

let find_max_register insts =  
  1 + (List.fold_right max 
		       (List.map
			  (function
			    | InstRI(_, (Reg i), _) -> i
			    | InstRR(_, (Reg i), (Reg j)) -> (max i j))
			  insts)
		       0);;

(* add your own code after this *)

(* 2.3 *)

let next_reg r = r + 1;;

let nt_get_scheme_op op =
  match op with
  | ScmAdd -> Add | ScmSub -> Sub | ScmMul -> Mul | ScmDiv -> Div;;
    
let compile_arith scm_expr =
  let rec with_imm reg expr =
    match expr with 
    | ScmInt num -> [InstRI (Mov, Reg reg, Imm num)]
    | ScmOp (op,car::cdr) -> List.append (with_imm reg car) (List.concat (List.map (with_reg (nt_get_scheme_op op) reg) cdr)) 
    | x -> []
  and with_reg operator reg expr =
    match expr with
    | ScmInt num -> [InstRI (operator, Reg reg, Imm num)]
    | ScmOp (op,param) -> List.append (with_imm (next_reg reg) (ScmOp (op,param))) [InstRR (operator,(Reg reg), (Reg (next_reg reg)))]
  in with_imm 0 scm_expr;;

(* 2.4 *)
let opcode_to_string e =
  match e with
  | Add -> "add"
  | Sub -> "sub"
  | Mul -> "mul"
  | Div -> "div"
  | Mov -> "mov"

let reg_to_string r =
  match r with
  | Reg (r) -> "r" ^ (string_of_int r)

let imm_to_string i =
  match i with
  |Imm (i) -> string_of_int i


let convert e =
  match e with
  | InstRI (op, reg, imm) -> (opcode_to_string op) ^ " " ^ (reg_to_string reg) ^ "," ^ " $" ^ (imm_to_string imm)
  | InstRR (op, reg1, reg2) -> (opcode_to_string op) ^ " " ^ (reg_to_string reg1) ^ ", " ^ (reg_to_string reg2)

let assembly_program_to_string p = 
  let rec helper_2_4 = function
    | [] -> ""
    | [x] -> (convert x)
    | car::cdr -> (convert car) ^ "\n" ^ (helper_2_4 cdr)  
  in
  helper_2_4 p;;

(*let assembly_program_to_string p =
  let ls = List.map convert p in
  List.fold_right (fun a b -> a ^ "\n" ^ b) ls "";;*)

(* 2.6 *)

let opDeriv op =
  match op with 
  | Add -> ScmAdd
  | Sub -> ScmSub
  | Mul -> ScmMul
  | Div -> ScmDiv
  | _   -> assert false;;

let decompile_assembly_program coms = 
  let uni = Uninitialized in
  let vec = Array.make (find_max_register coms) uni in
  let rec iter coms=
    match coms with
    | [] -> ()
    | car::cdr -> toScheme car; iter cdr 
  and toScheme coms=
    match coms with
    | InstRI (Mov,Reg reg,Imm num) -> 
      vec.(reg) <- (ScmInt' num)
    | InstRR (Mov,Reg reg1,Reg reg2)  when 
      (vec.(reg2) != uni) -> 
      vec.(reg1) <- vec.(reg2)
    | InstRI (op,Reg reg,Imm num) when 
      (vec.(reg) != uni)-> 
      vec.(reg) <- ScmOp' (opDeriv op, List.append [vec.(reg)] [ScmInt' num])
    | InstRR (op,Reg reg1,Reg reg2) when 
      (vec.(reg1) != uni && vec.(reg2) != uni) ->
      vec.(reg1) <- ScmOp' (opDeriv op, List.append [vec.(reg1)] [vec.(reg2)])
    | _ -> vec.(0) <- uni
  
  in 
  iter coms;
  let ret = vec.(0) in
  ret;;


(* 2.7 *)
let opDeriv = function
  | ScmAdd -> "+" | ScmSub -> "-" | ScmMul -> "*" | ScmDiv -> "/";;
 
let expr'_to_string expr' =
  let rec helper1 = function
    | Uninitialized -> raise (X_Expression_includes_uninitialized_values)
    | (ScmInt' num) -> (string_of_int num)
    | (ScmOp' (op,lst)) -> "(" ^ (opDeriv op) ^ (helper2 lst) ^ ")"

  and helper2 = function
    | [] -> ""
    | car::cdr -> " " ^ (helper1 car) ^ (helper2 cdr)

  in
  helper1 expr';;


(* do not add your own code after this *)

let full_cycle string =
  try (match (Parsers.nt_expr (string_to_list string)) with
       | (expr, []) ->
	  (try (match (Parsers.nt_assembly_program
			 (string_to_list
			    (assembly_program_to_string
			       (compile_arith expr)))) with 
		| (insts, []) ->
		   (expr'_to_string (decompile_assembly_program insts))
		| _ -> raise X_Cannot_parse_assembly_program_string)
	   with PC.X_no_match -> raise X_Cannot_parse_assembly_program_string)
	      | _ -> raise X_Cannot_parse_expr_string)
  with PC.X_no_match -> raise X_Cannot_parse_expr_string;;

end;; (* end of struct Full_Cycle *)
  
(* end of input *)
