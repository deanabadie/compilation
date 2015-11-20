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

(*let nt_create_inst_ri =
  let nt' = caten nt_star_nl (caten nt_clear_ws_op (caten nt_clear_ws_reg (caten nt_imm_second_param nt_nl))) in
  let nt = pack nt' (fun (star_nl,(op,(reg,(imm,nl)))) -> InstRI (op, reg, imm)) in
  nt;;

let nt_create_inst_rr =
  let nt' = caten nt_star_nl (caten nt_clear_ws_op (caten nt_clear_ws_reg (caten nt_reg_second_param nt_nl))) in
  let nt = pack nt' (fun (star_nl,(op,(reg1,(reg2,nl)))) -> InstRR (op, reg1, reg2)) in
  nt;;*)

(*let nt_assembly_program =  
  let nt_nl = char '\n' in
  let nt_star_nl = star nt_nl in
  let nt' = caten nt_star_nl (caten (star (disj nt_create_inst_rr nt_create_inst_ri)) nt_star_nl) in
  let nt = pack nt' (fun (nl1,(inst,nl2)) -> inst) in
  nt;;*)
  (*let nt = star (disj nt_create_inst_rr nt_create_inst_ri) in
  nt;;*)
  (*let newLine = char '\n' in
  let unified = (disj nt_create_inst_ri nt_create_inst_rr) in
  let nt' = caten (plus newLine) unified in
  let nt'' = pack nt' (fun (nl,inst) -> inst) in
  let nt = caten unified (star nt') in
  nt;;*)
  
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

(* 2.3 ------------Need to Change----------- *)
(*let cut_scm = function
  | ScmAdd -> Add
  | ScmSub -> Sub
  | ScmMul -> Mul
  | ScmDiv -> Div;;*)
let nt_get_scheme_op op =
  match op with
  | ScmAdd -> Add | ScmSub -> Sub | ScmMul -> Mul | ScmDiv -> Div;;
    

let compile_arith scm_expr =
  let rec arithRI reg_num = 
    function
    |(ScmInt n) -> [InstRI (Mov, (Reg reg_num), (Imm n))]
    |(ScmOp (op,head::tail)) -> (arithRI reg_num head) @ (List.flatten (List.map (arithRR (cut_scm op) reg_num) tail)) 
    | _ -> [] 

  and arithRR opration reg_num  =
    function
    |(ScmInt n) -> [InstRI (opration,(Reg reg_num),(Imm n))]
    |(ScmOp (op,arg)) -> (arithRI (reg_num + 1) (ScmOp (op,arg))) @ [InstRR (opration,(Reg reg_num), (Reg (reg_num + 1)))]
 
  in arithRI 0 scm_expr;;

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
(*  | Reg (r) -> "r" ^ (string_of_int r)
  | Imm (i) -> (string_of_int i);;*)

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
let reg_array insts = Array.make (find_max_register insts) Uninitialized;;

let decompile_assembly_program insts =
try
  let arr = reg_array insts in 

  let rec loop_insts =
    function
    | [] -> ()
    | ins::rest -> begin ass_inst ins; loop_insts rest end

  and  ass_inst =
    function 
    | InstRI (Mov,(Reg r),(Imm n)) -> arr.(r) <- (ScmInt' n)
    | InstRI (op,(Reg r),(Imm n)) -> if (arr.(r) == Uninitialized) then
        raise X_Expression_includes_uninitialized_values 
      else arr.(r) <- ScmOp' ((add_scm op), [arr.(r);(ScmInt' n)])
    | InstRR (Mov,(Reg r1),(Reg r2)) -> if (arr.(r2) == Uninitialized) then
        raise X_Expression_includes_uninitialized_values 
      else arr.(r1) <- arr.(r2)
    | InstRR (op,(Reg r1),(Reg r2)) -> if (arr.(r1) == Uninitialized || arr.(r2) == Uninitialized) then
        raise X_Expression_includes_uninitialized_values 
      else arr.(r1) <- ScmOp' ((add_scm op), [arr.(r1);arr.(r2)])

  and add_scm = 
    function | Add -> ScmAdd | Sub -> ScmSub | Mul -> ScmMul | Div -> ScmDiv |_ -> raise X_Expression_includes_uninitialized_values

  in begin loop_insts insts; arr.(0) end

with X_Expression_includes_uninitialized_values -> Uninitialized;;


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
