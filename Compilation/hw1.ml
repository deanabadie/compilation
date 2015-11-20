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

let nt_scmOp =
  let nt = char '+' in
  let nt = pack nt (fun _ -> ScmAdd) in
  let nt' = char '-' in
  let nt' = pack nt' (fun _ -> ScmSub) in
  let nt'' = char '*' in
  let nt'' = pack nt'' (fun _ -> ScmMul) in
  let nt''' = char '/' in
  let nt''' = pack nt''' (fun _ -> ScmDiv) in
  let nt = disj nt (disj nt' (disj nt'' nt''')) in
  nt;;

let nt_open = 
 let nt = char '(' in
 nt;;

let nt_close = 
 let nt = char ')' in
 nt;;

let nt_expr =
 let nti = nt_int in
 let nti = pack nti (fun x -> ScmInt(x)) in

 let nto = caten nt_open nt_scmOp in
 let nto = pack nto (fun (_,o) -> o) in

 let nte =  nt_int in
 let nte = caten nt_whitespace nte in
 let nte = pack nte (fun (_,x) -> ScmInt(x)) in
 let nte' = plus nte in
 let nte = caten nte nte' in
 let nte = pack nte (fun (x,l) -> x::l) in

 let nt = caten nto nte in
 let nt = caten nt nt_close in
 let nt = pack nt (fun ((op,l),_) -> (ScmOp(op,l))) in
 
 let nt = disj nt nti in
 nt;; 



let nt_assembly_program =
  let ntw = star nt_whitespace in
  let nt = caten ntw nt_opcode in
  let nt = pack nt (fun (_,o)->o) in
  let nt = caten nt ntw in
  let nt = pack nt (fun (o,_)->o) in
  let nt = caten nt nt_register in
  let nt = caten nt ntw in
  let nt = pack nt (fun (o,_)->o) in
  let nt = caten nt (char ',') in
  let nt = pack nt (fun (o,_)->o) in
  let nt = caten nt ntw in
  let nt = pack nt (fun (o,_)->o) in

  let nti = caten (char '$') nt_imm in
  let nti = pack nti (fun (_,x) -> x) in

  let nti = caten nt nti in
  
  let nti = pack nti (fun ((o,r),i)->InstRI(o,r,i))  in
  
  let ntr = caten nt nt_register in
  
  let ntr = pack ntr (fun ((o,r1),r2)->InstRR(o,r1,r2))  in

  let nt = disj nti ntr in

  let nts = caten (char '\n') nt in
  let nts = pack nts (fun (_,x)->x) in
  
  let nts = star nts in
  
  let nt = caten nt nts in
  let nt = pack nt (fun (x,l)->x::l) in

  let nt = caten nt ntw in
  let nt = pack nt (fun (x,_)->x) in
  nt;;
  

end;; (* end of struct Parsers *)

module type FULL_CYCLE = sig
  val compile_arith : expr -> inst list
  val assembly_program_to_string : inst list -> string
  val decompile_assembly_program : inst list -> expr'
  val expr'_to_string : expr' -> string
  val full_cycle : string -> string
end;; (* end of signature FULL_CYCLE *)

module Full_Cycle (*: FULL_CYCLE*) = struct

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

let compile_arith (ScmInt n) =
  [InstRI (Mov,(Reg 0),(Imm n))];;

(* do not add your own code after this *)

(*let full_cycle string =
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
 *)
end;; (* end of struct Full_Cycle *)
  
(* end of input *)