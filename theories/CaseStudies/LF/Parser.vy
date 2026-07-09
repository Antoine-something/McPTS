%{

From Coq Require Import List String.

From McPTS.CaseStudies.LF Require Import Frontend.

Parameter loc : Type.

Arguments eq_refl {_} _.

%}

%token <loc*string> VAR
%token <loc> LAMBDA PI TYPE KIND LET DEF_TYPE DEF_EXP (* keywords *)
%token <loc> ARROW "->" COLON ":" LPAREN "(" RPAREN ")" DOT "." COLONEQ ":=" EOF (* symbols *)

%start <Cst.obj * Cst.obj> prog
%type <Cst.obj> obj app_obj atomic_obj sort
%type <Cst.obj * Cst.obj> ann_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params
%type <Cst.obj> define_defns

%on_error_reduce obj params app_obj atomic_obj sort

%%

let prog :=
  | ~ = define_defns; EOF; { (define_defns, Cst.s_knd) }
  

let obj :=
  | PI; ~ = params; ":"; s = sort; "->"; ~ = obj; { List.fold_left (fun acc arg => Cst.pi (fst arg) Cst.s_typ s (snd arg) acc) params obj }
  | LAMBDA; ~ = params; ":"; s = sort; "->"; ~ = ann_obj; { 
    fst (
      List.fold_left (
        fun acc arg => (
          Cst.fn (fst arg) Cst.s_typ s (snd arg) (snd acc) (fst acc),
          Cst.pi (fst arg) Cst.s_typ s (snd arg) (snd acc) 
        ) 
      ) params ann_obj
    )}
  | ~ = app_obj; <>
  

let sort :=
  | TYPE; { Cst.s_typ }
  | KIND; { Cst.s_knd }

let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | ~ = sort; <>
  | x = VAR; { Cst.var (snd x) }
  | "("; ~ = obj; ")"; <>

(* Reversed nonempty list of parameters *)
let params :=
  | ~ = params; ~ = param; { param :: params }
  | ~ = param; { [param] }

(* (x : A) *)
let param :=
  | "("; x = VAR; ":"; ~ = obj; ")"; { (snd x, obj) }

(* (M : B) *)
let ann_obj :=
  | "("; exp = obj; ":"; ann = obj; ")"; { (exp, ann) }


let define_defns :=
  | DEF_TYPE; ~ = param; "."; ~ = define_defns; { 
      Cst.pi (fst param) Cst.s_knd Cst.s_knd (snd param) define_defns
   }
  | DEF_EXP; ~ = param; "."; ~ = define_defns; { 
      Cst.pi (fst param) Cst.s_typ Cst.s_knd (snd param) define_defns
   }
  | LET; ~ = param; COLONEQ; ~ = obj; "."; ~ = define_defns; {
      Cst.pi "#is_var" Cst.s_knd Cst.s_knd 
      (
        Cst.pi "#_" Cst.s_typ Cst.s_knd (snd param) Cst.s_typ
      ) 
      (
        Cst.pi (fst param) Cst.s_typ Cst.s_knd (Cst.app (Cst.var "#is_var") obj) define_defns
      )
    }
  | { Cst.s_typ }

%%

Extract Constant loc => "Lexing.position * Lexing.position".
