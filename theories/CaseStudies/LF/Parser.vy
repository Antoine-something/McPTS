%{

From Coq Require Import List String.

From McPTS.CaseStudies.LF Require Import Frontend.

Parameter loc : Type.

Arguments eq_refl {_} _.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE KIND ZERO LET IN ASSIGN (* keywords *)
%token <loc> ARROW "->" BAR "|" COLON ":" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" DOT "." EOF DEF ":=" (* symbols *)

%start <Cst.obj * Cst.obj> prog
%type <Cst.obj> obj app_obj atomic_obj sort
%type <Cst.obj * Cst.obj> ann_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params
%type <((string * Cst.obj) * Cst.obj) * Cst.obj> let_defn
%type <string * Cst.obj> assign_defn
%type <list (string * Cst.obj)> assign_defns

%on_error_reduce obj params app_obj atomic_obj sort

%%

let prog :=
  exp = obj; ":"; ty = obj; EOF; <>

let obj :=
  | PI; ~ = params; ":"; s = sort; "->"; ~ = obj; { List.fold_left (fun acc arg => Cst.pi (fst arg) Cst.s_typ s (snd arg) acc) params obj }
  | LAMBDA; ~ = param; ":"; s = sort; "->"; ~ = ann_obj; { Cst.fn (fst param) Cst.s_typ s (snd param) (snd ann_obj) (fst ann_obj) }
  | ~ = app_obj; <>
  | REC; escr = obj; RETURN; mx = VAR; "."; em = obj;
    "|"; ZERO; "=>"; ez = obj;
    "|"; SUCC; sx = VAR; ","; sr = VAR; "=>"; es = obj;
    END; { Cst.natrec escr (snd mx) em ez (snd sx) (snd sr) es }

  | SUCC; ~ = atomic_obj; { Cst.succ atomic_obj }

  | LET; ds = let_defn; IN; body = ann_obj; {Cst.app (Cst.fn (fst (fst (fst ds))) Cst.s_typ (snd ds) (snd (fst (fst ds))) (snd body) (fst body)) (snd (fst ds)) }
  | ds = assign_defns; body = ann_obj; { 
    fst (
      List.fold_left (
        fun acc arg => (
          Cst.fn (fst arg) Cst.s_knd Cst.s_knd (snd arg) (snd acc) (fst acc),
          Cst.pi (fst arg) Cst.s_knd Cst.s_knd (snd arg) (snd acc) 
        ) 
      ) ds body
    )
  }

let sort :=
  | TYPE; { Cst.s_typ }
  | KIND; {Cst.s_knd}

let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | ~ = sort; <>

  | NAT; { Cst.nat }
  | ZERO; { Cst.zero }
  | n = INT; { nat_rect (fun _ => Cst.obj) Cst.zero (fun _ => Cst.succ) (snd n) }

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


(* (x : A) : s := t *)
let let_defn :=
  | ~ = param; ":"; s = sort; ":="; ~ = obj; { ((param, obj), s) }

(* Reversed nonempty list of assignments *)
let assign_defns :=
  | ~ = assign_defns; ~ = assign_defn; { assign_defn :: assign_defns }
  | ~ = assign_defn; { [assign_defn] }

let assign_defn :=
  | ASSIGN; ~ = param; "."; { param }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
