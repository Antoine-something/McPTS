%{

From Coq Require Import List String.

From McPTS.CaseStudies.MiniML Require Import Frontend.

Parameter loc : Type.

Arguments eq_refl {_} _.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO LET IN (* keywords *)
%token <loc> ARROW "->" BAR "|" COLON ":" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" DOT "." EOF DEF ":=" (* symbols *)

%start <Cst.obj * Cst.obj> prog
%type <Cst.obj> obj app_obj atomic_obj
%type <Cst.obj * Cst.obj> ann_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params
%type <list ((string * Cst.obj) * Cst.obj)> let_defns
%type <(string * Cst.obj) * Cst.obj> let_defn

%on_error_reduce obj params app_obj atomic_obj

%%

let prog :=
  exp = obj; ":"; ty = obj; EOF; <>

let obj :=
  | PI; ~ = params; "->"; ~ = obj; { List.fold_left (fun acc arg => Cst.pi (fst arg) (snd arg) acc) params obj }
  | LAMBDA; ~ = params; "->"; ~ = ann_obj; { 
    fst (
      List.fold_left (
        fun acc arg => (
          Cst.fn (fst arg) (snd arg) (snd acc) (fst acc),
          Cst.pi (fst arg) (snd arg) (snd acc) 
        ) 
      ) params ann_obj
    )}
  | ~ = app_obj; <>
  | REC; escr = obj; RETURN; mx = VAR; "."; em = obj;
    "|"; ZERO; "=>"; ez = obj;
    "|"; SUCC; sx = VAR; ","; sr = VAR; "=>"; es = obj;
    END; { Cst.natrec escr (snd mx) em ez (snd sx) (snd sr) es }

  | SUCC; ~ = atomic_obj; { Cst.succ atomic_obj }

  | LET; ds = let_defns; IN; body = ann_obj; { 
    List.fold_left (fun acc arg => Cst.app acc (snd arg)) 
    (List.rev ds) 
    (
      fst (
        List.fold_left (
          fun acc arg => (
            Cst.fn (fst (fst arg)) (snd (fst arg)) (snd acc) (fst acc),
            Cst.pi (fst (fst arg)) (snd (fst arg)) (snd acc) 
          ) 
        ) ds body
      )
    ) 
  }

let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | TYPE; { Cst.st }

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


(* Reversed nonempty list of definitions *)
let let_defns :=
  | ~ = let_defns; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

(* (x : A) := t *)
let let_defn :=
  | "("; ~ = param; ":="; ~ = obj; ")"; { (param, obj) }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
