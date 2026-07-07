open Alphabet
open Datatypes
open Frontend
open Grammar
open List
open Main
open Nat
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type loc = Lexing.position * Lexing.position

module Coq__1 = struct
 type token =
 | ZERO of loc
 | VAR of (loc * string)
 | TYPE of loc
 | SUCC of loc
 | RPAREN of loc
 | RETURN of loc
 | REC of loc
 | PI of loc
 | NAT of loc
 | LPAREN of loc
 | LET of loc
 | LAMBDA of loc
 | KIND of loc
 | INT of (loc * int)
 | IN of loc
 | EOF of loc
 | END of loc
 | DOT of loc
 | DEF of loc
 | DARROW of loc
 | COMMA of loc
 | COLON of loc
 | BAR of loc
 | ARROW of loc
end
include Coq__1

module Gram =
 struct
  type terminal' =
  | ARROW't
  | BAR't
  | COLON't
  | COMMA't
  | DARROW't
  | DEF't
  | DOT't
  | END't
  | EOF't
  | IN't
  | INT't
  | KIND't
  | LAMBDA't
  | LET't
  | LPAREN't
  | NAT't
  | PI't
  | REC't
  | RETURN't
  | RPAREN't
  | SUCC't
  | TYPE't
  | VAR't
  | ZERO't

  type terminal = terminal'

  (** val terminalNum : terminal coq_Numbered **)

  let terminalNum =
    { inj = (fun x ->
      match x with
      | ARROW't -> 1
      | BAR't -> (fun p->2*p) 1
      | COLON't -> (fun p->1+2*p) 1
      | COMMA't -> (fun p->2*p) ((fun p->2*p) 1)
      | DARROW't -> (fun p->1+2*p) ((fun p->2*p) 1)
      | DEF't -> (fun p->2*p) ((fun p->1+2*p) 1)
      | DOT't -> (fun p->1+2*p) ((fun p->1+2*p) 1)
      | END't -> (fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | EOF't -> (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | IN't -> (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))
      | INT't -> (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))
      | KIND't -> (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))
      | LAMBDA't -> (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))
      | LET't -> (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))
      | LPAREN't -> (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))
      | NAT't -> (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | PI't -> (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | REC't -> (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | RETURN't ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | RPAREN't ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | SUCC't ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | TYPE't ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | VAR't ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | ZERO't ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))));
      surj = (fun n ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> VAR't)
                p2)
              (fun _ -> LPAREN't)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> RETURN't)
                p2)
              (fun _ -> INT't)
              p1)
            (fun _ -> DOT't)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> SUCC't)
                p2)
              (fun _ -> LAMBDA't)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> PI't)
                p2)
              (fun _ -> EOF't)
              p1)
            (fun _ -> DARROW't)
            p0)
          (fun _ -> COLON't)
          p)
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> TYPE't)
                p2)
              (fun _ -> LET't)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> REC't)
                p2)
              (fun _ -> IN't)
              p1)
            (fun _ -> DEF't)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> ARROW't)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> RPAREN't)
                p2)
              (fun _ -> KIND't)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> ZERO't)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> ARROW't)
                (fun _ -> ARROW't)
                (fun _ -> NAT't)
                p2)
              (fun _ -> END't)
              p1)
            (fun _ -> COMMA't)
            p0)
          (fun _ -> BAR't)
          p)
        (fun _ -> ARROW't)
        n); inj_bound = ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1)))) }

  (** val coq_TerminalAlph : terminal coq_Alphabet **)

  let coq_TerminalAlph =
    coq_NumberedAlphabet terminalNum

  type nonterminal' =
  | Coq_ann_obj'nt
  | Coq_app_obj'nt
  | Coq_atomic_obj'nt
  | Coq_let_defn'nt
  | Coq_obj'nt
  | Coq_param'nt
  | Coq_params'nt
  | Coq_prog'nt
  | Coq_sort'nt

  type nonterminal = nonterminal'

  (** val nonterminalNum : nonterminal coq_Numbered **)

  let nonterminalNum =
    { inj = (fun x ->
      match x with
      | Coq_ann_obj'nt -> 1
      | Coq_app_obj'nt -> (fun p->2*p) 1
      | Coq_atomic_obj'nt -> (fun p->1+2*p) 1
      | Coq_let_defn'nt -> (fun p->2*p) ((fun p->2*p) 1)
      | Coq_obj'nt -> (fun p->1+2*p) ((fun p->2*p) 1)
      | Coq_param'nt -> (fun p->2*p) ((fun p->1+2*p) 1)
      | Coq_params'nt -> (fun p->1+2*p) ((fun p->1+2*p) 1)
      | Coq_prog'nt -> (fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | Coq_sort'nt -> (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)));
      surj = (fun n ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> Coq_ann_obj'nt)
            (fun _ -> Coq_ann_obj'nt)
            (fun _ -> Coq_params'nt)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> Coq_ann_obj'nt)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Coq_ann_obj'nt)
              (fun _ -> Coq_ann_obj'nt)
              (fun _ -> Coq_sort'nt)
              p1)
            (fun _ -> Coq_obj'nt)
            p0)
          (fun _ -> Coq_atomic_obj'nt)
          p)
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> Coq_ann_obj'nt)
            (fun _ -> Coq_ann_obj'nt)
            (fun _ -> Coq_param'nt)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> Coq_ann_obj'nt)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Coq_ann_obj'nt)
              (fun _ -> Coq_ann_obj'nt)
              (fun _ -> Coq_prog'nt)
              p1)
            (fun _ -> Coq_let_defn'nt)
            p0)
          (fun _ -> Coq_app_obj'nt)
          p)
        (fun _ -> Coq_ann_obj'nt)
        n); inj_bound = ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))) }

  (** val coq_NonTerminalAlph : nonterminal coq_Alphabet **)

  let coq_NonTerminalAlph =
    coq_NumberedAlphabet nonterminalNum

  type symbol =
  | T of terminal
  | NT of nonterminal

  (** val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)

  let symbol_rect f f0 = function
  | T t0 -> f t0
  | NT n -> f0 n

  (** val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)

  let symbol_rec f f0 = function
  | T t0 -> f t0
  | NT n -> f0 n

  (** val coq_SymbolAlph : symbol coq_Alphabet **)

  let coq_SymbolAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | T x0 ->
        (match y with
         | T y0 -> coq_TerminalAlph.coq_AlphabetComparable x0 y0
         | NT _ -> Gt)
      | NT x0 ->
        (match y with
         | T _ -> Lt
         | NT y0 -> coq_NonTerminalAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (app (map (fun x -> T x) coq_TerminalAlph.coq_AlphabetFinite)
        (map (fun x -> NT x) coq_NonTerminalAlph.coq_AlphabetFinite)) }

  type terminal_semantic_type = __

  type nonterminal_semantic_type = __

  type symbol_semantic_type = __

  type token = Coq__1.token

  (** val token_term : token -> terminal **)

  let token_term = function
  | ZERO _ -> ZERO't
  | VAR _ -> VAR't
  | TYPE _ -> TYPE't
  | SUCC _ -> SUCC't
  | RPAREN _ -> RPAREN't
  | RETURN _ -> RETURN't
  | REC _ -> REC't
  | PI _ -> PI't
  | NAT _ -> NAT't
  | LPAREN _ -> LPAREN't
  | LET _ -> LET't
  | LAMBDA _ -> LAMBDA't
  | KIND _ -> KIND't
  | INT _ -> INT't
  | IN _ -> IN't
  | EOF _ -> EOF't
  | END _ -> END't
  | DOT _ -> DOT't
  | DEF _ -> DEF't
  | DARROW _ -> DARROW't
  | COMMA _ -> COMMA't
  | COLON _ -> COLON't
  | BAR _ -> BAR't
  | ARROW _ -> ARROW't

  (** val token_sem : token -> symbol_semantic_type **)

  let token_sem = function
  | ZERO x -> Obj.magic x
  | VAR x -> Obj.magic x
  | TYPE x -> Obj.magic x
  | SUCC x -> Obj.magic x
  | RPAREN x -> Obj.magic x
  | RETURN x -> Obj.magic x
  | REC x -> Obj.magic x
  | PI x -> Obj.magic x
  | NAT x -> Obj.magic x
  | LPAREN x -> Obj.magic x
  | LET x -> Obj.magic x
  | LAMBDA x -> Obj.magic x
  | KIND x -> Obj.magic x
  | INT x -> Obj.magic x
  | IN x -> Obj.magic x
  | EOF x -> Obj.magic x
  | END x -> Obj.magic x
  | DOT x -> Obj.magic x
  | DEF x -> Obj.magic x
  | DARROW x -> Obj.magic x
  | COMMA x -> Obj.magic x
  | COLON x -> Obj.magic x
  | BAR x -> Obj.magic x
  | ARROW x -> Obj.magic x

  type production' =
  | Prod'sort'1
  | Prod'sort'0
  | Prod'prog'0
  | Prod'params'1
  | Prod'params'0
  | Prod'param'0
  | Prod'obj'5
  | Prod'obj'4
  | Prod'obj'3
  | Prod'obj'2
  | Prod'obj'1
  | Prod'obj'0
  | Prod'let_defn'0
  | Prod'atomic_obj'5
  | Prod'atomic_obj'4
  | Prod'atomic_obj'3
  | Prod'atomic_obj'2
  | Prod'atomic_obj'1
  | Prod'atomic_obj'0
  | Prod'app_obj'1
  | Prod'app_obj'0
  | Prod'ann_obj'0

  type production = production'

  (** val productionNum : production coq_Numbered **)

  let productionNum =
    { inj = (fun x ->
      match x with
      | Prod'sort'1 -> 1
      | Prod'sort'0 -> (fun p->2*p) 1
      | Prod'prog'0 -> (fun p->1+2*p) 1
      | Prod'params'1 -> (fun p->2*p) ((fun p->2*p) 1)
      | Prod'params'0 -> (fun p->1+2*p) ((fun p->2*p) 1)
      | Prod'param'0 -> (fun p->2*p) ((fun p->1+2*p) 1)
      | Prod'obj'5 -> (fun p->1+2*p) ((fun p->1+2*p) 1)
      | Prod'obj'4 -> (fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | Prod'obj'3 -> (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | Prod'obj'2 -> (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))
      | Prod'obj'1 -> (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))
      | Prod'obj'0 -> (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))
      | Prod'let_defn'0 -> (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))
      | Prod'atomic_obj'5 -> (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))
      | Prod'atomic_obj'4 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))
      | Prod'atomic_obj'3 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Prod'atomic_obj'2 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Prod'atomic_obj'1 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Prod'atomic_obj'0 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Prod'app_obj'1 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | Prod'app_obj'0 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | Prod'ann_obj'0 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))));
      surj = (fun n ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun _ -> Prod'sort'1)
              (fun _ -> Prod'atomic_obj'4)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'atomic_obj'0)
                p2)
              (fun _ -> Prod'obj'1)
              p1)
            (fun _ -> Prod'obj'5)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'app_obj'0)
                p2)
              (fun _ -> Prod'let_defn'0)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'atomic_obj'2)
                p2)
              (fun _ -> Prod'obj'3)
              p1)
            (fun _ -> Prod'params'0)
            p0)
          (fun _ -> Prod'prog'0)
          p)
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'ann_obj'0)
                p2)
              (fun _ -> Prod'atomic_obj'5)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'atomic_obj'1)
                p2)
              (fun _ -> Prod'obj'2)
              p1)
            (fun _ -> Prod'param'0)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'app_obj'1)
                p2)
              (fun _ -> Prod'obj'0)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun _ -> Prod'sort'1)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'sort'1)
                (fun _ -> Prod'atomic_obj'3)
                p2)
              (fun _ -> Prod'obj'4)
              p1)
            (fun _ -> Prod'params'1)
            p0)
          (fun _ -> Prod'sort'0)
          p)
        (fun _ -> Prod'sort'1)
        n); inj_bound = ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->2*p) 1)))) }

  (** val coq_ProductionAlph : production coq_Alphabet **)

  let coq_ProductionAlph =
    coq_NumberedAlphabet productionNum

  (** val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT **)

  let prod_contents = function
  | Prod'sort'1 ->
    Obj.magic (Coq_existT ((Obj.magic (Coq_sort'nt, ((T KIND't) :: []))),
      (Obj.magic (fun _ -> Cst.Coq_s_knd))))
  | Prod'sort'0 ->
    Obj.magic (Coq_existT ((Obj.magic (Coq_sort'nt, ((T TYPE't) :: []))),
      (Obj.magic (fun _ -> Cst.Coq_s_typ))))
  | Prod'prog'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_prog'nt, ((T EOF't) :: ((NT Coq_obj'nt) :: ((T
         COLON't) :: ((NT Coq_obj'nt) :: [])))))),
      (Obj.magic (fun _ ty _ exp -> (exp, ty)))))
  | Prod'params'1 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_params'nt, ((NT Coq_param'nt) :: []))),
      (Obj.magic (fun param -> param :: []))))
  | Prod'params'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_params'nt, ((NT Coq_param'nt) :: ((NT
         Coq_params'nt) :: [])))),
      (Obj.magic (fun param params -> param :: params))))
  | Prod'param'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_param'nt, ((T RPAREN't) :: ((NT Coq_obj'nt) :: ((T
         COLON't) :: ((T VAR't) :: ((T LPAREN't) :: []))))))),
      (Obj.magic (fun _ obj0 _ x _ -> ((snd x), obj0)))))
  | Prod'obj'5 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_obj'nt, ((NT Coq_ann_obj'nt) :: ((T IN't) :: ((NT
         Coq_let_defn'nt) :: ((T LET't) :: [])))))),
      (Obj.magic (fun body _ ds _ -> Cst.Coq_app ((Cst.Coq_fn
        ((fst (fst (fst ds))), (snd ds), (snd (fst (fst ds))), (snd body),
        (fst body))), (snd (fst ds)))))))
  | Prod'obj'4 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_obj'nt, ((NT Coq_atomic_obj'nt) :: ((T
         SUCC't) :: [])))),
      (Obj.magic (fun atomic_obj _ -> Cst.Coq_succ atomic_obj))))
  | Prod'obj'3 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_obj'nt, ((T END't) :: ((NT Coq_obj'nt) :: ((T
         DARROW't) :: ((T VAR't) :: ((T COMMA't) :: ((T VAR't) :: ((T
         SUCC't) :: ((T BAR't) :: ((NT Coq_obj'nt) :: ((T DARROW't) :: ((T
         ZERO't) :: ((T BAR't) :: ((NT Coq_obj'nt) :: ((T DOT't) :: ((T
         VAR't) :: ((T RETURN't) :: ((NT Coq_obj'nt) :: ((T
         REC't) :: [])))))))))))))))))))),
      (Obj.magic (fun _ es _ sr _ sx _ _ ez _ _ _ em _ mx _ escr _ ->
        Cst.Coq_natrec (escr, (snd mx), em, ez, (snd sx), (snd sr), es)))))
  | Prod'obj'2 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_obj'nt, ((NT Coq_app_obj'nt) :: []))),
      (Obj.magic (fun app_obj -> app_obj))))
  | Prod'obj'1 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_obj'nt, ((NT Coq_ann_obj'nt) :: ((T ARROW't) :: ((NT
         Coq_sort'nt) :: ((T COLON't) :: ((NT Coq_param'nt) :: ((T
         LAMBDA't) :: [])))))))),
      (Obj.magic (fun ann_obj _ s _ param _ -> Cst.Coq_fn ((fst param), s,
        (snd param), (snd ann_obj), (fst ann_obj))))))
  | Prod'obj'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_obj'nt, ((NT Coq_obj'nt) :: ((T ARROW't) :: ((NT
         Coq_sort'nt) :: ((T COLON't) :: ((NT Coq_params'nt) :: ((T
         PI't) :: [])))))))),
      (Obj.magic (fun obj0 _ s _ params _ ->
        fold_left (fun acc arg -> Cst.Coq_pi ((fst arg), s, (snd arg), acc))
          params obj0))))
  | Prod'let_defn'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_let_defn'nt, ((NT Coq_obj'nt) :: ((T DEF't) :: ((NT
         Coq_sort'nt) :: ((T COLON't) :: ((NT Coq_param'nt) :: []))))))),
      (Obj.magic (fun obj0 _ s _ param -> ((param, obj0), s)))))
  | Prod'atomic_obj'5 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_atomic_obj'nt, ((T RPAREN't) :: ((NT
         Coq_obj'nt) :: ((T LPAREN't) :: []))))),
      (Obj.magic (fun _ obj0 _ -> obj0))))
  | Prod'atomic_obj'4 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_atomic_obj'nt, ((T VAR't) :: []))),
      (Obj.magic (fun x -> Cst.Coq_var (snd x)))))
  | Prod'atomic_obj'3 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_atomic_obj'nt, ((T INT't) :: []))),
      (Obj.magic (fun n ->
        let rec f n0 =
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Cst.Coq_zero)
            (fun n1 -> Cst.Coq_succ (f n1))
            n0
        in f (snd n)))))
  | Prod'atomic_obj'2 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_atomic_obj'nt, ((T ZERO't) :: []))),
      (Obj.magic (fun _ -> Cst.Coq_zero))))
  | Prod'atomic_obj'1 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_atomic_obj'nt, ((T NAT't) :: []))),
      (Obj.magic (fun _ -> Cst.Coq_nat))))
  | Prod'atomic_obj'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_atomic_obj'nt, ((NT Coq_sort'nt) :: []))),
      (Obj.magic (fun sort -> sort))))
  | Prod'app_obj'1 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_app_obj'nt, ((NT Coq_atomic_obj'nt) :: []))),
      (Obj.magic (fun atomic_obj -> atomic_obj))))
  | Prod'app_obj'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_app_obj'nt, ((NT Coq_atomic_obj'nt) :: ((NT
         Coq_app_obj'nt) :: [])))),
      (Obj.magic (fun atomic_obj app_obj -> Cst.Coq_app (app_obj,
        atomic_obj)))))
  | Prod'ann_obj'0 ->
    Obj.magic (Coq_existT
      ((Obj.magic (Coq_ann_obj'nt, ((T RPAREN't) :: ((NT Coq_obj'nt) :: ((T
         COLON't) :: ((NT Coq_obj'nt) :: ((T LPAREN't) :: []))))))),
      (Obj.magic (fun _ ann _ exp _ -> (exp, ann)))))

  (** val prod_lhs : production -> nonterminal **)

  let prod_lhs p =
    fst (projT1 (prod_contents p))

  (** val prod_rhs_rev : production -> symbol list **)

  let prod_rhs_rev p =
    snd (projT1 (prod_contents p))

  (** val prod_action : production -> symbol_semantic_type arrows_right **)

  let prod_action p =
    projT2 (prod_contents p)

  type parse_tree =
  | Terminal_pt of token
  | Non_terminal_pt of production * token list * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of symbol list * token list * parse_tree_list * symbol
     * token list * parse_tree

  (** val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1 **)

  let parse_tree_rect f f0 _ _ = function
  | Terminal_pt tok -> f tok
  | Non_terminal_pt (prod, word, p0) -> f0 prod word p0

  (** val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1 **)

  let parse_tree_rec f f0 _ _ = function
  | Terminal_pt tok -> f tok
  | Non_terminal_pt (prod, word, p0) -> f0 prod word p0

  (** val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1 **)

  let rec parse_tree_list_rect f f0 _ _ = function
  | Nil_ptl -> f
  | Cons_ptl (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0
      (parse_tree_list_rect f f0 head_symbolsq wordq p0) head_symbolt wordt p1

  (** val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1 **)

  let rec parse_tree_list_rec f f0 _ _ = function
  | Nil_ptl -> f
  | Cons_ptl (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0
      (parse_tree_list_rec f f0 head_symbolsq wordq p0) head_symbolt wordt p1

  (** val pt_sem :
      symbol -> token list -> parse_tree -> symbol_semantic_type **)

  let rec pt_sem _ _ = function
  | Terminal_pt tok -> token_sem tok
  | Non_terminal_pt (prod, word0, ptl) ->
    Obj.magic ptl_sem (prod_rhs_rev prod) word0 ptl (prod_action prod)

  (** val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1 **)

  and ptl_sem _ _ tree0 act =
    match tree0 with
    | Nil_ptl -> Obj.magic act
    | Cons_ptl (head_symbolsq, wordq, q, head_symbolt, wordt, t0) ->
      ptl_sem head_symbolsq wordq q
        (Obj.magic act (pt_sem head_symbolt wordt t0))

  (** val pt_size : symbol -> token list -> parse_tree -> int **)

  let rec pt_size _ _ = function
  | Terminal_pt _ -> Stdlib.Int.succ 0
  | Non_terminal_pt (prod, word0, l) ->
    Stdlib.Int.succ (ptl_size (prod_rhs_rev prod) word0 l)

  (** val ptl_size : symbol list -> token list -> parse_tree_list -> int **)

  and ptl_size _ _ = function
  | Nil_ptl -> 0
  | Cons_ptl (head_symbolsq, wordq, q, head_symbolt, wordt, t0) ->
    add (pt_size head_symbolt wordt t0) (ptl_size head_symbolsq wordq q)
 end
module Coq__2 = Gram

module Aut =
 struct
  module Gram = Gram

  module GramDefs = Gram

  (** val nullable_nterm : Coq__2.nonterminal -> bool **)

  let nullable_nterm _ =
    false

  (** val first_nterm : Coq__2.nonterminal -> Coq__2.terminal list **)

  let first_nterm = function
  | Coq__2.Coq_app_obj'nt ->
    Coq__2.ZERO't :: (Coq__2.VAR't :: (Coq__2.TYPE't :: (Coq__2.NAT't :: (Coq__2.LPAREN't :: (Coq__2.KIND't :: (Coq__2.INT't :: []))))))
  | Coq__2.Coq_atomic_obj'nt ->
    Coq__2.ZERO't :: (Coq__2.VAR't :: (Coq__2.TYPE't :: (Coq__2.NAT't :: (Coq__2.LPAREN't :: (Coq__2.KIND't :: (Coq__2.INT't :: []))))))
  | Coq__2.Coq_obj'nt ->
    Coq__2.ZERO't :: (Coq__2.VAR't :: (Coq__2.TYPE't :: (Coq__2.SUCC't :: (Coq__2.REC't :: (Coq__2.PI't :: (Coq__2.NAT't :: (Coq__2.LPAREN't :: (Coq__2.LET't :: (Coq__2.LAMBDA't :: (Coq__2.KIND't :: (Coq__2.INT't :: [])))))))))))
  | Coq__2.Coq_prog'nt ->
    Coq__2.ZERO't :: (Coq__2.VAR't :: (Coq__2.TYPE't :: (Coq__2.SUCC't :: (Coq__2.REC't :: (Coq__2.PI't :: (Coq__2.NAT't :: (Coq__2.LPAREN't :: (Coq__2.LET't :: (Coq__2.LAMBDA't :: (Coq__2.KIND't :: (Coq__2.INT't :: [])))))))))))
  | Coq__2.Coq_sort'nt -> Coq__2.TYPE't :: (Coq__2.KIND't :: [])
  | _ -> Coq__2.LPAREN't :: []

  type noninitstate' =
  | Nis'71
  | Nis'70
  | Nis'69
  | Nis'68
  | Nis'66
  | Nis'65
  | Nis'64
  | Nis'63
  | Nis'62
  | Nis'61
  | Nis'60
  | Nis'59
  | Nis'58
  | Nis'57
  | Nis'56
  | Nis'55
  | Nis'54
  | Nis'53
  | Nis'52
  | Nis'51
  | Nis'50
  | Nis'49
  | Nis'48
  | Nis'47
  | Nis'46
  | Nis'45
  | Nis'44
  | Nis'43
  | Nis'42
  | Nis'41
  | Nis'40
  | Nis'39
  | Nis'38
  | Nis'37
  | Nis'36
  | Nis'35
  | Nis'34
  | Nis'33
  | Nis'32
  | Nis'31
  | Nis'30
  | Nis'29
  | Nis'28
  | Nis'27
  | Nis'26
  | Nis'25
  | Nis'24
  | Nis'23
  | Nis'22
  | Nis'21
  | Nis'20
  | Nis'19
  | Nis'18
  | Nis'17
  | Nis'16
  | Nis'15
  | Nis'14
  | Nis'13
  | Nis'12
  | Nis'11
  | Nis'10
  | Nis'9
  | Nis'8
  | Nis'7
  | Nis'6
  | Nis'5
  | Nis'4
  | Nis'3
  | Nis'2
  | Nis'1

  type noninitstate = noninitstate'

  (** val noninitstateNum : noninitstate coq_Numbered **)

  let noninitstateNum =
    { inj = (fun x ->
      match x with
      | Nis'71 -> 1
      | Nis'70 -> (fun p->2*p) 1
      | Nis'69 -> (fun p->1+2*p) 1
      | Nis'68 -> (fun p->2*p) ((fun p->2*p) 1)
      | Nis'66 -> (fun p->1+2*p) ((fun p->2*p) 1)
      | Nis'65 -> (fun p->2*p) ((fun p->1+2*p) 1)
      | Nis'64 -> (fun p->1+2*p) ((fun p->1+2*p) 1)
      | Nis'63 -> (fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | Nis'62 -> (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))
      | Nis'61 -> (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))
      | Nis'60 -> (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))
      | Nis'59 -> (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))
      | Nis'58 -> (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))
      | Nis'57 -> (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))
      | Nis'56 -> (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))
      | Nis'55 -> (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Nis'54 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Nis'53 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Nis'52 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
      | Nis'51 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | Nis'50 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | Nis'49 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | Nis'48 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
      | Nis'47 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
      | Nis'46 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
      | Nis'45 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
      | Nis'44 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
      | Nis'43 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
      | Nis'42 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
      | Nis'41 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
      | Nis'40 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
      | Nis'39 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          1))))
      | Nis'38 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'37 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'36 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'35 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'34 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'33 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'32 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
      | Nis'31 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'30 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'29 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'28 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'27 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'26 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'25 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'24 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))
      | Nis'23 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'22 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'21 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'20 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'19 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'18 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'17 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'16 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1))))
      | Nis'15 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'14 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'13 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'12 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'11 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'10 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'9 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'8 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))
      | Nis'7 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1)))))
      | Nis'6 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))
      | Nis'5 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))
      | Nis'4 ->
        (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))
      | Nis'3 ->
        (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))
      | Nis'2 ->
        (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))
      | Nis'1 ->
        (fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))); surj = (fun n ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'8)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'24)
                  p3)
                (fun _ -> Nis'40)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'16)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'32)
                  p3)
                (fun _ -> Nis'48)
                p2)
              (fun _ -> Nis'56)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'12)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'28)
                  p3)
                (fun _ -> Nis'44)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'20)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'4)
                    p4)
                  (fun _ -> Nis'36)
                  p3)
                (fun _ -> Nis'52)
                p2)
              (fun _ -> Nis'60)
              p1)
            (fun _ -> Nis'64)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'10)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'26)
                  p3)
                (fun _ -> Nis'42)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'18)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'2)
                    p4)
                  (fun _ -> Nis'34)
                  p3)
                (fun _ -> Nis'50)
                p2)
              (fun _ -> Nis'58)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'14)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'30)
                  p3)
                (fun _ -> Nis'46)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'22)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'6)
                    p4)
                  (fun _ -> Nis'38)
                  p3)
                (fun _ -> Nis'54)
                p2)
              (fun _ -> Nis'62)
              p1)
            (fun _ -> Nis'66)
            p0)
          (fun _ -> Nis'69)
          p)
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'9)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'25)
                  p3)
                (fun _ -> Nis'41)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'17)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'1)
                    p4)
                  (fun _ -> Nis'33)
                  p3)
                (fun _ -> Nis'49)
                p2)
              (fun _ -> Nis'57)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'13)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'29)
                  p3)
                (fun _ -> Nis'45)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'21)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'5)
                    p4)
                  (fun _ -> Nis'37)
                  p3)
                (fun _ -> Nis'53)
                p2)
              (fun _ -> Nis'61)
              p1)
            (fun _ -> Nis'65)
            p0)
          (fun p0 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'11)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'27)
                  p3)
                (fun _ -> Nis'43)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'19)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'3)
                    p4)
                  (fun _ -> Nis'35)
                  p3)
                (fun _ -> Nis'51)
                p2)
              (fun _ -> Nis'59)
              p1)
            (fun p1 ->
            (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'15)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'31)
                  p3)
                (fun _ -> Nis'47)
                p2)
              (fun p2 ->
              (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'71)
                  (fun _ -> Nis'23)
                  p3)
                (fun p3 ->
                (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                  (fun _ -> Nis'71)
                  (fun p4 ->
                  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'71)
                    (fun _ -> Nis'7)
                    p4)
                  (fun _ -> Nis'39)
                  p3)
                (fun _ -> Nis'55)
                p2)
              (fun _ -> Nis'63)
              p1)
            (fun _ -> Nis'68)
            p0)
          (fun _ -> Nis'70)
          p)
        (fun _ -> Nis'71)
        n); inj_bound = ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))) }

  (** val coq_NonInitStateAlph : noninitstate coq_Alphabet **)

  let coq_NonInitStateAlph =
    coq_NumberedAlphabet noninitstateNum

  (** val last_symb_of_non_init_state : noninitstate -> Coq__2.symbol **)

  let last_symb_of_non_init_state = function
  | Nis'71 -> Coq__2.T Coq__2.EOF't
  | Nis'69 -> Coq__2.T Coq__2.COLON't
  | Nis'66 -> Coq__2.NT Coq__2.Coq_atomic_obj'nt
  | Nis'65 -> Coq__2.T Coq__2.RPAREN't
  | Nis'63 -> Coq__2.T Coq__2.END't
  | Nis'61 -> Coq__2.T Coq__2.DARROW't
  | Nis'60 -> Coq__2.T Coq__2.VAR't
  | Nis'59 -> Coq__2.T Coq__2.COMMA't
  | Nis'58 -> Coq__2.T Coq__2.VAR't
  | Nis'57 -> Coq__2.T Coq__2.SUCC't
  | Nis'56 -> Coq__2.T Coq__2.BAR't
  | Nis'54 -> Coq__2.T Coq__2.DARROW't
  | Nis'53 -> Coq__2.T Coq__2.ZERO't
  | Nis'52 -> Coq__2.T Coq__2.BAR't
  | Nis'50 -> Coq__2.T Coq__2.DOT't
  | Nis'49 -> Coq__2.T Coq__2.VAR't
  | Nis'48 -> Coq__2.T Coq__2.RETURN't
  | Nis'46 -> Coq__2.NT Coq__2.Coq_param'nt
  | Nis'45 -> Coq__2.NT Coq__2.Coq_param'nt
  | Nis'43 -> Coq__2.T Coq__2.ARROW't
  | Nis'42 -> Coq__2.NT Coq__2.Coq_sort'nt
  | Nis'41 -> Coq__2.T Coq__2.COLON't
  | Nis'40 -> Coq__2.NT Coq__2.Coq_params'nt
  | Nis'39 -> Coq__2.T Coq__2.RPAREN't
  | Nis'37 -> Coq__2.NT Coq__2.Coq_ann_obj'nt
  | Nis'36 -> Coq__2.T Coq__2.IN't
  | Nis'35 -> Coq__2.NT Coq__2.Coq_let_defn'nt
  | Nis'33 -> Coq__2.NT Coq__2.Coq_ann_obj'nt
  | Nis'32 -> Coq__2.NT Coq__2.Coq_atomic_obj'nt
  | Nis'31 -> Coq__2.NT Coq__2.Coq_app_obj'nt
  | Nis'30 -> Coq__2.NT Coq__2.Coq_atomic_obj'nt
  | Nis'29 -> Coq__2.T Coq__2.RPAREN't
  | Nis'27 -> Coq__2.T Coq__2.COLON't
  | Nis'25 -> Coq__2.NT Coq__2.Coq_sort'nt
  | Nis'24 -> Coq__2.T Coq__2.INT't
  | Nis'23 -> Coq__2.T Coq__2.LPAREN't
  | Nis'22 -> Coq__2.T Coq__2.ARROW't
  | Nis'21 -> Coq__2.NT Coq__2.Coq_sort'nt
  | Nis'20 -> Coq__2.T Coq__2.COLON't
  | Nis'19 -> Coq__2.NT Coq__2.Coq_param'nt
  | Nis'18 -> Coq__2.T Coq__2.LAMBDA't
  | Nis'17 -> Coq__2.T Coq__2.DEF't
  | Nis'16 -> Coq__2.NT Coq__2.Coq_sort'nt
  | Nis'15 -> Coq__2.T Coq__2.KIND't
  | Nis'14 -> Coq__2.T Coq__2.COLON't
  | Nis'13 -> Coq__2.NT Coq__2.Coq_param'nt
  | Nis'12 -> Coq__2.T Coq__2.LET't
  | Nis'11 -> Coq__2.T Coq__2.COLON't
  | Nis'10 -> Coq__2.T Coq__2.VAR't
  | Nis'9 -> Coq__2.T Coq__2.LPAREN't
  | Nis'8 -> Coq__2.T Coq__2.PI't
  | Nis'7 -> Coq__2.T Coq__2.REC't
  | Nis'6 -> Coq__2.T Coq__2.LPAREN't
  | Nis'5 -> Coq__2.T Coq__2.NAT't
  | Nis'4 -> Coq__2.T Coq__2.SUCC't
  | Nis'3 -> Coq__2.T Coq__2.TYPE't
  | Nis'2 -> Coq__2.T Coq__2.VAR't
  | Nis'1 -> Coq__2.T Coq__2.ZERO't
  | _ -> Coq__2.NT Coq__2.Coq_obj'nt

  type initstate' =
  | Init'0

  type initstate = initstate'

  (** val initstateNum : initstate coq_Numbered **)

  let initstateNum =
    { inj = (fun _ -> 1); surj = (fun n ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Init'0)
        (fun _ -> Init'0)
        (fun _ -> Init'0)
        n); inj_bound = 1 }

  (** val coq_InitStateAlph : initstate coq_Alphabet **)

  let coq_InitStateAlph =
    coq_NumberedAlphabet initstateNum

  type state =
  | Init of initstate
  | Ninit of noninitstate

  (** val state_rect :
      (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1 **)

  let state_rect f f0 = function
  | Init i -> f i
  | Ninit n -> f0 n

  (** val state_rec :
      (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1 **)

  let state_rec f f0 = function
  | Init i -> f i
  | Ninit n -> f0 n

  (** val coq_StateAlph : state coq_Alphabet **)

  let coq_StateAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | Init x0 ->
        (match y with
         | Init y0 -> coq_InitStateAlph.coq_AlphabetComparable x0 y0
         | Ninit _ -> Lt)
      | Ninit x0 ->
        (match y with
         | Init _ -> Gt
         | Ninit y0 -> coq_NonInitStateAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (app (map (fun x -> Init x) coq_InitStateAlph.coq_AlphabetFinite)
        (map (fun x -> Ninit x) coq_NonInitStateAlph.coq_AlphabetFinite)) }

  type lookahead_action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act

  (** val lookahead_action_rect :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> lookahead_action -> 'a1 **)

  let lookahead_action_rect _ f f0 f1 = function
  | Shift_act s -> f s __
  | Reduce_act p -> f0 p
  | Fail_act -> f1

  (** val lookahead_action_rec :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> lookahead_action -> 'a1 **)

  let lookahead_action_rec _ f f0 f1 = function
  | Shift_act s -> f s __
  | Reduce_act p -> f0 p
  | Fail_act -> f1

  type action =
  | Default_reduce_act of Gram.production
  | Lookahead_act of (Gram.terminal -> lookahead_action)

  (** val action_rect :
      (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) ->
      'a1) -> action -> 'a1 **)

  let action_rect f f0 = function
  | Default_reduce_act p -> f p
  | Lookahead_act l -> f0 l

  (** val action_rec :
      (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) ->
      'a1) -> action -> 'a1 **)

  let action_rec f f0 = function
  | Default_reduce_act p -> f p
  | Lookahead_act l -> f0 l

  type item = { prod_item : Gram.production; dot_pos_item : int;
                lookaheads_item : Gram.terminal list }

  (** val prod_item : item -> Gram.production **)

  let prod_item i =
    i.prod_item

  (** val dot_pos_item : item -> int **)

  let dot_pos_item i =
    i.dot_pos_item

  (** val lookaheads_item : item -> Gram.terminal list **)

  let lookaheads_item i =
    i.lookaheads_item

  (** val start_nt : initstate -> Coq__2.nonterminal **)

  let start_nt _ =
    Coq__2.Coq_prog'nt

  (** val action_table : state -> action **)

  let action_table = function
  | Init _ ->
    Lookahead_act (fun terminal0 ->
      match terminal0 with
      | Coq__2.INT't -> Shift_act Nis'24
      | Coq__2.KIND't -> Shift_act Nis'15
      | Coq__2.LAMBDA't -> Shift_act Nis'18
      | Coq__2.LET't -> Shift_act Nis'12
      | Coq__2.LPAREN't -> Shift_act Nis'6
      | Coq__2.NAT't -> Shift_act Nis'5
      | Coq__2.PI't -> Shift_act Nis'8
      | Coq__2.REC't -> Shift_act Nis'7
      | Coq__2.SUCC't -> Shift_act Nis'4
      | Coq__2.TYPE't -> Shift_act Nis'3
      | Coq__2.VAR't -> Shift_act Nis'2
      | Coq__2.ZERO't -> Shift_act Nis'1
      | _ -> Fail_act)
  | Ninit n ->
    (match n with
     | Nis'71 -> Default_reduce_act Coq__2.Prod'prog'0
     | Nis'70 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.EOF't -> Shift_act Nis'71
         | _ -> Fail_act)
     | Nis'68 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'66 -> Default_reduce_act Coq__2.Prod'obj'4
     | Nis'65 -> Default_reduce_act Coq__2.Prod'atomic_obj'5
     | Nis'64 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'65
         | _ -> Fail_act)
     | Nis'63 -> Default_reduce_act Coq__2.Prod'obj'3
     | Nis'62 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.END't -> Shift_act Nis'63
         | _ -> Fail_act)
     | Nis'60 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DARROW't -> Shift_act Nis'61
         | _ -> Fail_act)
     | Nis'59 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR't -> Shift_act Nis'60
         | _ -> Fail_act)
     | Nis'58 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'59
         | _ -> Fail_act)
     | Nis'57 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR't -> Shift_act Nis'58
         | _ -> Fail_act)
     | Nis'56 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SUCC't -> Shift_act Nis'57
         | _ -> Fail_act)
     | Nis'55 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.BAR't -> Shift_act Nis'56
         | _ -> Fail_act)
     | Nis'53 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DARROW't -> Shift_act Nis'54
         | _ -> Fail_act)
     | Nis'52 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ZERO't -> Shift_act Nis'53
         | _ -> Fail_act)
     | Nis'51 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.BAR't -> Shift_act Nis'52
         | _ -> Fail_act)
     | Nis'49 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DOT't -> Shift_act Nis'50
         | _ -> Fail_act)
     | Nis'48 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR't -> Shift_act Nis'49
         | _ -> Fail_act)
     | Nis'47 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RETURN't -> Shift_act Nis'48
         | _ -> Fail_act)
     | Nis'46 -> Default_reduce_act Coq__2.Prod'params'1
     | Nis'45 -> Default_reduce_act Coq__2.Prod'params'0
     | Nis'44 -> Default_reduce_act Coq__2.Prod'obj'0
     | Nis'42 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ARROW't -> Shift_act Nis'43
         | _ -> Fail_act)
     | Nis'41 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.KIND't -> Shift_act Nis'15
         | Coq__2.TYPE't -> Shift_act Nis'3
         | _ -> Fail_act)
     | Nis'40 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'41
         | Coq__2.LPAREN't -> Shift_act Nis'9
         | _ -> Fail_act)
     | Nis'39 -> Default_reduce_act Coq__2.Prod'param'0
     | Nis'38 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'39
         | _ -> Fail_act)
     | Nis'37 -> Default_reduce_act Coq__2.Prod'obj'5
     | Nis'36 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'23
         | _ -> Fail_act)
     | Nis'35 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.IN't -> Shift_act Nis'36
         | _ -> Fail_act)
     | Nis'34 -> Default_reduce_act Coq__2.Prod'let_defn'0
     | Nis'33 -> Default_reduce_act Coq__2.Prod'obj'1
     | Nis'32 -> Default_reduce_act Coq__2.Prod'app_obj'0
     | Nis'31 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.INT't -> Shift_act Nis'24
         | Coq__2.KIND't -> Shift_act Nis'15
         | Coq__2.LPAREN't -> Shift_act Nis'6
         | Coq__2.NAT't -> Shift_act Nis'5
         | Coq__2.TYPE't -> Shift_act Nis'3
         | Coq__2.VAR't -> Shift_act Nis'2
         | Coq__2.ZERO't -> Shift_act Nis'1
         | _ -> Reduce_act Coq__2.Prod'obj'2)
     | Nis'30 -> Default_reduce_act Coq__2.Prod'app_obj'1
     | Nis'29 -> Default_reduce_act Coq__2.Prod'ann_obj'0
     | Nis'28 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'29
         | _ -> Fail_act)
     | Nis'26 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'27
         | _ -> Fail_act)
     | Nis'25 -> Default_reduce_act Coq__2.Prod'atomic_obj'0
     | Nis'24 -> Default_reduce_act Coq__2.Prod'atomic_obj'3
     | Nis'22 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'23
         | _ -> Fail_act)
     | Nis'21 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ARROW't -> Shift_act Nis'22
         | _ -> Fail_act)
     | Nis'20 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.KIND't -> Shift_act Nis'15
         | Coq__2.TYPE't -> Shift_act Nis'3
         | _ -> Fail_act)
     | Nis'19 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'20
         | _ -> Fail_act)
     | Nis'18 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'9
         | _ -> Fail_act)
     | Nis'16 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DEF't -> Shift_act Nis'17
         | _ -> Fail_act)
     | Nis'15 -> Default_reduce_act Coq__2.Prod'sort'1
     | Nis'14 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.KIND't -> Shift_act Nis'15
         | Coq__2.TYPE't -> Shift_act Nis'3
         | _ -> Fail_act)
     | Nis'13 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'14
         | _ -> Fail_act)
     | Nis'12 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'9
         | _ -> Fail_act)
     | Nis'10 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'11
         | _ -> Fail_act)
     | Nis'9 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR't -> Shift_act Nis'10
         | _ -> Fail_act)
     | Nis'8 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'9
         | _ -> Fail_act)
     | Nis'5 -> Default_reduce_act Coq__2.Prod'atomic_obj'1
     | Nis'4 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.INT't -> Shift_act Nis'24
         | Coq__2.KIND't -> Shift_act Nis'15
         | Coq__2.LPAREN't -> Shift_act Nis'6
         | Coq__2.NAT't -> Shift_act Nis'5
         | Coq__2.TYPE't -> Shift_act Nis'3
         | Coq__2.VAR't -> Shift_act Nis'2
         | Coq__2.ZERO't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'3 -> Default_reduce_act Coq__2.Prod'sort'0
     | Nis'2 -> Default_reduce_act Coq__2.Prod'atomic_obj'4
     | Nis'1 -> Default_reduce_act Coq__2.Prod'atomic_obj'2
     | _ ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.INT't -> Shift_act Nis'24
         | Coq__2.KIND't -> Shift_act Nis'15
         | Coq__2.LAMBDA't -> Shift_act Nis'18
         | Coq__2.LET't -> Shift_act Nis'12
         | Coq__2.LPAREN't -> Shift_act Nis'6
         | Coq__2.NAT't -> Shift_act Nis'5
         | Coq__2.PI't -> Shift_act Nis'8
         | Coq__2.REC't -> Shift_act Nis'7
         | Coq__2.SUCC't -> Shift_act Nis'4
         | Coq__2.TYPE't -> Shift_act Nis'3
         | Coq__2.VAR't -> Shift_act Nis'2
         | Coq__2.ZERO't -> Shift_act Nis'1
         | _ -> Fail_act))

  (** val goto_table : state -> Coq__2.nonterminal -> noninitstate option **)

  let goto_table state0 nt =
    match state0 with
    | Init _ ->
      (match nt with
       | Coq__2.Coq_app_obj'nt -> Some Nis'31
       | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
       | Coq__2.Coq_obj'nt -> Some Nis'68
       | Coq__2.Coq_sort'nt -> Some Nis'25
       | _ -> None)
    | Ninit n ->
      (match n with
       | Nis'69 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'70
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'61 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'62
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'54 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'55
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'50 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'51
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'43 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'44
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'41 ->
         (match nt with
          | Coq__2.Coq_sort'nt -> Some Nis'42
          | _ -> None)
       | Nis'40 ->
         (match nt with
          | Coq__2.Coq_param'nt -> Some Nis'45
          | _ -> None)
       | Nis'36 ->
         (match nt with
          | Coq__2.Coq_ann_obj'nt -> Some Nis'37
          | _ -> None)
       | Nis'31 ->
         (match nt with
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'32
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'27 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'28
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'23 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'26
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'22 ->
         (match nt with
          | Coq__2.Coq_ann_obj'nt -> Some Nis'33
          | _ -> None)
       | Nis'20 ->
         (match nt with
          | Coq__2.Coq_sort'nt -> Some Nis'21
          | _ -> None)
       | Nis'18 ->
         (match nt with
          | Coq__2.Coq_param'nt -> Some Nis'19
          | _ -> None)
       | Nis'17 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'34
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'14 ->
         (match nt with
          | Coq__2.Coq_sort'nt -> Some Nis'16
          | _ -> None)
       | Nis'12 ->
         (match nt with
          | Coq__2.Coq_let_defn'nt -> Some Nis'35
          | Coq__2.Coq_param'nt -> Some Nis'13
          | _ -> None)
       | Nis'11 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'38
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'8 ->
         (match nt with
          | Coq__2.Coq_param'nt -> Some Nis'46
          | Coq__2.Coq_params'nt -> Some Nis'40
          | _ -> None)
       | Nis'7 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'47
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'6 ->
         (match nt with
          | Coq__2.Coq_app_obj'nt -> Some Nis'31
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'30
          | Coq__2.Coq_obj'nt -> Some Nis'64
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | Nis'4 ->
         (match nt with
          | Coq__2.Coq_atomic_obj'nt -> Some Nis'66
          | Coq__2.Coq_sort'nt -> Some Nis'25
          | _ -> None)
       | _ -> None)

  (** val past_symb_of_non_init_state : noninitstate -> Coq__2.symbol list **)

  let past_symb_of_non_init_state = fun _ -> assert false

  (** val past_state_of_non_init_state :
      noninitstate -> (state -> bool) list **)

  let past_state_of_non_init_state = fun _ -> assert false

  (** val items_of_state : state -> item list **)

  let items_of_state = fun _ -> assert false

  (** val coq_N_of_state : state -> int **)

  let coq_N_of_state = function
  | Init _ -> 0
  | Ninit n ->
    (match n with
     | Nis'71 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) 1))))))
     | Nis'70 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) 1))))))
     | Nis'69 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) 1))))))
     | Nis'68 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) 1))))))
     | Nis'66 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) 1))))))
     | Nis'65 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) 1))))))
     | Nis'64 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) 1))))))
     | Nis'63 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'62 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'61 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'60 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'59 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'58 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'57 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'56 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'55 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'54 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'53 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'52 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'51 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'50 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'49 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'48 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->1+2*p) 1)))))
     | Nis'47 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'46 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'45 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'44 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'43 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'42 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'41 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'40 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1)))))
     | Nis'39 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'38 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'37 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'36 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'35 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'34 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'33 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) 1)))))
     | Nis'32 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         1)))))
     | Nis'31 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
     | Nis'30 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
     | Nis'29 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
     | Nis'28 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
     | Nis'27 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
     | Nis'26 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
     | Nis'25 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
     | Nis'24 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
     | Nis'23 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
     | Nis'22 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
     | Nis'21 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
     | Nis'20 ->
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
     | Nis'19 ->
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))
     | Nis'18 ->
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))
     | Nis'17 ->
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
     | Nis'16 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
     | Nis'15 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
     | Nis'14 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
     | Nis'13 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
     | Nis'12 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
     | Nis'11 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
     | Nis'10 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
     | Nis'9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
     | Nis'8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
     | Nis'7 -> ((fun p->1+2*p) ((fun p->1+2*p) 1))
     | Nis'6 -> ((fun p->2*p) ((fun p->1+2*p) 1))
     | Nis'5 -> ((fun p->1+2*p) ((fun p->2*p) 1))
     | Nis'4 -> ((fun p->2*p) ((fun p->2*p) 1))
     | Nis'3 -> ((fun p->1+2*p) 1)
     | Nis'2 -> ((fun p->2*p) 1)
     | Nis'1 -> 1)
 end

module MenhirLibParser = Make(Aut)

(** val prog :
    int -> MenhirLibParser.Inter.buffer -> (Cst.obj * Cst.obj)
    MenhirLibParser.Inter.parse_result **)

let prog =
  Obj.magic MenhirLibParser.parse Aut.Init'0
