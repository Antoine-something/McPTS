  

From Coq Require Import List String.

From McPTS.CaseStudies.LF Require Import Frontend.

Parameter loc : Type.

Arguments eq_refl {_} _.



From Coq.extraction Require Extraction.
From Coq.Lists Require List.
From Coq.PArith Require Import BinPos.
From Coq.NArith Require Import BinNat.
From MenhirLib Require Main.
From MenhirLib Require Version.
Import List.ListNotations.

Definition version_check : unit := MenhirLib.Version.require_20240715.

Unset Elimination Schemes.

Inductive token : Type :=
| ZERO :        (loc)%type -> token
| VAR :        (loc*string)%type -> token
| TYPE :        (loc)%type -> token
| SUCC :        (loc)%type -> token
| RPAREN :        (loc)%type -> token
| RETURN :        (loc)%type -> token
| REC :        (loc)%type -> token
| PI :        (loc)%type -> token
| NAT :        (loc)%type -> token
| LPAREN :        (loc)%type -> token
| LET :        (loc)%type -> token
| LAMBDA :        (loc)%type -> token
| KIND :        (loc)%type -> token
| INT :        (loc*nat)%type -> token
| IN :        (loc)%type -> token
| EOF :        (loc)%type -> token
| END :        (loc)%type -> token
| DOT :        (loc)%type -> token
| DEF :        (loc)%type -> token
| DARROW :        (loc)%type -> token
| COMMA :        (loc)%type -> token
| COLON :        (loc)%type -> token
| BAR :        (loc)%type -> token
| ARROW :        (loc)%type -> token.

Module Import Gram <: MenhirLib.Grammar.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Inductive terminal' : Set :=
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
| ZERO't.
Definition terminal := terminal'.

Global Program Instance terminalNum : MenhirLib.Alphabet.Numbered terminal :=
  { inj := fun x => match x return _ with
    | ARROW't => 1%positive
    | BAR't => 2%positive
    | COLON't => 3%positive
    | COMMA't => 4%positive
    | DARROW't => 5%positive
    | DEF't => 6%positive
    | DOT't => 7%positive
    | END't => 8%positive
    | EOF't => 9%positive
    | IN't => 10%positive
    | INT't => 11%positive
    | KIND't => 12%positive
    | LAMBDA't => 13%positive
    | LET't => 14%positive
    | LPAREN't => 15%positive
    | NAT't => 16%positive
    | PI't => 17%positive
    | REC't => 18%positive
    | RETURN't => 19%positive
    | RPAREN't => 20%positive
    | SUCC't => 21%positive
    | TYPE't => 22%positive
    | VAR't => 23%positive
    | ZERO't => 24%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => ARROW't
    | 2%positive => BAR't
    | 3%positive => COLON't
    | 4%positive => COMMA't
    | 5%positive => DARROW't
    | 6%positive => DEF't
    | 7%positive => DOT't
    | 8%positive => END't
    | 9%positive => EOF't
    | 10%positive => IN't
    | 11%positive => INT't
    | 12%positive => KIND't
    | 13%positive => LAMBDA't
    | 14%positive => LET't
    | 15%positive => LPAREN't
    | 16%positive => NAT't
    | 17%positive => PI't
    | 18%positive => REC't
    | 19%positive => RETURN't
    | 20%positive => RPAREN't
    | 21%positive => SUCC't
    | 22%positive => TYPE't
    | 23%positive => VAR't
    | 24%positive => ZERO't
    | _ => ARROW't
    end)%Z;
    inj_bound := 24%positive }.
Global Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| ann_obj'nt
| app_obj'nt
| atomic_obj'nt
| let_defn'nt
| obj'nt
| param'nt
| params'nt
| prog'nt
| sort'nt.
Definition nonterminal := nonterminal'.

Global Program Instance nonterminalNum : MenhirLib.Alphabet.Numbered nonterminal :=
  { inj := fun x => match x return _ with
    | ann_obj'nt => 1%positive
    | app_obj'nt => 2%positive
    | atomic_obj'nt => 3%positive
    | let_defn'nt => 4%positive
    | obj'nt => 5%positive
    | param'nt => 6%positive
    | params'nt => 7%positive
    | prog'nt => 8%positive
    | sort'nt => 9%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => ann_obj'nt
    | 2%positive => app_obj'nt
    | 3%positive => atomic_obj'nt
    | 4%positive => let_defn'nt
    | 5%positive => obj'nt
    | 6%positive => param'nt
    | 7%positive => params'nt
    | 8%positive => prog'nt
    | 9%positive => sort'nt
    | _ => ann_obj'nt
    end)%Z;
    inj_bound := 9%positive }.
Global Instance NonTerminalAlph : MenhirLib.Alphabet.Alphabet nonterminal := _.

Include MenhirLib.Grammar.Symbol.

Definition terminal_semantic_type (t:terminal) : Type:=
  match t with
  | ZERO't =>        (loc)%type
  | VAR't =>        (loc*string)%type
  | TYPE't =>        (loc)%type
  | SUCC't =>        (loc)%type
  | RPAREN't =>        (loc)%type
  | RETURN't =>        (loc)%type
  | REC't =>        (loc)%type
  | PI't =>        (loc)%type
  | NAT't =>        (loc)%type
  | LPAREN't =>        (loc)%type
  | LET't =>        (loc)%type
  | LAMBDA't =>        (loc)%type
  | KIND't =>        (loc)%type
  | INT't =>        (loc*nat)%type
  | IN't =>        (loc)%type
  | EOF't =>        (loc)%type
  | END't =>        (loc)%type
  | DOT't =>        (loc)%type
  | DEF't =>        (loc)%type
  | DARROW't =>        (loc)%type
  | COMMA't =>        (loc)%type
  | COLON't =>        (loc)%type
  | BAR't =>        (loc)%type
  | ARROW't =>        (loc)%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | sort'nt =>       (Cst.obj)%type
  | prog'nt =>        (Cst.obj * Cst.obj)%type
  | params'nt =>       (list (string * Cst.obj))%type
  | param'nt =>       (string * Cst.obj)%type
  | obj'nt =>       (Cst.obj)%type
  | let_defn'nt =>       (((string * Cst.obj) * Cst.obj) * Cst.obj)%type
  | atomic_obj'nt =>       (Cst.obj)%type
  | app_obj'nt =>       (Cst.obj)%type
  | ann_obj'nt =>       (Cst.obj * Cst.obj)%type
  end.

Definition symbol_semantic_type (s:symbol) : Type:=
  match s with
  | T t => terminal_semantic_type t
  | NT nt => nonterminal_semantic_type nt
  end.

Definition token := token.

Definition token_term (tok : token) : terminal :=
  match tok with
  | ZERO _ => ZERO't
  | VAR _ => VAR't
  | TYPE _ => TYPE't
  | SUCC _ => SUCC't
  | RPAREN _ => RPAREN't
  | RETURN _ => RETURN't
  | REC _ => REC't
  | PI _ => PI't
  | NAT _ => NAT't
  | LPAREN _ => LPAREN't
  | LET _ => LET't
  | LAMBDA _ => LAMBDA't
  | KIND _ => KIND't
  | INT _ => INT't
  | IN _ => IN't
  | EOF _ => EOF't
  | END _ => END't
  | DOT _ => DOT't
  | DEF _ => DEF't
  | DARROW _ => DARROW't
  | COMMA _ => COMMA't
  | COLON _ => COLON't
  | BAR _ => BAR't
  | ARROW _ => ARROW't
  end.

Definition token_sem (tok : token) : symbol_semantic_type (T (token_term tok)) :=
  match tok with
  | ZERO x => x
  | VAR x => x
  | TYPE x => x
  | SUCC x => x
  | RPAREN x => x
  | RETURN x => x
  | REC x => x
  | PI x => x
  | NAT x => x
  | LPAREN x => x
  | LET x => x
  | LAMBDA x => x
  | KIND x => x
  | INT x => x
  | IN x => x
  | EOF x => x
  | END x => x
  | DOT x => x
  | DEF x => x
  | DARROW x => x
  | COMMA x => x
  | COLON x => x
  | BAR x => x
  | ARROW x => x
  end.

Inductive production' : Set :=
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
| Prod'ann_obj'0.
Definition production := production'.

Global Program Instance productionNum : MenhirLib.Alphabet.Numbered production :=
  { inj := fun x => match x return _ with
    | Prod'sort'1 => 1%positive
    | Prod'sort'0 => 2%positive
    | Prod'prog'0 => 3%positive
    | Prod'params'1 => 4%positive
    | Prod'params'0 => 5%positive
    | Prod'param'0 => 6%positive
    | Prod'obj'5 => 7%positive
    | Prod'obj'4 => 8%positive
    | Prod'obj'3 => 9%positive
    | Prod'obj'2 => 10%positive
    | Prod'obj'1 => 11%positive
    | Prod'obj'0 => 12%positive
    | Prod'let_defn'0 => 13%positive
    | Prod'atomic_obj'5 => 14%positive
    | Prod'atomic_obj'4 => 15%positive
    | Prod'atomic_obj'3 => 16%positive
    | Prod'atomic_obj'2 => 17%positive
    | Prod'atomic_obj'1 => 18%positive
    | Prod'atomic_obj'0 => 19%positive
    | Prod'app_obj'1 => 20%positive
    | Prod'app_obj'0 => 21%positive
    | Prod'ann_obj'0 => 22%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'sort'1
    | 2%positive => Prod'sort'0
    | 3%positive => Prod'prog'0
    | 4%positive => Prod'params'1
    | 5%positive => Prod'params'0
    | 6%positive => Prod'param'0
    | 7%positive => Prod'obj'5
    | 8%positive => Prod'obj'4
    | 9%positive => Prod'obj'3
    | 10%positive => Prod'obj'2
    | 11%positive => Prod'obj'1
    | 12%positive => Prod'obj'0
    | 13%positive => Prod'let_defn'0
    | 14%positive => Prod'atomic_obj'5
    | 15%positive => Prod'atomic_obj'4
    | 16%positive => Prod'atomic_obj'3
    | 17%positive => Prod'atomic_obj'2
    | 18%positive => Prod'atomic_obj'1
    | 19%positive => Prod'atomic_obj'0
    | 20%positive => Prod'app_obj'1
    | 21%positive => Prod'app_obj'0
    | 22%positive => Prod'ann_obj'0
    | _ => Prod'sort'1
    end)%Z;
    inj_bound := 22%positive }.
Global Instance ProductionAlph : MenhirLib.Alphabet.Alphabet production := _.

Definition prod_contents (p:production) :
  { p:nonterminal * list symbol &
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) }
 :=
  let box := existT (fun p =>
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) )
  in
  match p with
  | Prod'ann_obj'0 => box
    (ann_obj'nt, [T RPAREN't; NT obj'nt; T COLON't; NT obj'nt; T LPAREN't]%list)
    (fun _5 ann _3 exp _1 =>
                                         ( (exp, ann) )
)
  | Prod'app_obj'0 => box
    (app_obj'nt, [NT atomic_obj'nt; NT app_obj'nt]%list)
    (fun atomic_obj app_obj =>
                                 ( Cst.app app_obj atomic_obj )
)
  | Prod'app_obj'1 => box
    (app_obj'nt, [NT atomic_obj'nt]%list)
    (fun atomic_obj =>
atomic_obj
)
  | Prod'atomic_obj'0 => box
    (atomic_obj'nt, [NT sort'nt]%list)
    (fun sort =>
sort
)
  | Prod'atomic_obj'1 => box
    (atomic_obj'nt, [T NAT't]%list)
    (fun _1 =>
         ( Cst.nat )
)
  | Prod'atomic_obj'2 => box
    (atomic_obj'nt, [T ZERO't]%list)
    (fun _1 =>
          ( Cst.zero )
)
  | Prod'atomic_obj'3 => box
    (atomic_obj'nt, [T INT't]%list)
    (fun n =>
             ( nat_rect (fun _ => Cst.obj) Cst.zero (fun _ => Cst.succ) (snd n) )
)
  | Prod'atomic_obj'4 => box
    (atomic_obj'nt, [T VAR't]%list)
    (fun x =>
             ( Cst.var (snd x) )
)
  | Prod'atomic_obj'5 => box
    (atomic_obj'nt, [T RPAREN't; NT obj'nt; T LPAREN't]%list)
    (fun _3 obj _1 =>
obj
)
  | Prod'let_defn'0 => box
    (let_defn'nt, [NT obj'nt; T DEF't; NT sort'nt; T COLON't; NT param'nt]%list)
    (fun obj _4 s _2 param =>
                                             ( ((param, obj), s) )
)
  | Prod'obj'0 => box
    (obj'nt, [NT obj'nt; T ARROW't; NT sort'nt; T COLON't; NT params'nt; T PI't]%list)
    (fun obj _5 s _3 params _1 =>
                                                  ( List.fold_left (fun acc arg => Cst.pi (fst arg) s (snd arg) acc) params obj )
)
  | Prod'obj'1 => box
    (obj'nt, [NT ann_obj'nt; T ARROW't; NT sort'nt; T COLON't; NT param'nt; T LAMBDA't]%list)
    (fun ann_obj _5 s _3 param _1 =>
                                                         ( Cst.fn (fst param) s (snd param) (snd ann_obj) (fst ann_obj) )
)
  | Prod'obj'2 => box
    (obj'nt, [NT app_obj'nt]%list)
    (fun app_obj =>
app_obj
)
  | Prod'obj'3 => box
    (obj'nt, [T END't; NT obj'nt; T DARROW't; T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list)
    (fun _18 es _16 sr _14 sx _12 _11 ez _9 _8 _7 em _5 mx _3 escr _1 =>
         ( Cst.natrec escr (snd mx) em ez (snd sx) (snd sr) es )
)
  | Prod'obj'4 => box
    (obj'nt, [NT atomic_obj'nt; T SUCC't]%list)
    (fun atomic_obj _1 =>
                          ( Cst.succ atomic_obj )
)
  | Prod'obj'5 => box
    (obj'nt, [NT ann_obj'nt; T IN't; NT let_defn'nt; T LET't]%list)
    (fun body _3 ds _1 =>
                                            (Cst.app (Cst.fn (fst (fst (fst ds))) (snd ds) (snd (fst (fst ds))) (snd body) (fst body)) (snd (fst ds)) )
)
  | Prod'param'0 => box
    (param'nt, [T RPAREN't; NT obj'nt; T COLON't; T VAR't; T LPAREN't]%list)
    (fun _5 obj _3 x _1 =>
                                     ( (snd x, obj) )
)
  | Prod'params'0 => box
    (params'nt, [NT param'nt; NT params'nt]%list)
    (fun param params =>
                           ( param :: params )
)
  | Prod'params'1 => box
    (params'nt, [NT param'nt]%list)
    (fun param =>
               ( [param] )
)
  | Prod'prog'0 => box
    (prog'nt, [T EOF't; NT obj'nt; T COLON't; NT obj'nt]%list)
    (fun _4 ty _2 exp =>
(exp, ty)
)
  | Prod'sort'0 => box
    (sort'nt, [T TYPE't]%list)
    (fun _1 =>
          ( Cst.s_typ )
)
  | Prod'sort'1 => box
    (sort'nt, [T KIND't]%list)
    (fun _1 =>
          (Cst.s_knd)
)
  end.

Definition prod_lhs (p:production) :=
  fst (projT1 (prod_contents p)).
Definition prod_rhs_rev (p:production) :=
  snd (projT1 (prod_contents p)).
Definition prod_action (p:production) :=
  projT2 (prod_contents p).

Include MenhirLib.Grammar.Defs.

End Gram.

Module Aut <: MenhirLib.Automaton.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Module Gram := Gram.
Module GramDefs := Gram.

Definition nullable_nterm (nt:nonterminal) : bool :=
  match nt with
  | sort'nt => false
  | prog'nt => false
  | params'nt => false
  | param'nt => false
  | obj'nt => false
  | let_defn'nt => false
  | atomic_obj'nt => false
  | app_obj'nt => false
  | ann_obj'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | sort'nt => [TYPE't; KIND't]%list
  | prog'nt => [ZERO't; VAR't; TYPE't; SUCC't; REC't; PI't; NAT't; LPAREN't; LET't; LAMBDA't; KIND't; INT't]%list
  | params'nt => [LPAREN't]%list
  | param'nt => [LPAREN't]%list
  | obj'nt => [ZERO't; VAR't; TYPE't; SUCC't; REC't; PI't; NAT't; LPAREN't; LET't; LAMBDA't; KIND't; INT't]%list
  | let_defn'nt => [LPAREN't]%list
  | atomic_obj'nt => [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't]%list
  | app_obj'nt => [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't]%list
  | ann_obj'nt => [LPAREN't]%list
  end.

Inductive noninitstate' : Set :=
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
| Nis'1.
Definition noninitstate := noninitstate'.

Global Program Instance noninitstateNum : MenhirLib.Alphabet.Numbered noninitstate :=
  { inj := fun x => match x return _ with
    | Nis'71 => 1%positive
    | Nis'70 => 2%positive
    | Nis'69 => 3%positive
    | Nis'68 => 4%positive
    | Nis'66 => 5%positive
    | Nis'65 => 6%positive
    | Nis'64 => 7%positive
    | Nis'63 => 8%positive
    | Nis'62 => 9%positive
    | Nis'61 => 10%positive
    | Nis'60 => 11%positive
    | Nis'59 => 12%positive
    | Nis'58 => 13%positive
    | Nis'57 => 14%positive
    | Nis'56 => 15%positive
    | Nis'55 => 16%positive
    | Nis'54 => 17%positive
    | Nis'53 => 18%positive
    | Nis'52 => 19%positive
    | Nis'51 => 20%positive
    | Nis'50 => 21%positive
    | Nis'49 => 22%positive
    | Nis'48 => 23%positive
    | Nis'47 => 24%positive
    | Nis'46 => 25%positive
    | Nis'45 => 26%positive
    | Nis'44 => 27%positive
    | Nis'43 => 28%positive
    | Nis'42 => 29%positive
    | Nis'41 => 30%positive
    | Nis'40 => 31%positive
    | Nis'39 => 32%positive
    | Nis'38 => 33%positive
    | Nis'37 => 34%positive
    | Nis'36 => 35%positive
    | Nis'35 => 36%positive
    | Nis'34 => 37%positive
    | Nis'33 => 38%positive
    | Nis'32 => 39%positive
    | Nis'31 => 40%positive
    | Nis'30 => 41%positive
    | Nis'29 => 42%positive
    | Nis'28 => 43%positive
    | Nis'27 => 44%positive
    | Nis'26 => 45%positive
    | Nis'25 => 46%positive
    | Nis'24 => 47%positive
    | Nis'23 => 48%positive
    | Nis'22 => 49%positive
    | Nis'21 => 50%positive
    | Nis'20 => 51%positive
    | Nis'19 => 52%positive
    | Nis'18 => 53%positive
    | Nis'17 => 54%positive
    | Nis'16 => 55%positive
    | Nis'15 => 56%positive
    | Nis'14 => 57%positive
    | Nis'13 => 58%positive
    | Nis'12 => 59%positive
    | Nis'11 => 60%positive
    | Nis'10 => 61%positive
    | Nis'9 => 62%positive
    | Nis'8 => 63%positive
    | Nis'7 => 64%positive
    | Nis'6 => 65%positive
    | Nis'5 => 66%positive
    | Nis'4 => 67%positive
    | Nis'3 => 68%positive
    | Nis'2 => 69%positive
    | Nis'1 => 70%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'71
    | 2%positive => Nis'70
    | 3%positive => Nis'69
    | 4%positive => Nis'68
    | 5%positive => Nis'66
    | 6%positive => Nis'65
    | 7%positive => Nis'64
    | 8%positive => Nis'63
    | 9%positive => Nis'62
    | 10%positive => Nis'61
    | 11%positive => Nis'60
    | 12%positive => Nis'59
    | 13%positive => Nis'58
    | 14%positive => Nis'57
    | 15%positive => Nis'56
    | 16%positive => Nis'55
    | 17%positive => Nis'54
    | 18%positive => Nis'53
    | 19%positive => Nis'52
    | 20%positive => Nis'51
    | 21%positive => Nis'50
    | 22%positive => Nis'49
    | 23%positive => Nis'48
    | 24%positive => Nis'47
    | 25%positive => Nis'46
    | 26%positive => Nis'45
    | 27%positive => Nis'44
    | 28%positive => Nis'43
    | 29%positive => Nis'42
    | 30%positive => Nis'41
    | 31%positive => Nis'40
    | 32%positive => Nis'39
    | 33%positive => Nis'38
    | 34%positive => Nis'37
    | 35%positive => Nis'36
    | 36%positive => Nis'35
    | 37%positive => Nis'34
    | 38%positive => Nis'33
    | 39%positive => Nis'32
    | 40%positive => Nis'31
    | 41%positive => Nis'30
    | 42%positive => Nis'29
    | 43%positive => Nis'28
    | 44%positive => Nis'27
    | 45%positive => Nis'26
    | 46%positive => Nis'25
    | 47%positive => Nis'24
    | 48%positive => Nis'23
    | 49%positive => Nis'22
    | 50%positive => Nis'21
    | 51%positive => Nis'20
    | 52%positive => Nis'19
    | 53%positive => Nis'18
    | 54%positive => Nis'17
    | 55%positive => Nis'16
    | 56%positive => Nis'15
    | 57%positive => Nis'14
    | 58%positive => Nis'13
    | 59%positive => Nis'12
    | 60%positive => Nis'11
    | 61%positive => Nis'10
    | 62%positive => Nis'9
    | 63%positive => Nis'8
    | 64%positive => Nis'7
    | 65%positive => Nis'6
    | 66%positive => Nis'5
    | 67%positive => Nis'4
    | 68%positive => Nis'3
    | 69%positive => Nis'2
    | 70%positive => Nis'1
    | _ => Nis'71
    end)%Z;
    inj_bound := 70%positive }.
Global Instance NonInitStateAlph : MenhirLib.Alphabet.Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T ZERO't
  | Nis'2 => T VAR't
  | Nis'3 => T TYPE't
  | Nis'4 => T SUCC't
  | Nis'5 => T NAT't
  | Nis'6 => T LPAREN't
  | Nis'7 => T REC't
  | Nis'8 => T PI't
  | Nis'9 => T LPAREN't
  | Nis'10 => T VAR't
  | Nis'11 => T COLON't
  | Nis'12 => T LET't
  | Nis'13 => NT param'nt
  | Nis'14 => T COLON't
  | Nis'15 => T KIND't
  | Nis'16 => NT sort'nt
  | Nis'17 => T DEF't
  | Nis'18 => T LAMBDA't
  | Nis'19 => NT param'nt
  | Nis'20 => T COLON't
  | Nis'21 => NT sort'nt
  | Nis'22 => T ARROW't
  | Nis'23 => T LPAREN't
  | Nis'24 => T INT't
  | Nis'25 => NT sort'nt
  | Nis'26 => NT obj'nt
  | Nis'27 => T COLON't
  | Nis'28 => NT obj'nt
  | Nis'29 => T RPAREN't
  | Nis'30 => NT atomic_obj'nt
  | Nis'31 => NT app_obj'nt
  | Nis'32 => NT atomic_obj'nt
  | Nis'33 => NT ann_obj'nt
  | Nis'34 => NT obj'nt
  | Nis'35 => NT let_defn'nt
  | Nis'36 => T IN't
  | Nis'37 => NT ann_obj'nt
  | Nis'38 => NT obj'nt
  | Nis'39 => T RPAREN't
  | Nis'40 => NT params'nt
  | Nis'41 => T COLON't
  | Nis'42 => NT sort'nt
  | Nis'43 => T ARROW't
  | Nis'44 => NT obj'nt
  | Nis'45 => NT param'nt
  | Nis'46 => NT param'nt
  | Nis'47 => NT obj'nt
  | Nis'48 => T RETURN't
  | Nis'49 => T VAR't
  | Nis'50 => T DOT't
  | Nis'51 => NT obj'nt
  | Nis'52 => T BAR't
  | Nis'53 => T ZERO't
  | Nis'54 => T DARROW't
  | Nis'55 => NT obj'nt
  | Nis'56 => T BAR't
  | Nis'57 => T SUCC't
  | Nis'58 => T VAR't
  | Nis'59 => T COMMA't
  | Nis'60 => T VAR't
  | Nis'61 => T DARROW't
  | Nis'62 => NT obj'nt
  | Nis'63 => T END't
  | Nis'64 => NT obj'nt
  | Nis'65 => T RPAREN't
  | Nis'66 => NT atomic_obj'nt
  | Nis'68 => NT obj'nt
  | Nis'69 => T COLON't
  | Nis'70 => NT obj'nt
  | Nis'71 => T EOF't
  end.

Inductive initstate' : Set :=
| Init'0.
Definition initstate := initstate'.

Global Program Instance initstateNum : MenhirLib.Alphabet.Numbered initstate :=
  { inj := fun x => match x return _ with
    | Init'0 => 1%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Init'0
    | _ => Init'0
    end)%Z;
    inj_bound := 1%positive }.
Global Instance InitStateAlph : MenhirLib.Alphabet.Alphabet initstate := _.

Include MenhirLib.Automaton.Types.

Definition start_nt (init:initstate) : nonterminal :=
  match init with
  | Init'0 => prog'nt
  end.

Definition action_table (state:state) : action :=
  match state with
  | Init Init'0 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Default_reduce_act Prod'atomic_obj'2
  | Ninit Nis'2 => Default_reduce_act Prod'atomic_obj'4
  | Ninit Nis'3 => Default_reduce_act Prod'sort'0
  | Ninit Nis'4 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'5 => Default_reduce_act Prod'atomic_obj'1
  | Ninit Nis'6 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'7 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'8 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'9 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'10 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'11 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'11 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'14 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'15 => Default_reduce_act Prod'sort'1
  | Ninit Nis'16 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DEF't => Shift_act Nis'17 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'17 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'19 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'20 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'20 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'21 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ARROW't => Shift_act Nis'22 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'22 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'23 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'23 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'24 => Default_reduce_act Prod'atomic_obj'3
  | Ninit Nis'25 => Default_reduce_act Prod'atomic_obj'0
  | Ninit Nis'26 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'27 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'27 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'28 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'29 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'29 => Default_reduce_act Prod'ann_obj'0
  | Ninit Nis'30 => Default_reduce_act Prod'app_obj'1
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Reduce_act Prod'obj'2
    | RPAREN't => Reduce_act Prod'obj'2
    | RETURN't => Reduce_act Prod'obj'2
    | REC't => Reduce_act Prod'obj'2
    | PI't => Reduce_act Prod'obj'2
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Reduce_act Prod'obj'2
    | LAMBDA't => Reduce_act Prod'obj'2
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | IN't => Reduce_act Prod'obj'2
    | EOF't => Reduce_act Prod'obj'2
    | END't => Reduce_act Prod'obj'2
    | DOT't => Reduce_act Prod'obj'2
    | DEF't => Reduce_act Prod'obj'2
    | DARROW't => Reduce_act Prod'obj'2
    | COMMA't => Reduce_act Prod'obj'2
    | COLON't => Reduce_act Prod'obj'2
    | BAR't => Reduce_act Prod'obj'2
    | ARROW't => Reduce_act Prod'obj'2
    end)
  | Ninit Nis'32 => Default_reduce_act Prod'app_obj'0
  | Ninit Nis'33 => Default_reduce_act Prod'obj'1
  | Ninit Nis'34 => Default_reduce_act Prod'let_defn'0
  | Ninit Nis'35 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | IN't => Shift_act Nis'36 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'36 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'23 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'37 => Default_reduce_act Prod'obj'5
  | Ninit Nis'38 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'39 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'39 => Default_reduce_act Prod'param'0
  | Ninit Nis'40 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | COLON't => Shift_act Nis'41 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'41 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'42 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ARROW't => Shift_act Nis'43 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'43 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'44 => Default_reduce_act Prod'obj'0
  | Ninit Nis'45 => Default_reduce_act Prod'params'0
  | Ninit Nis'46 => Default_reduce_act Prod'params'1
  | Ninit Nis'47 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RETURN't => Shift_act Nis'48 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'48 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'49 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'49 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'50 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'50 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'51 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | BAR't => Shift_act Nis'52 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'52 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'53 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'53 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DARROW't => Shift_act Nis'54 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'54 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'55 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | BAR't => Shift_act Nis'56 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'56 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SUCC't => Shift_act Nis'57 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'57 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'58 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'58 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COMMA't => Shift_act Nis'59 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'59 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'60 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'60 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DARROW't => Shift_act Nis'61 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'61 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'62 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | END't => Shift_act Nis'63 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'63 => Default_reduce_act Prod'obj'3
  | Ninit Nis'64 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'65 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'65 => Default_reduce_act Prod'atomic_obj'5
  | Ninit Nis'66 => Default_reduce_act Prod'obj'4
  | Ninit Nis'68 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'69 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'69 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LET't => Shift_act Nis'12 (eq_refl _)
    | LAMBDA't => Shift_act Nis'18 (eq_refl _)
    | KIND't => Shift_act Nis'15 (eq_refl _)
    | INT't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'70 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EOF't => Shift_act Nis'71 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'71 => Default_reduce_act Prod'prog'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Init Init'0, prog'nt => None  | Init Init'0, obj'nt => Some (exist _ Nis'68 (eq_refl _))
  | Init Init'0, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Init Init'0, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'4, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'4, atomic_obj'nt => Some (exist _ Nis'66 (eq_refl _))
  | Ninit Nis'6, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'6, obj'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'6, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'6, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'7, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'7, obj'nt => Some (exist _ Nis'47 (eq_refl _))
  | Ninit Nis'7, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'7, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'8, params'nt => Some (exist _ Nis'40 (eq_refl _))
  | Ninit Nis'8, param'nt => Some (exist _ Nis'46 (eq_refl _))
  | Ninit Nis'11, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'11, obj'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'11, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'11, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'12, param'nt => Some (exist _ Nis'13 (eq_refl _))
  | Ninit Nis'12, let_defn'nt => Some (exist _ Nis'35 (eq_refl _))
  | Ninit Nis'14, sort'nt => Some (exist _ Nis'16 (eq_refl _))
  | Ninit Nis'17, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'17, obj'nt => Some (exist _ Nis'34 (eq_refl _))
  | Ninit Nis'17, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'17, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'18, param'nt => Some (exist _ Nis'19 (eq_refl _))
  | Ninit Nis'20, sort'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'22, ann_obj'nt => Some (exist _ Nis'33 (eq_refl _))
  | Ninit Nis'23, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'23, obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'23, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'23, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'27, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'27, obj'nt => Some (exist _ Nis'28 (eq_refl _))
  | Ninit Nis'27, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'27, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'31, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'31, atomic_obj'nt => Some (exist _ Nis'32 (eq_refl _))
  | Ninit Nis'36, ann_obj'nt => Some (exist _ Nis'37 (eq_refl _))
  | Ninit Nis'40, param'nt => Some (exist _ Nis'45 (eq_refl _))
  | Ninit Nis'41, sort'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'43, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'43, obj'nt => Some (exist _ Nis'44 (eq_refl _))
  | Ninit Nis'43, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'43, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'50, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'50, obj'nt => Some (exist _ Nis'51 (eq_refl _))
  | Ninit Nis'50, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'50, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'54, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'54, obj'nt => Some (exist _ Nis'55 (eq_refl _))
  | Ninit Nis'54, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'54, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'61, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'61, obj'nt => Some (exist _ Nis'62 (eq_refl _))
  | Ninit Nis'61, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'61, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'69, sort'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'69, obj'nt => Some (exist _ Nis'70 (eq_refl _))
  | Ninit Nis'69, atomic_obj'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'69, app_obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []%list
  | Nis'2 => []%list
  | Nis'3 => []%list
  | Nis'4 => []%list
  | Nis'5 => []%list
  | Nis'6 => []%list
  | Nis'7 => []%list
  | Nis'8 => []%list
  | Nis'9 => []%list
  | Nis'10 => [T LPAREN't]%list
  | Nis'11 => [T VAR't; T LPAREN't]%list
  | Nis'12 => []%list
  | Nis'13 => []%list
  | Nis'14 => [NT param'nt]%list
  | Nis'15 => []%list
  | Nis'16 => [T COLON't; NT param'nt]%list
  | Nis'17 => [NT sort'nt; T COLON't; NT param'nt]%list
  | Nis'18 => []%list
  | Nis'19 => [T LAMBDA't]%list
  | Nis'20 => [NT param'nt; T LAMBDA't]%list
  | Nis'21 => [T COLON't; NT param'nt; T LAMBDA't]%list
  | Nis'22 => [NT sort'nt; T COLON't; NT param'nt; T LAMBDA't]%list
  | Nis'23 => []%list
  | Nis'24 => []%list
  | Nis'25 => []%list
  | Nis'26 => [T LPAREN't]%list
  | Nis'27 => [NT obj'nt; T LPAREN't]%list
  | Nis'28 => [T COLON't; NT obj'nt; T LPAREN't]%list
  | Nis'29 => [NT obj'nt; T COLON't; NT obj'nt; T LPAREN't]%list
  | Nis'30 => []%list
  | Nis'31 => []%list
  | Nis'32 => [NT app_obj'nt]%list
  | Nis'33 => [T ARROW't; NT sort'nt; T COLON't; NT param'nt; T LAMBDA't]%list
  | Nis'34 => [T DEF't; NT sort'nt; T COLON't; NT param'nt]%list
  | Nis'35 => [T LET't]%list
  | Nis'36 => [NT let_defn'nt; T LET't]%list
  | Nis'37 => [T IN't; NT let_defn'nt; T LET't]%list
  | Nis'38 => [T COLON't; T VAR't; T LPAREN't]%list
  | Nis'39 => [NT obj'nt; T COLON't; T VAR't; T LPAREN't]%list
  | Nis'40 => [T PI't]%list
  | Nis'41 => [NT params'nt; T PI't]%list
  | Nis'42 => [T COLON't; NT params'nt; T PI't]%list
  | Nis'43 => [NT sort'nt; T COLON't; NT params'nt; T PI't]%list
  | Nis'44 => [T ARROW't; NT sort'nt; T COLON't; NT params'nt; T PI't]%list
  | Nis'45 => [NT params'nt]%list
  | Nis'46 => []%list
  | Nis'47 => [T REC't]%list
  | Nis'48 => [NT obj'nt; T REC't]%list
  | Nis'49 => [T RETURN't; NT obj'nt; T REC't]%list
  | Nis'50 => [T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'51 => [T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'52 => [NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'53 => [T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'54 => [T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'55 => [T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'56 => [NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'57 => [T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'58 => [T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'59 => [T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'60 => [T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'61 => [T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'62 => [T DARROW't; T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'63 => [NT obj'nt; T DARROW't; T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'64 => [T LPAREN't]%list
  | Nis'65 => [NT obj'nt; T LPAREN't]%list
  | Nis'66 => [T SUCC't]%list
  | Nis'68 => []%list
  | Nis'69 => [NT obj'nt]%list
  | Nis'70 => [T COLON't; NT obj'nt]%list
  | Nis'71 => [NT obj'nt; T COLON't; NT obj'nt]%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'4 | Ninit Nis'6 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'17 | Ninit Nis'23 | Ninit Nis'27 | Ninit Nis'31 | Ninit Nis'43 | Ninit Nis'50 | Ninit Nis'54 | Ninit Nis'61 | Ninit Nis'69 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'4 | Ninit Nis'6 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'14 | Ninit Nis'17 | Ninit Nis'20 | Ninit Nis'23 | Ninit Nis'27 | Ninit Nis'31 | Ninit Nis'41 | Ninit Nis'43 | Ninit Nis'50 | Ninit Nis'54 | Ninit Nis'61 | Ninit Nis'69 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'6 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'17 | Ninit Nis'23 | Ninit Nis'27 | Ninit Nis'43 | Ninit Nis'50 | Ninit Nis'54 | Ninit Nis'61 | Ninit Nis'69 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'12 | Ninit Nis'18 | Ninit Nis'40 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'9 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Ninit Nis'10 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'12 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'14 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'16 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'18 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'19 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'20 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'21 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'22 | Ninit Nis'36 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'23 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'26 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'27 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'28 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'31 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Ninit Nis'22 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'35 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'36 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'38 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'40 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Ninit Nis'42 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition state_set_32 (s:state) : bool :=
  match s with
  | Ninit Nis'7 => true
  | _ => false
  end.
Extract Inlined Constant state_set_32 => "assert false".

Definition state_set_33 (s:state) : bool :=
  match s with
  | Ninit Nis'47 => true
  | _ => false
  end.
Extract Inlined Constant state_set_33 => "assert false".

Definition state_set_34 (s:state) : bool :=
  match s with
  | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_34 => "assert false".

Definition state_set_35 (s:state) : bool :=
  match s with
  | Ninit Nis'49 => true
  | _ => false
  end.
Extract Inlined Constant state_set_35 => "assert false".

Definition state_set_36 (s:state) : bool :=
  match s with
  | Ninit Nis'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_36 => "assert false".

Definition state_set_37 (s:state) : bool :=
  match s with
  | Ninit Nis'51 => true
  | _ => false
  end.
Extract Inlined Constant state_set_37 => "assert false".

Definition state_set_38 (s:state) : bool :=
  match s with
  | Ninit Nis'52 => true
  | _ => false
  end.
Extract Inlined Constant state_set_38 => "assert false".

Definition state_set_39 (s:state) : bool :=
  match s with
  | Ninit Nis'53 => true
  | _ => false
  end.
Extract Inlined Constant state_set_39 => "assert false".

Definition state_set_40 (s:state) : bool :=
  match s with
  | Ninit Nis'54 => true
  | _ => false
  end.
Extract Inlined Constant state_set_40 => "assert false".

Definition state_set_41 (s:state) : bool :=
  match s with
  | Ninit Nis'55 => true
  | _ => false
  end.
Extract Inlined Constant state_set_41 => "assert false".

Definition state_set_42 (s:state) : bool :=
  match s with
  | Ninit Nis'56 => true
  | _ => false
  end.
Extract Inlined Constant state_set_42 => "assert false".

Definition state_set_43 (s:state) : bool :=
  match s with
  | Ninit Nis'57 => true
  | _ => false
  end.
Extract Inlined Constant state_set_43 => "assert false".

Definition state_set_44 (s:state) : bool :=
  match s with
  | Ninit Nis'58 => true
  | _ => false
  end.
Extract Inlined Constant state_set_44 => "assert false".

Definition state_set_45 (s:state) : bool :=
  match s with
  | Ninit Nis'59 => true
  | _ => false
  end.
Extract Inlined Constant state_set_45 => "assert false".

Definition state_set_46 (s:state) : bool :=
  match s with
  | Ninit Nis'60 => true
  | _ => false
  end.
Extract Inlined Constant state_set_46 => "assert false".

Definition state_set_47 (s:state) : bool :=
  match s with
  | Ninit Nis'61 => true
  | _ => false
  end.
Extract Inlined Constant state_set_47 => "assert false".

Definition state_set_48 (s:state) : bool :=
  match s with
  | Ninit Nis'62 => true
  | _ => false
  end.
Extract Inlined Constant state_set_48 => "assert false".

Definition state_set_49 (s:state) : bool :=
  match s with
  | Ninit Nis'6 => true
  | _ => false
  end.
Extract Inlined Constant state_set_49 => "assert false".

Definition state_set_50 (s:state) : bool :=
  match s with
  | Ninit Nis'64 => true
  | _ => false
  end.
Extract Inlined Constant state_set_50 => "assert false".

Definition state_set_51 (s:state) : bool :=
  match s with
  | Ninit Nis'4 => true
  | _ => false
  end.
Extract Inlined Constant state_set_51 => "assert false".

Definition state_set_52 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_52 => "assert false".

Definition state_set_53 (s:state) : bool :=
  match s with
  | Ninit Nis'68 => true
  | _ => false
  end.
Extract Inlined Constant state_set_53 => "assert false".

Definition state_set_54 (s:state) : bool :=
  match s with
  | Ninit Nis'69 => true
  | _ => false
  end.
Extract Inlined Constant state_set_54 => "assert false".

Definition state_set_55 (s:state) : bool :=
  match s with
  | Ninit Nis'70 => true
  | _ => false
  end.
Extract Inlined Constant state_set_55 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [state_set_1]%list
  | Nis'2 => [state_set_1]%list
  | Nis'3 => [state_set_2]%list
  | Nis'4 => [state_set_3]%list
  | Nis'5 => [state_set_1]%list
  | Nis'6 => [state_set_1]%list
  | Nis'7 => [state_set_3]%list
  | Nis'8 => [state_set_3]%list
  | Nis'9 => [state_set_4]%list
  | Nis'10 => [state_set_5; state_set_4]%list
  | Nis'11 => [state_set_6; state_set_5; state_set_4]%list
  | Nis'12 => [state_set_3]%list
  | Nis'13 => [state_set_7]%list
  | Nis'14 => [state_set_8; state_set_7]%list
  | Nis'15 => [state_set_2]%list
  | Nis'16 => [state_set_9; state_set_8; state_set_7]%list
  | Nis'17 => [state_set_10; state_set_9; state_set_8; state_set_7]%list
  | Nis'18 => [state_set_3]%list
  | Nis'19 => [state_set_11; state_set_3]%list
  | Nis'20 => [state_set_12; state_set_11; state_set_3]%list
  | Nis'21 => [state_set_13; state_set_12; state_set_11; state_set_3]%list
  | Nis'22 => [state_set_14; state_set_13; state_set_12; state_set_11; state_set_3]%list
  | Nis'23 => [state_set_15]%list
  | Nis'24 => [state_set_1]%list
  | Nis'25 => [state_set_1]%list
  | Nis'26 => [state_set_16; state_set_15]%list
  | Nis'27 => [state_set_17; state_set_16; state_set_15]%list
  | Nis'28 => [state_set_18; state_set_17; state_set_16; state_set_15]%list
  | Nis'29 => [state_set_19; state_set_18; state_set_17; state_set_16; state_set_15]%list
  | Nis'30 => [state_set_3]%list
  | Nis'31 => [state_set_3]%list
  | Nis'32 => [state_set_20; state_set_3]%list
  | Nis'33 => [state_set_21; state_set_14; state_set_13; state_set_12; state_set_11; state_set_3]%list
  | Nis'34 => [state_set_22; state_set_10; state_set_9; state_set_8; state_set_7]%list
  | Nis'35 => [state_set_7; state_set_3]%list
  | Nis'36 => [state_set_23; state_set_7; state_set_3]%list
  | Nis'37 => [state_set_24; state_set_23; state_set_7; state_set_3]%list
  | Nis'38 => [state_set_25; state_set_6; state_set_5; state_set_4]%list
  | Nis'39 => [state_set_26; state_set_25; state_set_6; state_set_5; state_set_4]%list
  | Nis'40 => [state_set_27; state_set_3]%list
  | Nis'41 => [state_set_28; state_set_27; state_set_3]%list
  | Nis'42 => [state_set_29; state_set_28; state_set_27; state_set_3]%list
  | Nis'43 => [state_set_30; state_set_29; state_set_28; state_set_27; state_set_3]%list
  | Nis'44 => [state_set_31; state_set_30; state_set_29; state_set_28; state_set_27; state_set_3]%list
  | Nis'45 => [state_set_28; state_set_27]%list
  | Nis'46 => [state_set_27]%list
  | Nis'47 => [state_set_32; state_set_3]%list
  | Nis'48 => [state_set_33; state_set_32; state_set_3]%list
  | Nis'49 => [state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'50 => [state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'51 => [state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'52 => [state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'53 => [state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'54 => [state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'55 => [state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'56 => [state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'57 => [state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'58 => [state_set_43; state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'59 => [state_set_44; state_set_43; state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'60 => [state_set_45; state_set_44; state_set_43; state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'61 => [state_set_46; state_set_45; state_set_44; state_set_43; state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'62 => [state_set_47; state_set_46; state_set_45; state_set_44; state_set_43; state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'63 => [state_set_48; state_set_47; state_set_46; state_set_45; state_set_44; state_set_43; state_set_42; state_set_41; state_set_40; state_set_39; state_set_38; state_set_37; state_set_36; state_set_35; state_set_34; state_set_33; state_set_32; state_set_3]%list
  | Nis'64 => [state_set_49; state_set_1]%list
  | Nis'65 => [state_set_50; state_set_49; state_set_1]%list
  | Nis'66 => [state_set_51; state_set_3]%list
  | Nis'68 => [state_set_52]%list
  | Nis'69 => [state_set_53; state_set_52]%list
  | Nis'70 => [state_set_54; state_set_53; state_set_52]%list
  | Nis'71 => [state_set_55; state_set_54; state_set_53; state_set_52]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition lookahead_set_1 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't; COLON't]%list.
Extract Inlined Constant lookahead_set_1 => "assert false".

Definition lookahead_set_2 : list terminal :=
  [COLON't]%list.
Extract Inlined Constant lookahead_set_2 => "assert false".

Definition lookahead_set_3 : list terminal :=
  [ZERO't; VAR't; TYPE't; SUCC't; RPAREN't; RETURN't; REC't; PI't; NAT't; LPAREN't; LET't; LAMBDA't; KIND't; INT't; IN't; EOF't; END't; DOT't; DEF't; DARROW't; COMMA't; COLON't; BAR't; ARROW't]%list.
Extract Inlined Constant lookahead_set_3 => "assert false".

Definition lookahead_set_4 : list terminal :=
  [ZERO't; VAR't; TYPE't; RPAREN't; RETURN't; NAT't; LPAREN't; KIND't; INT't; IN't; EOF't; END't; COLON't; BAR't]%list.
Extract Inlined Constant lookahead_set_4 => "assert false".

Definition lookahead_set_5 : list terminal :=
  [ZERO't; VAR't; TYPE't; RPAREN't; RETURN't; NAT't; LPAREN't; KIND't; INT't; IN't; EOF't; END't; DEF't; COLON't; BAR't; ARROW't]%list.
Extract Inlined Constant lookahead_set_5 => "assert false".

Definition lookahead_set_6 : list terminal :=
  [RPAREN't; RETURN't; IN't; EOF't; END't; COLON't; BAR't]%list.
Extract Inlined Constant lookahead_set_6 => "assert false".

Definition lookahead_set_7 : list terminal :=
  [ZERO't; VAR't; TYPE't; RPAREN't; NAT't; LPAREN't; KIND't; INT't]%list.
Extract Inlined Constant lookahead_set_7 => "assert false".

Definition lookahead_set_8 : list terminal :=
  [RPAREN't]%list.
Extract Inlined Constant lookahead_set_8 => "assert false".

Definition lookahead_set_9 : list terminal :=
  [ZERO't; VAR't; TYPE't; RETURN't; NAT't; LPAREN't; KIND't; INT't]%list.
Extract Inlined Constant lookahead_set_9 => "assert false".

Definition lookahead_set_10 : list terminal :=
  [RETURN't]%list.
Extract Inlined Constant lookahead_set_10 => "assert false".

Definition lookahead_set_11 : list terminal :=
  [LPAREN't; COLON't]%list.
Extract Inlined Constant lookahead_set_11 => "assert false".

Definition lookahead_set_12 : list terminal :=
  [IN't]%list.
Extract Inlined Constant lookahead_set_12 => "assert false".

Definition lookahead_set_13 : list terminal :=
  [DEF't]%list.
Extract Inlined Constant lookahead_set_13 => "assert false".

Definition lookahead_set_14 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't; IN't]%list.
Extract Inlined Constant lookahead_set_14 => "assert false".

Definition lookahead_set_15 : list terminal :=
  [ARROW't]%list.
Extract Inlined Constant lookahead_set_15 => "assert false".

Definition lookahead_set_16 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't; BAR't]%list.
Extract Inlined Constant lookahead_set_16 => "assert false".

Definition lookahead_set_17 : list terminal :=
  [BAR't]%list.
Extract Inlined Constant lookahead_set_17 => "assert false".

Definition lookahead_set_18 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't; END't]%list.
Extract Inlined Constant lookahead_set_18 => "assert false".

Definition lookahead_set_19 : list terminal :=
  [END't]%list.
Extract Inlined Constant lookahead_set_19 => "assert false".

Definition lookahead_set_20 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; KIND't; INT't; EOF't]%list.
Extract Inlined Constant lookahead_set_20 => "assert false".

Definition lookahead_set_21 : list terminal :=
  [EOF't]%list.
Extract Inlined Constant lookahead_set_21 => "assert false".

Definition items_of_state_0 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'prog'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_0 => "assert false".

Definition items_of_state_1 : list item :=
  [ {| prod_item := Prod'atomic_obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_1 => "assert false".

Definition items_of_state_2 : list item :=
  [ {| prod_item := Prod'atomic_obj'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_2 => "assert false".

Definition items_of_state_3 : list item :=
  [ {| prod_item := Prod'sort'0; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_3 => "assert false".

Definition items_of_state_4 : list item :=
  [ {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_4 => "assert false".

Definition items_of_state_5 : list item :=
  [ {| prod_item := Prod'atomic_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_5 => "assert false".

Definition items_of_state_6 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_6 => "assert false".

Definition items_of_state_7 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_7 => "assert false".

Definition items_of_state_8 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'params'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'params'1; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_8 => "assert false".

Definition items_of_state_9 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 1; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_9 => "assert false".

Definition items_of_state_10 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 2; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_10 => "assert false".

Definition items_of_state_11 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'param'0; dot_pos_item := 3; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_11 => "assert false".

Definition items_of_state_12 : list item :=
  [ {| prod_item := Prod'let_defn'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ]%list.
Extract Inlined Constant items_of_state_12 => "assert false".

Definition items_of_state_13 : list item :=
  [ {| prod_item := Prod'let_defn'0; dot_pos_item := 1; lookaheads_item := lookahead_set_12 |} ]%list.
Extract Inlined Constant items_of_state_13 => "assert false".

Definition items_of_state_14 : list item :=
  [ {| prod_item := Prod'let_defn'0; dot_pos_item := 2; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |} ]%list.
Extract Inlined Constant items_of_state_14 => "assert false".

Definition items_of_state_15 : list item :=
  [ {| prod_item := Prod'sort'1; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_15 => "assert false".

Definition items_of_state_16 : list item :=
  [ {| prod_item := Prod'let_defn'0; dot_pos_item := 3; lookaheads_item := lookahead_set_12 |} ]%list.
Extract Inlined Constant items_of_state_16 => "assert false".

Definition items_of_state_17 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'let_defn'0; dot_pos_item := 4; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |} ]%list.
Extract Inlined Constant items_of_state_17 => "assert false".

Definition items_of_state_18 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ]%list.
Extract Inlined Constant items_of_state_18 => "assert false".

Definition items_of_state_19 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_19 => "assert false".

Definition items_of_state_20 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |} ]%list.
Extract Inlined Constant items_of_state_20 => "assert false".

Definition items_of_state_21 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_21 => "assert false".

Definition items_of_state_22 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_22 => "assert false".

Definition items_of_state_23 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_23 => "assert false".

Definition items_of_state_24 : list item :=
  [ {| prod_item := Prod'atomic_obj'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_24 => "assert false".

Definition items_of_state_25 : list item :=
  [ {| prod_item := Prod'atomic_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_25 => "assert false".

Definition items_of_state_26 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_26 => "assert false".

Definition items_of_state_27 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_27 => "assert false".

Definition items_of_state_28 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_28 => "assert false".

Definition items_of_state_29 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_29 => "assert false".

Definition items_of_state_30 : list item :=
  [ {| prod_item := Prod'app_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_30 => "assert false".

Definition items_of_state_31 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_31 => "assert false".

Definition items_of_state_32 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_32 => "assert false".

Definition items_of_state_33 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 6; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_33 => "assert false".

Definition items_of_state_34 : list item :=
  [ {| prod_item := Prod'let_defn'0; dot_pos_item := 5; lookaheads_item := lookahead_set_12 |} ]%list.
Extract Inlined Constant items_of_state_34 => "assert false".

Definition items_of_state_35 : list item :=
  [ {| prod_item := Prod'obj'5; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_35 => "assert false".

Definition items_of_state_36 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_36 => "assert false".

Definition items_of_state_37 : list item :=
  [ {| prod_item := Prod'obj'5; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_37 => "assert false".

Definition items_of_state_38 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 4; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_38 => "assert false".

Definition items_of_state_39 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 5; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_39 => "assert false".

Definition items_of_state_40 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'params'0; dot_pos_item := 1; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_40 => "assert false".

Definition items_of_state_41 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |} ]%list.
Extract Inlined Constant items_of_state_41 => "assert false".

Definition items_of_state_42 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_42 => "assert false".

Definition items_of_state_43 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_43 => "assert false".

Definition items_of_state_44 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 6; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_44 => "assert false".

Definition items_of_state_45 : list item :=
  [ {| prod_item := Prod'params'0; dot_pos_item := 2; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_45 => "assert false".

Definition items_of_state_46 : list item :=
  [ {| prod_item := Prod'params'1; dot_pos_item := 1; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_46 => "assert false".

Definition items_of_state_47 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_47 => "assert false".

Definition items_of_state_48 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_48 => "assert false".

Definition items_of_state_49 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_49 => "assert false".

Definition items_of_state_50 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |} ]%list.
Extract Inlined Constant items_of_state_50 => "assert false".

Definition items_of_state_51 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 6; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_51 => "assert false".

Definition items_of_state_52 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 7; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_52 => "assert false".

Definition items_of_state_53 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 8; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_53 => "assert false".

Definition items_of_state_54 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 9; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |} ]%list.
Extract Inlined Constant items_of_state_54 => "assert false".

Definition items_of_state_55 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 10; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_55 => "assert false".

Definition items_of_state_56 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 11; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_56 => "assert false".

Definition items_of_state_57 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 12; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_57 => "assert false".

Definition items_of_state_58 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 13; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_58 => "assert false".

Definition items_of_state_59 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 14; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_59 => "assert false".

Definition items_of_state_60 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 15; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_60 => "assert false".

Definition items_of_state_61 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_19 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_19 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_19 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_19 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 16; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_19 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_19 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_18 |} ]%list.
Extract Inlined Constant items_of_state_61 => "assert false".

Definition items_of_state_62 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 17; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_62 => "assert false".

Definition items_of_state_63 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 18; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_63 => "assert false".

Definition items_of_state_64 : list item :=
  [ {| prod_item := Prod'atomic_obj'5; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_64 => "assert false".

Definition items_of_state_65 : list item :=
  [ {| prod_item := Prod'atomic_obj'5; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_65 => "assert false".

Definition items_of_state_66 : list item :=
  [ {| prod_item := Prod'obj'4; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_66 => "assert false".

Definition items_of_state_68 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 1; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_68 => "assert false".

Definition items_of_state_69 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'atomic_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_21 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_21 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_21 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_21 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_21 |};
    {| prod_item := Prod'obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_21 |};
    {| prod_item := Prod'prog'0; dot_pos_item := 2; lookaheads_item := lookahead_set_3 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_20 |} ]%list.
Extract Inlined Constant items_of_state_69 => "assert false".

Definition items_of_state_70 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 3; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_70 => "assert false".

Definition items_of_state_71 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 4; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_71 => "assert false".

Definition items_of_state (s:state) : list item :=
  match s with
  | Init Init'0 => items_of_state_0
  | Ninit Nis'1 => items_of_state_1
  | Ninit Nis'2 => items_of_state_2
  | Ninit Nis'3 => items_of_state_3
  | Ninit Nis'4 => items_of_state_4
  | Ninit Nis'5 => items_of_state_5
  | Ninit Nis'6 => items_of_state_6
  | Ninit Nis'7 => items_of_state_7
  | Ninit Nis'8 => items_of_state_8
  | Ninit Nis'9 => items_of_state_9
  | Ninit Nis'10 => items_of_state_10
  | Ninit Nis'11 => items_of_state_11
  | Ninit Nis'12 => items_of_state_12
  | Ninit Nis'13 => items_of_state_13
  | Ninit Nis'14 => items_of_state_14
  | Ninit Nis'15 => items_of_state_15
  | Ninit Nis'16 => items_of_state_16
  | Ninit Nis'17 => items_of_state_17
  | Ninit Nis'18 => items_of_state_18
  | Ninit Nis'19 => items_of_state_19
  | Ninit Nis'20 => items_of_state_20
  | Ninit Nis'21 => items_of_state_21
  | Ninit Nis'22 => items_of_state_22
  | Ninit Nis'23 => items_of_state_23
  | Ninit Nis'24 => items_of_state_24
  | Ninit Nis'25 => items_of_state_25
  | Ninit Nis'26 => items_of_state_26
  | Ninit Nis'27 => items_of_state_27
  | Ninit Nis'28 => items_of_state_28
  | Ninit Nis'29 => items_of_state_29
  | Ninit Nis'30 => items_of_state_30
  | Ninit Nis'31 => items_of_state_31
  | Ninit Nis'32 => items_of_state_32
  | Ninit Nis'33 => items_of_state_33
  | Ninit Nis'34 => items_of_state_34
  | Ninit Nis'35 => items_of_state_35
  | Ninit Nis'36 => items_of_state_36
  | Ninit Nis'37 => items_of_state_37
  | Ninit Nis'38 => items_of_state_38
  | Ninit Nis'39 => items_of_state_39
  | Ninit Nis'40 => items_of_state_40
  | Ninit Nis'41 => items_of_state_41
  | Ninit Nis'42 => items_of_state_42
  | Ninit Nis'43 => items_of_state_43
  | Ninit Nis'44 => items_of_state_44
  | Ninit Nis'45 => items_of_state_45
  | Ninit Nis'46 => items_of_state_46
  | Ninit Nis'47 => items_of_state_47
  | Ninit Nis'48 => items_of_state_48
  | Ninit Nis'49 => items_of_state_49
  | Ninit Nis'50 => items_of_state_50
  | Ninit Nis'51 => items_of_state_51
  | Ninit Nis'52 => items_of_state_52
  | Ninit Nis'53 => items_of_state_53
  | Ninit Nis'54 => items_of_state_54
  | Ninit Nis'55 => items_of_state_55
  | Ninit Nis'56 => items_of_state_56
  | Ninit Nis'57 => items_of_state_57
  | Ninit Nis'58 => items_of_state_58
  | Ninit Nis'59 => items_of_state_59
  | Ninit Nis'60 => items_of_state_60
  | Ninit Nis'61 => items_of_state_61
  | Ninit Nis'62 => items_of_state_62
  | Ninit Nis'63 => items_of_state_63
  | Ninit Nis'64 => items_of_state_64
  | Ninit Nis'65 => items_of_state_65
  | Ninit Nis'66 => items_of_state_66
  | Ninit Nis'68 => items_of_state_68
  | Ninit Nis'69 => items_of_state_69
  | Ninit Nis'70 => items_of_state_70
  | Ninit Nis'71 => items_of_state_71
  end.
Extract Constant items_of_state => "fun _ -> assert false".

Definition N_of_state (s:state) : N :=
  match s with
  | Init Init'0 => 0%N
  | Ninit Nis'1 => 1%N
  | Ninit Nis'2 => 2%N
  | Ninit Nis'3 => 3%N
  | Ninit Nis'4 => 4%N
  | Ninit Nis'5 => 5%N
  | Ninit Nis'6 => 6%N
  | Ninit Nis'7 => 7%N
  | Ninit Nis'8 => 8%N
  | Ninit Nis'9 => 9%N
  | Ninit Nis'10 => 10%N
  | Ninit Nis'11 => 11%N
  | Ninit Nis'12 => 12%N
  | Ninit Nis'13 => 13%N
  | Ninit Nis'14 => 14%N
  | Ninit Nis'15 => 15%N
  | Ninit Nis'16 => 16%N
  | Ninit Nis'17 => 17%N
  | Ninit Nis'18 => 18%N
  | Ninit Nis'19 => 19%N
  | Ninit Nis'20 => 20%N
  | Ninit Nis'21 => 21%N
  | Ninit Nis'22 => 22%N
  | Ninit Nis'23 => 23%N
  | Ninit Nis'24 => 24%N
  | Ninit Nis'25 => 25%N
  | Ninit Nis'26 => 26%N
  | Ninit Nis'27 => 27%N
  | Ninit Nis'28 => 28%N
  | Ninit Nis'29 => 29%N
  | Ninit Nis'30 => 30%N
  | Ninit Nis'31 => 31%N
  | Ninit Nis'32 => 32%N
  | Ninit Nis'33 => 33%N
  | Ninit Nis'34 => 34%N
  | Ninit Nis'35 => 35%N
  | Ninit Nis'36 => 36%N
  | Ninit Nis'37 => 37%N
  | Ninit Nis'38 => 38%N
  | Ninit Nis'39 => 39%N
  | Ninit Nis'40 => 40%N
  | Ninit Nis'41 => 41%N
  | Ninit Nis'42 => 42%N
  | Ninit Nis'43 => 43%N
  | Ninit Nis'44 => 44%N
  | Ninit Nis'45 => 45%N
  | Ninit Nis'46 => 46%N
  | Ninit Nis'47 => 47%N
  | Ninit Nis'48 => 48%N
  | Ninit Nis'49 => 49%N
  | Ninit Nis'50 => 50%N
  | Ninit Nis'51 => 51%N
  | Ninit Nis'52 => 52%N
  | Ninit Nis'53 => 53%N
  | Ninit Nis'54 => 54%N
  | Ninit Nis'55 => 55%N
  | Ninit Nis'56 => 56%N
  | Ninit Nis'57 => 57%N
  | Ninit Nis'58 => 58%N
  | Ninit Nis'59 => 59%N
  | Ninit Nis'60 => 60%N
  | Ninit Nis'61 => 61%N
  | Ninit Nis'62 => 62%N
  | Ninit Nis'63 => 63%N
  | Ninit Nis'64 => 64%N
  | Ninit Nis'65 => 65%N
  | Ninit Nis'66 => 66%N
  | Ninit Nis'68 => 68%N
  | Ninit Nis'69 => 69%N
  | Ninit Nis'70 => 70%N
  | Ninit Nis'71 => 71%N
  end.
End Aut.

Module MenhirLibParser := MenhirLib.Main.Make Aut.
Theorem safe:
  MenhirLibParser.safe_validator tt = true.
Proof eq_refl true<:MenhirLibParser.safe_validator tt = true.

Theorem complete:
  MenhirLibParser.complete_validator tt = true.
Proof eq_refl true<:MenhirLibParser.complete_validator tt = true.

Definition prog : nat -> MenhirLibParser.Inter.buffer -> MenhirLibParser.Inter.parse_result        (Cst.obj * Cst.obj) := MenhirLibParser.parse safe Aut.Init'0.

Theorem prog_correct (log_fuel : nat) (buffer : MenhirLibParser.Inter.buffer):
  match prog log_fuel buffer with
  | MenhirLibParser.Inter.Parsed_pr sem buffer_new =>
      exists word (tree : Gram.parse_tree (NT prog'nt) word),
        buffer = MenhirLibParser.Inter.app_buf word buffer_new /\
        Gram.pt_sem tree = sem
  | _ => True
  end.
Proof. apply MenhirLibParser.parse_correct with (init:=Aut.Init'0). Qed.

Theorem prog_complete (log_fuel : nat) (word : list token) (buffer_end : MenhirLibParser.Inter.buffer) :
  forall tree : Gram.parse_tree (NT prog'nt) word,
  match prog log_fuel (MenhirLibParser.Inter.app_buf word buffer_end) with
  | MenhirLibParser.Inter.Fail_pr => False
  | MenhirLibParser.Inter.Parsed_pr output_res buffer_end_res =>
      output_res = Gram.pt_sem tree /\
      buffer_end_res = buffer_end /\ (Gram.pt_size tree <= PeanoNat.Nat.pow 2 log_fuel)%nat
  | MenhirLibParser.Inter.Timeout_pr => (PeanoNat.Nat.pow 2 log_fuel < Gram.pt_size tree)%nat
  end.
Proof. apply MenhirLibParser.parse_complete with (init:=Aut.Init'0); exact complete. Qed.




Extract Constant loc => "Lexing.position * Lexing.position".
