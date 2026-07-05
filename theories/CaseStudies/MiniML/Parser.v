  

From Coq Require Import List String.

From McPTS.CaseStudies.MiniML Require Import Frontend.

Parameter loc : Type.



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
| LAMBDA :        (loc)%type -> token
| INT :        (loc*nat)%type -> token
| EOF :        (loc)%type -> token
| END :        (loc)%type -> token
| DOT :        (loc)%type -> token
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
| DOT't
| END't
| EOF't
| INT't
| LAMBDA't
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
    | DOT't => 6%positive
    | END't => 7%positive
    | EOF't => 8%positive
    | INT't => 9%positive
    | LAMBDA't => 10%positive
    | LPAREN't => 11%positive
    | NAT't => 12%positive
    | PI't => 13%positive
    | REC't => 14%positive
    | RETURN't => 15%positive
    | RPAREN't => 16%positive
    | SUCC't => 17%positive
    | TYPE't => 18%positive
    | VAR't => 19%positive
    | ZERO't => 20%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => ARROW't
    | 2%positive => BAR't
    | 3%positive => COLON't
    | 4%positive => COMMA't
    | 5%positive => DARROW't
    | 6%positive => DOT't
    | 7%positive => END't
    | 8%positive => EOF't
    | 9%positive => INT't
    | 10%positive => LAMBDA't
    | 11%positive => LPAREN't
    | 12%positive => NAT't
    | 13%positive => PI't
    | 14%positive => REC't
    | 15%positive => RETURN't
    | 16%positive => RPAREN't
    | 17%positive => SUCC't
    | 18%positive => TYPE't
    | 19%positive => VAR't
    | 20%positive => ZERO't
    | _ => ARROW't
    end)%Z;
    inj_bound := 20%positive }.
Global Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| ann_obj'nt
| app_obj'nt
| atomic_obj'nt
| obj'nt
| param'nt
| params'nt
| prog'nt.
Definition nonterminal := nonterminal'.

Global Program Instance nonterminalNum : MenhirLib.Alphabet.Numbered nonterminal :=
  { inj := fun x => match x return _ with
    | ann_obj'nt => 1%positive
    | app_obj'nt => 2%positive
    | atomic_obj'nt => 3%positive
    | obj'nt => 4%positive
    | param'nt => 5%positive
    | params'nt => 6%positive
    | prog'nt => 7%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => ann_obj'nt
    | 2%positive => app_obj'nt
    | 3%positive => atomic_obj'nt
    | 4%positive => obj'nt
    | 5%positive => param'nt
    | 6%positive => params'nt
    | 7%positive => prog'nt
    | _ => ann_obj'nt
    end)%Z;
    inj_bound := 7%positive }.
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
  | LAMBDA't =>        (loc)%type
  | INT't =>        (loc*nat)%type
  | EOF't =>        (loc)%type
  | END't =>        (loc)%type
  | DOT't =>        (loc)%type
  | DARROW't =>        (loc)%type
  | COMMA't =>        (loc)%type
  | COLON't =>        (loc)%type
  | BAR't =>        (loc)%type
  | ARROW't =>        (loc)%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | prog'nt =>        (Cst.obj * Cst.obj)%type
  | params'nt =>       (list (string * Cst.obj))%type
  | param'nt =>       (string * Cst.obj)%type
  | obj'nt =>       (Cst.obj)%type
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
  | LAMBDA _ => LAMBDA't
  | INT _ => INT't
  | EOF _ => EOF't
  | END _ => END't
  | DOT _ => DOT't
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
  | LAMBDA x => x
  | INT x => x
  | EOF x => x
  | END x => x
  | DOT x => x
  | DARROW x => x
  | COMMA x => x
  | COLON x => x
  | BAR x => x
  | ARROW x => x
  end.

Inductive production' : Set :=
| Prod'prog'0
| Prod'params'1
| Prod'params'0
| Prod'param'0
| Prod'obj'4
| Prod'obj'3
| Prod'obj'2
| Prod'obj'1
| Prod'obj'0
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
    | Prod'prog'0 => 1%positive
    | Prod'params'1 => 2%positive
    | Prod'params'0 => 3%positive
    | Prod'param'0 => 4%positive
    | Prod'obj'4 => 5%positive
    | Prod'obj'3 => 6%positive
    | Prod'obj'2 => 7%positive
    | Prod'obj'1 => 8%positive
    | Prod'obj'0 => 9%positive
    | Prod'atomic_obj'4 => 10%positive
    | Prod'atomic_obj'3 => 11%positive
    | Prod'atomic_obj'2 => 12%positive
    | Prod'atomic_obj'1 => 13%positive
    | Prod'atomic_obj'0 => 14%positive
    | Prod'app_obj'1 => 15%positive
    | Prod'app_obj'0 => 16%positive
    | Prod'ann_obj'0 => 17%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'prog'0
    | 2%positive => Prod'params'1
    | 3%positive => Prod'params'0
    | 4%positive => Prod'param'0
    | 5%positive => Prod'obj'4
    | 6%positive => Prod'obj'3
    | 7%positive => Prod'obj'2
    | 8%positive => Prod'obj'1
    | 9%positive => Prod'obj'0
    | 10%positive => Prod'atomic_obj'4
    | 11%positive => Prod'atomic_obj'3
    | 12%positive => Prod'atomic_obj'2
    | 13%positive => Prod'atomic_obj'1
    | 14%positive => Prod'atomic_obj'0
    | 15%positive => Prod'app_obj'1
    | 16%positive => Prod'app_obj'0
    | 17%positive => Prod'ann_obj'0
    | _ => Prod'prog'0
    end)%Z;
    inj_bound := 17%positive }.
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
    (atomic_obj'nt, [T TYPE't]%list)
    (fun _1 =>
          ( Cst.st )
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
    (atomic_obj'nt, [T VAR't]%list)
    (fun x =>
             ( Cst.var (snd x) )
)
  | Prod'atomic_obj'4 => box
    (atomic_obj'nt, [T RPAREN't; NT obj'nt; T LPAREN't]%list)
    (fun _3 obj _1 =>
obj
)
  | Prod'obj'0 => box
    (obj'nt, [NT obj'nt; T ARROW't; NT params'nt; T PI't]%list)
    (fun obj _3 params _1 =>
                                   ( List.fold_left (fun acc arg => Cst.pi (fst arg) (snd arg) acc) params obj )
)
  | Prod'obj'1 => box
    (obj'nt, [NT ann_obj'nt; T ARROW't; NT param'nt; T LAMBDA't]%list)
    (fun ann_obj _3 param _1 =>
                                          ( Cst.fn (fst param) (snd param) (snd ann_obj) (fst ann_obj) )
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
  | prog'nt => false
  | params'nt => false
  | param'nt => false
  | obj'nt => false
  | atomic_obj'nt => false
  | app_obj'nt => false
  | ann_obj'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | prog'nt => [ZERO't; VAR't; TYPE't; SUCC't; REC't; PI't; NAT't; LPAREN't; LAMBDA't]%list
  | params'nt => [LPAREN't]%list
  | param'nt => [LPAREN't]%list
  | obj'nt => [ZERO't; VAR't; TYPE't; SUCC't; REC't; PI't; NAT't; LPAREN't; LAMBDA't]%list
  | atomic_obj'nt => [ZERO't; VAR't; TYPE't; NAT't; LPAREN't]%list
  | app_obj'nt => [ZERO't; VAR't; TYPE't; NAT't; LPAREN't]%list
  | ann_obj'nt => [LPAREN't]%list
  end.

Inductive noninitstate' : Set :=
| Nis'55
| Nis'54
| Nis'53
| Nis'52
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
    | Nis'55 => 1%positive
    | Nis'54 => 2%positive
    | Nis'53 => 3%positive
    | Nis'52 => 4%positive
    | Nis'50 => 5%positive
    | Nis'49 => 6%positive
    | Nis'48 => 7%positive
    | Nis'47 => 8%positive
    | Nis'46 => 9%positive
    | Nis'45 => 10%positive
    | Nis'44 => 11%positive
    | Nis'43 => 12%positive
    | Nis'42 => 13%positive
    | Nis'41 => 14%positive
    | Nis'40 => 15%positive
    | Nis'39 => 16%positive
    | Nis'38 => 17%positive
    | Nis'37 => 18%positive
    | Nis'36 => 19%positive
    | Nis'35 => 20%positive
    | Nis'34 => 21%positive
    | Nis'33 => 22%positive
    | Nis'32 => 23%positive
    | Nis'31 => 24%positive
    | Nis'30 => 25%positive
    | Nis'29 => 26%positive
    | Nis'28 => 27%positive
    | Nis'27 => 28%positive
    | Nis'26 => 29%positive
    | Nis'25 => 30%positive
    | Nis'24 => 31%positive
    | Nis'23 => 32%positive
    | Nis'22 => 33%positive
    | Nis'21 => 34%positive
    | Nis'20 => 35%positive
    | Nis'19 => 36%positive
    | Nis'18 => 37%positive
    | Nis'17 => 38%positive
    | Nis'16 => 39%positive
    | Nis'15 => 40%positive
    | Nis'14 => 41%positive
    | Nis'13 => 42%positive
    | Nis'12 => 43%positive
    | Nis'11 => 44%positive
    | Nis'10 => 45%positive
    | Nis'9 => 46%positive
    | Nis'8 => 47%positive
    | Nis'7 => 48%positive
    | Nis'6 => 49%positive
    | Nis'5 => 50%positive
    | Nis'4 => 51%positive
    | Nis'3 => 52%positive
    | Nis'2 => 53%positive
    | Nis'1 => 54%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'55
    | 2%positive => Nis'54
    | 3%positive => Nis'53
    | 4%positive => Nis'52
    | 5%positive => Nis'50
    | 6%positive => Nis'49
    | 7%positive => Nis'48
    | 8%positive => Nis'47
    | 9%positive => Nis'46
    | 10%positive => Nis'45
    | 11%positive => Nis'44
    | 12%positive => Nis'43
    | 13%positive => Nis'42
    | 14%positive => Nis'41
    | 15%positive => Nis'40
    | 16%positive => Nis'39
    | 17%positive => Nis'38
    | 18%positive => Nis'37
    | 19%positive => Nis'36
    | 20%positive => Nis'35
    | 21%positive => Nis'34
    | 22%positive => Nis'33
    | 23%positive => Nis'32
    | 24%positive => Nis'31
    | 25%positive => Nis'30
    | 26%positive => Nis'29
    | 27%positive => Nis'28
    | 28%positive => Nis'27
    | 29%positive => Nis'26
    | 30%positive => Nis'25
    | 31%positive => Nis'24
    | 32%positive => Nis'23
    | 33%positive => Nis'22
    | 34%positive => Nis'21
    | 35%positive => Nis'20
    | 36%positive => Nis'19
    | 37%positive => Nis'18
    | 38%positive => Nis'17
    | 39%positive => Nis'16
    | 40%positive => Nis'15
    | 41%positive => Nis'14
    | 42%positive => Nis'13
    | 43%positive => Nis'12
    | 44%positive => Nis'11
    | 45%positive => Nis'10
    | 46%positive => Nis'9
    | 47%positive => Nis'8
    | 48%positive => Nis'7
    | 49%positive => Nis'6
    | 50%positive => Nis'5
    | 51%positive => Nis'4
    | 52%positive => Nis'3
    | 53%positive => Nis'2
    | 54%positive => Nis'1
    | _ => Nis'55
    end)%Z;
    inj_bound := 54%positive }.
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
  | Nis'12 => T LAMBDA't
  | Nis'13 => NT param'nt
  | Nis'14 => T ARROW't
  | Nis'15 => T LPAREN't
  | Nis'16 => NT obj'nt
  | Nis'17 => T COLON't
  | Nis'18 => NT obj'nt
  | Nis'19 => T RPAREN't
  | Nis'20 => NT atomic_obj'nt
  | Nis'21 => NT app_obj'nt
  | Nis'22 => NT atomic_obj'nt
  | Nis'23 => NT ann_obj'nt
  | Nis'24 => NT obj'nt
  | Nis'25 => T RPAREN't
  | Nis'26 => NT params'nt
  | Nis'27 => T ARROW't
  | Nis'28 => NT obj'nt
  | Nis'29 => NT param'nt
  | Nis'30 => NT param'nt
  | Nis'31 => NT obj'nt
  | Nis'32 => T RETURN't
  | Nis'33 => T VAR't
  | Nis'34 => T DOT't
  | Nis'35 => NT obj'nt
  | Nis'36 => T BAR't
  | Nis'37 => T ZERO't
  | Nis'38 => T DARROW't
  | Nis'39 => NT obj'nt
  | Nis'40 => T BAR't
  | Nis'41 => T SUCC't
  | Nis'42 => T VAR't
  | Nis'43 => T COMMA't
  | Nis'44 => T VAR't
  | Nis'45 => T DARROW't
  | Nis'46 => NT obj'nt
  | Nis'47 => T END't
  | Nis'48 => NT obj'nt
  | Nis'49 => T RPAREN't
  | Nis'50 => NT atomic_obj'nt
  | Nis'52 => NT obj'nt
  | Nis'53 => T COLON't
  | Nis'54 => NT obj'nt
  | Nis'55 => T EOF't
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
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Default_reduce_act Prod'atomic_obj'2
  | Ninit Nis'2 => Default_reduce_act Prod'atomic_obj'3
  | Ninit Nis'3 => Default_reduce_act Prod'atomic_obj'0
  | Ninit Nis'4 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
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
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
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
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
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
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ARROW't => Shift_act Nis'14 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'15 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'15 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'16 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'17 (eq_refl _)
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
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'19 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'19 => Default_reduce_act Prod'ann_obj'0
  | Ninit Nis'20 => Default_reduce_act Prod'app_obj'1
  | Ninit Nis'21 => Lookahead_act (fun terminal:terminal =>
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
    | LAMBDA't => Reduce_act Prod'obj'2
    | INT't => Reduce_act Prod'obj'2
    | EOF't => Reduce_act Prod'obj'2
    | END't => Reduce_act Prod'obj'2
    | DOT't => Reduce_act Prod'obj'2
    | DARROW't => Reduce_act Prod'obj'2
    | COMMA't => Reduce_act Prod'obj'2
    | COLON't => Reduce_act Prod'obj'2
    | BAR't => Reduce_act Prod'obj'2
    | ARROW't => Reduce_act Prod'obj'2
    end)
  | Ninit Nis'22 => Default_reduce_act Prod'app_obj'0
  | Ninit Nis'23 => Default_reduce_act Prod'obj'1
  | Ninit Nis'24 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'25 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'25 => Default_reduce_act Prod'param'0
  | Ninit Nis'26 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | ARROW't => Shift_act Nis'27 (eq_refl _)
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
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'28 => Default_reduce_act Prod'obj'0
  | Ninit Nis'29 => Default_reduce_act Prod'params'0
  | Ninit Nis'30 => Default_reduce_act Prod'params'1
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RETURN't => Shift_act Nis'32 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'32 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'33 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'33 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'34 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'35 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | BAR't => Shift_act Nis'36 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'36 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'37 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DARROW't => Shift_act Nis'38 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'38 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'39 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | BAR't => Shift_act Nis'40 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'40 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SUCC't => Shift_act Nis'41 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'41 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'42 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'42 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COMMA't => Shift_act Nis'43 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'43 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'44 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'44 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DARROW't => Shift_act Nis'45 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'45 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'46 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | END't => Shift_act Nis'47 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'47 => Default_reduce_act Prod'obj'3
  | Ninit Nis'48 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'49 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'49 => Default_reduce_act Prod'atomic_obj'4
  | Ninit Nis'50 => Default_reduce_act Prod'obj'4
  | Ninit Nis'52 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'53 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'53 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'4 (eq_refl _)
    | REC't => Shift_act Nis'7 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'5 (eq_refl _)
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'54 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EOF't => Shift_act Nis'55 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'55 => Default_reduce_act Prod'prog'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, prog'nt => None  | Init Init'0, obj'nt => Some (exist _ Nis'52 (eq_refl _))
  | Init Init'0, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Init Init'0, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'4, atomic_obj'nt => Some (exist _ Nis'50 (eq_refl _))
  | Ninit Nis'6, obj'nt => Some (exist _ Nis'48 (eq_refl _))
  | Ninit Nis'6, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'6, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'7, obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'7, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'7, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'8, params'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'8, param'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'11, obj'nt => Some (exist _ Nis'24 (eq_refl _))
  | Ninit Nis'11, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'11, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'12, param'nt => Some (exist _ Nis'13 (eq_refl _))
  | Ninit Nis'14, ann_obj'nt => Some (exist _ Nis'23 (eq_refl _))
  | Ninit Nis'15, obj'nt => Some (exist _ Nis'16 (eq_refl _))
  | Ninit Nis'15, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'15, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'17, obj'nt => Some (exist _ Nis'18 (eq_refl _))
  | Ninit Nis'17, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'17, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'21, atomic_obj'nt => Some (exist _ Nis'22 (eq_refl _))
  | Ninit Nis'26, param'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'27, obj'nt => Some (exist _ Nis'28 (eq_refl _))
  | Ninit Nis'27, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'27, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'34, obj'nt => Some (exist _ Nis'35 (eq_refl _))
  | Ninit Nis'34, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'34, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'38, obj'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'38, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'38, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'45, obj'nt => Some (exist _ Nis'46 (eq_refl _))
  | Ninit Nis'45, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'45, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'53, obj'nt => Some (exist _ Nis'54 (eq_refl _))
  | Ninit Nis'53, atomic_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'53, app_obj'nt => Some (exist _ Nis'21 (eq_refl _))
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
  | Nis'13 => [T LAMBDA't]%list
  | Nis'14 => [NT param'nt; T LAMBDA't]%list
  | Nis'15 => []%list
  | Nis'16 => [T LPAREN't]%list
  | Nis'17 => [NT obj'nt; T LPAREN't]%list
  | Nis'18 => [T COLON't; NT obj'nt; T LPAREN't]%list
  | Nis'19 => [NT obj'nt; T COLON't; NT obj'nt; T LPAREN't]%list
  | Nis'20 => []%list
  | Nis'21 => []%list
  | Nis'22 => [NT app_obj'nt]%list
  | Nis'23 => [T ARROW't; NT param'nt; T LAMBDA't]%list
  | Nis'24 => [T COLON't; T VAR't; T LPAREN't]%list
  | Nis'25 => [NT obj'nt; T COLON't; T VAR't; T LPAREN't]%list
  | Nis'26 => [T PI't]%list
  | Nis'27 => [NT params'nt; T PI't]%list
  | Nis'28 => [T ARROW't; NT params'nt; T PI't]%list
  | Nis'29 => [NT params'nt]%list
  | Nis'30 => []%list
  | Nis'31 => [T REC't]%list
  | Nis'32 => [NT obj'nt; T REC't]%list
  | Nis'33 => [T RETURN't; NT obj'nt; T REC't]%list
  | Nis'34 => [T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'35 => [T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'36 => [NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'37 => [T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'38 => [T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'39 => [T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'40 => [NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'41 => [T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'42 => [T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'43 => [T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'44 => [T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'45 => [T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'46 => [T DARROW't; T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'47 => [NT obj'nt; T DARROW't; T VAR't; T COMMA't; T VAR't; T SUCC't; T BAR't; NT obj'nt; T DARROW't; T ZERO't; T BAR't; NT obj'nt; T DOT't; T VAR't; T RETURN't; NT obj'nt; T REC't]%list
  | Nis'48 => [T LPAREN't]%list
  | Nis'49 => [NT obj'nt; T LPAREN't]%list
  | Nis'50 => [T SUCC't]%list
  | Nis'52 => []%list
  | Nis'53 => [NT obj'nt]%list
  | Nis'54 => [T COLON't; NT obj'nt]%list
  | Nis'55 => [NT obj'nt; T COLON't; NT obj'nt]%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'4 | Ninit Nis'6 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'15 | Ninit Nis'17 | Ninit Nis'21 | Ninit Nis'27 | Ninit Nis'34 | Ninit Nis'38 | Ninit Nis'45 | Ninit Nis'53 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'6 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'15 | Ninit Nis'17 | Ninit Nis'27 | Ninit Nis'34 | Ninit Nis'38 | Ninit Nis'45 | Ninit Nis'53 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'12 | Ninit Nis'26 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'9 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'10 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Ninit Nis'12 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'14 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'15 => true
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
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'18 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'21 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'24 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
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
  | Ninit Nis'7 => true
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
  | Ninit Nis'32 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'33 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'34 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'35 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Ninit Nis'36 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Ninit Nis'38 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'39 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'40 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'42 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition state_set_32 (s:state) : bool :=
  match s with
  | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_32 => "assert false".

Definition state_set_33 (s:state) : bool :=
  match s with
  | Ninit Nis'44 => true
  | _ => false
  end.
Extract Inlined Constant state_set_33 => "assert false".

Definition state_set_34 (s:state) : bool :=
  match s with
  | Ninit Nis'45 => true
  | _ => false
  end.
Extract Inlined Constant state_set_34 => "assert false".

Definition state_set_35 (s:state) : bool :=
  match s with
  | Ninit Nis'46 => true
  | _ => false
  end.
Extract Inlined Constant state_set_35 => "assert false".

Definition state_set_36 (s:state) : bool :=
  match s with
  | Ninit Nis'6 => true
  | _ => false
  end.
Extract Inlined Constant state_set_36 => "assert false".

Definition state_set_37 (s:state) : bool :=
  match s with
  | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_37 => "assert false".

Definition state_set_38 (s:state) : bool :=
  match s with
  | Ninit Nis'4 => true
  | _ => false
  end.
Extract Inlined Constant state_set_38 => "assert false".

Definition state_set_39 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_39 => "assert false".

Definition state_set_40 (s:state) : bool :=
  match s with
  | Ninit Nis'52 => true
  | _ => false
  end.
Extract Inlined Constant state_set_40 => "assert false".

Definition state_set_41 (s:state) : bool :=
  match s with
  | Ninit Nis'53 => true
  | _ => false
  end.
Extract Inlined Constant state_set_41 => "assert false".

Definition state_set_42 (s:state) : bool :=
  match s with
  | Ninit Nis'54 => true
  | _ => false
  end.
Extract Inlined Constant state_set_42 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [state_set_1]%list
  | Nis'2 => [state_set_1]%list
  | Nis'3 => [state_set_1]%list
  | Nis'4 => [state_set_2]%list
  | Nis'5 => [state_set_1]%list
  | Nis'6 => [state_set_1]%list
  | Nis'7 => [state_set_2]%list
  | Nis'8 => [state_set_2]%list
  | Nis'9 => [state_set_3]%list
  | Nis'10 => [state_set_4; state_set_3]%list
  | Nis'11 => [state_set_5; state_set_4; state_set_3]%list
  | Nis'12 => [state_set_2]%list
  | Nis'13 => [state_set_6; state_set_2]%list
  | Nis'14 => [state_set_7; state_set_6; state_set_2]%list
  | Nis'15 => [state_set_8]%list
  | Nis'16 => [state_set_9; state_set_8]%list
  | Nis'17 => [state_set_10; state_set_9; state_set_8]%list
  | Nis'18 => [state_set_11; state_set_10; state_set_9; state_set_8]%list
  | Nis'19 => [state_set_12; state_set_11; state_set_10; state_set_9; state_set_8]%list
  | Nis'20 => [state_set_2]%list
  | Nis'21 => [state_set_2]%list
  | Nis'22 => [state_set_13; state_set_2]%list
  | Nis'23 => [state_set_8; state_set_7; state_set_6; state_set_2]%list
  | Nis'24 => [state_set_14; state_set_5; state_set_4; state_set_3]%list
  | Nis'25 => [state_set_15; state_set_14; state_set_5; state_set_4; state_set_3]%list
  | Nis'26 => [state_set_16; state_set_2]%list
  | Nis'27 => [state_set_17; state_set_16; state_set_2]%list
  | Nis'28 => [state_set_18; state_set_17; state_set_16; state_set_2]%list
  | Nis'29 => [state_set_17; state_set_16]%list
  | Nis'30 => [state_set_16]%list
  | Nis'31 => [state_set_19; state_set_2]%list
  | Nis'32 => [state_set_20; state_set_19; state_set_2]%list
  | Nis'33 => [state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'34 => [state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'35 => [state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'36 => [state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'37 => [state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'38 => [state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'39 => [state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'40 => [state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'41 => [state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'42 => [state_set_30; state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'43 => [state_set_31; state_set_30; state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'44 => [state_set_32; state_set_31; state_set_30; state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'45 => [state_set_33; state_set_32; state_set_31; state_set_30; state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'46 => [state_set_34; state_set_33; state_set_32; state_set_31; state_set_30; state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'47 => [state_set_35; state_set_34; state_set_33; state_set_32; state_set_31; state_set_30; state_set_29; state_set_28; state_set_27; state_set_26; state_set_25; state_set_24; state_set_23; state_set_22; state_set_21; state_set_20; state_set_19; state_set_2]%list
  | Nis'48 => [state_set_36; state_set_1]%list
  | Nis'49 => [state_set_37; state_set_36; state_set_1]%list
  | Nis'50 => [state_set_38; state_set_2]%list
  | Nis'52 => [state_set_39]%list
  | Nis'53 => [state_set_40; state_set_39]%list
  | Nis'54 => [state_set_41; state_set_40; state_set_39]%list
  | Nis'55 => [state_set_42; state_set_41; state_set_40; state_set_39]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition lookahead_set_1 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; COLON't]%list.
Extract Inlined Constant lookahead_set_1 => "assert false".

Definition lookahead_set_2 : list terminal :=
  [COLON't]%list.
Extract Inlined Constant lookahead_set_2 => "assert false".

Definition lookahead_set_3 : list terminal :=
  [ZERO't; VAR't; TYPE't; SUCC't; RPAREN't; RETURN't; REC't; PI't; NAT't; LPAREN't; LAMBDA't; INT't; EOF't; END't; DOT't; DARROW't; COMMA't; COLON't; BAR't; ARROW't]%list.
Extract Inlined Constant lookahead_set_3 => "assert false".

Definition lookahead_set_4 : list terminal :=
  [ZERO't; VAR't; TYPE't; RPAREN't; RETURN't; NAT't; LPAREN't; EOF't; END't; COLON't; BAR't]%list.
Extract Inlined Constant lookahead_set_4 => "assert false".

Definition lookahead_set_5 : list terminal :=
  [RPAREN't; RETURN't; EOF't; END't; COLON't; BAR't]%list.
Extract Inlined Constant lookahead_set_5 => "assert false".

Definition lookahead_set_6 : list terminal :=
  [ZERO't; VAR't; TYPE't; RPAREN't; NAT't; LPAREN't]%list.
Extract Inlined Constant lookahead_set_6 => "assert false".

Definition lookahead_set_7 : list terminal :=
  [RPAREN't]%list.
Extract Inlined Constant lookahead_set_7 => "assert false".

Definition lookahead_set_8 : list terminal :=
  [ZERO't; VAR't; TYPE't; RETURN't; NAT't; LPAREN't]%list.
Extract Inlined Constant lookahead_set_8 => "assert false".

Definition lookahead_set_9 : list terminal :=
  [RETURN't]%list.
Extract Inlined Constant lookahead_set_9 => "assert false".

Definition lookahead_set_10 : list terminal :=
  [LPAREN't; ARROW't]%list.
Extract Inlined Constant lookahead_set_10 => "assert false".

Definition lookahead_set_11 : list terminal :=
  [ARROW't]%list.
Extract Inlined Constant lookahead_set_11 => "assert false".

Definition lookahead_set_12 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; BAR't]%list.
Extract Inlined Constant lookahead_set_12 => "assert false".

Definition lookahead_set_13 : list terminal :=
  [BAR't]%list.
Extract Inlined Constant lookahead_set_13 => "assert false".

Definition lookahead_set_14 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; END't]%list.
Extract Inlined Constant lookahead_set_14 => "assert false".

Definition lookahead_set_15 : list terminal :=
  [END't]%list.
Extract Inlined Constant lookahead_set_15 => "assert false".

Definition lookahead_set_16 : list terminal :=
  [ZERO't; VAR't; TYPE't; NAT't; LPAREN't; EOF't]%list.
Extract Inlined Constant lookahead_set_16 => "assert false".

Definition lookahead_set_17 : list terminal :=
  [EOF't]%list.
Extract Inlined Constant lookahead_set_17 => "assert false".

Definition items_of_state_0 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'prog'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_0 => "assert false".

Definition items_of_state_1 : list item :=
  [ {| prod_item := Prod'atomic_obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_1 => "assert false".

Definition items_of_state_2 : list item :=
  [ {| prod_item := Prod'atomic_obj'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_2 => "assert false".

Definition items_of_state_3 : list item :=
  [ {| prod_item := Prod'atomic_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_3 => "assert false".

Definition items_of_state_4 : list item :=
  [ {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_4 => "assert false".

Definition items_of_state_5 : list item :=
  [ {| prod_item := Prod'atomic_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_5 => "assert false".

Definition items_of_state_6 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_6 => "assert false".

Definition items_of_state_7 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_7 => "assert false".

Definition items_of_state_8 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_8 => "assert false".

Definition items_of_state_9 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_9 => "assert false".

Definition items_of_state_10 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 2; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_10 => "assert false".

Definition items_of_state_11 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'param'0; dot_pos_item := 3; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_11 => "assert false".

Definition items_of_state_12 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_12 => "assert false".

Definition items_of_state_13 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 2; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_13 => "assert false".

Definition items_of_state_14 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 3; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_14 => "assert false".

Definition items_of_state_15 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ]%list.
Extract Inlined Constant items_of_state_15 => "assert false".

Definition items_of_state_16 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_16 => "assert false".

Definition items_of_state_17 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_17 => "assert false".

Definition items_of_state_18 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_18 => "assert false".

Definition items_of_state_19 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 5; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_19 => "assert false".

Definition items_of_state_20 : list item :=
  [ {| prod_item := Prod'app_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_20 => "assert false".

Definition items_of_state_21 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_21 => "assert false".

Definition items_of_state_22 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_22 => "assert false".

Definition items_of_state_23 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 4; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_23 => "assert false".

Definition items_of_state_24 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 4; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_24 => "assert false".

Definition items_of_state_25 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 5; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_25 => "assert false".

Definition items_of_state_26 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'0; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_26 => "assert false".

Definition items_of_state_27 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_27 => "assert false".

Definition items_of_state_28 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_28 => "assert false".

Definition items_of_state_29 : list item :=
  [ {| prod_item := Prod'params'0; dot_pos_item := 2; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_29 => "assert false".

Definition items_of_state_30 : list item :=
  [ {| prod_item := Prod'params'1; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_30 => "assert false".

Definition items_of_state_31 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 2; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_31 => "assert false".

Definition items_of_state_32 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 3; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_32 => "assert false".

Definition items_of_state_33 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 4; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_33 => "assert false".

Definition items_of_state_34 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 5; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |} ]%list.
Extract Inlined Constant items_of_state_34 => "assert false".

Definition items_of_state_35 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 6; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_35 => "assert false".

Definition items_of_state_36 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 7; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_36 => "assert false".

Definition items_of_state_37 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 8; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_37 => "assert false".

Definition items_of_state_38 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 9; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |} ]%list.
Extract Inlined Constant items_of_state_38 => "assert false".

Definition items_of_state_39 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 10; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_39 => "assert false".

Definition items_of_state_40 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 11; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_40 => "assert false".

Definition items_of_state_41 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 12; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_41 => "assert false".

Definition items_of_state_42 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 13; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_42 => "assert false".

Definition items_of_state_43 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 14; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_43 => "assert false".

Definition items_of_state_44 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 15; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_44 => "assert false".

Definition items_of_state_45 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 16; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |} ]%list.
Extract Inlined Constant items_of_state_45 => "assert false".

Definition items_of_state_46 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 17; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_46 => "assert false".

Definition items_of_state_47 : list item :=
  [ {| prod_item := Prod'obj'3; dot_pos_item := 18; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_47 => "assert false".

Definition items_of_state_48 : list item :=
  [ {| prod_item := Prod'atomic_obj'4; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_48 => "assert false".

Definition items_of_state_49 : list item :=
  [ {| prod_item := Prod'atomic_obj'4; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_49 => "assert false".

Definition items_of_state_50 : list item :=
  [ {| prod_item := Prod'obj'4; dot_pos_item := 2; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_50 => "assert false".

Definition items_of_state_52 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 1; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_52 => "assert false".

Definition items_of_state_53 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'atomic_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_16 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_17 |};
    {| prod_item := Prod'prog'0; dot_pos_item := 2; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_53 => "assert false".

Definition items_of_state_54 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 3; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_54 => "assert false".

Definition items_of_state_55 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 4; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_55 => "assert false".

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
  | Ninit Nis'52 => items_of_state_52
  | Ninit Nis'53 => items_of_state_53
  | Ninit Nis'54 => items_of_state_54
  | Ninit Nis'55 => items_of_state_55
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
  | Ninit Nis'52 => 52%N
  | Ninit Nis'53 => 53%N
  | Ninit Nis'54 => 54%N
  | Ninit Nis'55 => 55%N
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
