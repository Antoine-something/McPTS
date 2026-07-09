  

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
| VAR :        (loc*string)%type -> token
| TYPE :        (loc)%type -> token
| RPAREN :        (loc)%type -> token
| PI :        (loc)%type -> token
| LPAREN :        (loc)%type -> token
| LET :        (loc)%type -> token
| LAMBDA :        (loc)%type -> token
| KIND :        (loc)%type -> token
| EOF :        (loc)%type -> token
| DOT :        (loc)%type -> token
| DEF_TYPE :        (loc)%type -> token
| DEF_EXP :        (loc)%type -> token
| COLONEQ :        (loc)%type -> token
| COLON :        (loc)%type -> token
| ARROW :        (loc)%type -> token.

Module Import Gram <: MenhirLib.Grammar.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Inductive terminal' : Set :=
| ARROW't
| COLON't
| COLONEQ't
| DEF_EXP't
| DEF_TYPE't
| DOT't
| EOF't
| KIND't
| LAMBDA't
| LET't
| LPAREN't
| PI't
| RPAREN't
| TYPE't
| VAR't.
Definition terminal := terminal'.

Global Program Instance terminalNum : MenhirLib.Alphabet.Numbered terminal :=
  { inj := fun x => match x return _ with
    | ARROW't => 1%positive
    | COLON't => 2%positive
    | COLONEQ't => 3%positive
    | DEF_EXP't => 4%positive
    | DEF_TYPE't => 5%positive
    | DOT't => 6%positive
    | EOF't => 7%positive
    | KIND't => 8%positive
    | LAMBDA't => 9%positive
    | LET't => 10%positive
    | LPAREN't => 11%positive
    | PI't => 12%positive
    | RPAREN't => 13%positive
    | TYPE't => 14%positive
    | VAR't => 15%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => ARROW't
    | 2%positive => COLON't
    | 3%positive => COLONEQ't
    | 4%positive => DEF_EXP't
    | 5%positive => DEF_TYPE't
    | 6%positive => DOT't
    | 7%positive => EOF't
    | 8%positive => KIND't
    | 9%positive => LAMBDA't
    | 10%positive => LET't
    | 11%positive => LPAREN't
    | 12%positive => PI't
    | 13%positive => RPAREN't
    | 14%positive => TYPE't
    | 15%positive => VAR't
    | _ => ARROW't
    end)%Z;
    inj_bound := 15%positive }.
Global Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| ann_obj'nt
| app_obj'nt
| atomic_obj'nt
| define_defns'nt
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
    | define_defns'nt => 4%positive
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
    | 4%positive => define_defns'nt
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
  | VAR't =>        (loc*string)%type
  | TYPE't =>        (loc)%type
  | RPAREN't =>        (loc)%type
  | PI't =>        (loc)%type
  | LPAREN't =>        (loc)%type
  | LET't =>        (loc)%type
  | LAMBDA't =>        (loc)%type
  | KIND't =>        (loc)%type
  | EOF't =>        (loc)%type
  | DOT't =>        (loc)%type
  | DEF_TYPE't =>        (loc)%type
  | DEF_EXP't =>        (loc)%type
  | COLONEQ't =>        (loc)%type
  | COLON't =>        (loc)%type
  | ARROW't =>        (loc)%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | sort'nt =>       (Cst.obj)%type
  | prog'nt =>        (Cst.obj * Cst.obj)%type
  | params'nt =>       (list (string * Cst.obj))%type
  | param'nt =>       (string * Cst.obj)%type
  | obj'nt =>       (Cst.obj)%type
  | define_defns'nt =>       (Cst.obj)%type
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
  | VAR _ => VAR't
  | TYPE _ => TYPE't
  | RPAREN _ => RPAREN't
  | PI _ => PI't
  | LPAREN _ => LPAREN't
  | LET _ => LET't
  | LAMBDA _ => LAMBDA't
  | KIND _ => KIND't
  | EOF _ => EOF't
  | DOT _ => DOT't
  | DEF_TYPE _ => DEF_TYPE't
  | DEF_EXP _ => DEF_EXP't
  | COLONEQ _ => COLONEQ't
  | COLON _ => COLON't
  | ARROW _ => ARROW't
  end.

Definition token_sem (tok : token) : symbol_semantic_type (T (token_term tok)) :=
  match tok with
  | VAR x => x
  | TYPE x => x
  | RPAREN x => x
  | PI x => x
  | LPAREN x => x
  | LET x => x
  | LAMBDA x => x
  | KIND x => x
  | EOF x => x
  | DOT x => x
  | DEF_TYPE x => x
  | DEF_EXP x => x
  | COLONEQ x => x
  | COLON x => x
  | ARROW x => x
  end.

Inductive production' : Set :=
| Prod'sort'1
| Prod'sort'0
| Prod'prog'0
| Prod'params'1
| Prod'params'0
| Prod'param'0
| Prod'obj'2
| Prod'obj'1
| Prod'obj'0
| Prod'define_defns'3
| Prod'define_defns'2
| Prod'define_defns'1
| Prod'define_defns'0
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
    | Prod'obj'2 => 7%positive
    | Prod'obj'1 => 8%positive
    | Prod'obj'0 => 9%positive
    | Prod'define_defns'3 => 10%positive
    | Prod'define_defns'2 => 11%positive
    | Prod'define_defns'1 => 12%positive
    | Prod'define_defns'0 => 13%positive
    | Prod'atomic_obj'2 => 14%positive
    | Prod'atomic_obj'1 => 15%positive
    | Prod'atomic_obj'0 => 16%positive
    | Prod'app_obj'1 => 17%positive
    | Prod'app_obj'0 => 18%positive
    | Prod'ann_obj'0 => 19%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'sort'1
    | 2%positive => Prod'sort'0
    | 3%positive => Prod'prog'0
    | 4%positive => Prod'params'1
    | 5%positive => Prod'params'0
    | 6%positive => Prod'param'0
    | 7%positive => Prod'obj'2
    | 8%positive => Prod'obj'1
    | 9%positive => Prod'obj'0
    | 10%positive => Prod'define_defns'3
    | 11%positive => Prod'define_defns'2
    | 12%positive => Prod'define_defns'1
    | 13%positive => Prod'define_defns'0
    | 14%positive => Prod'atomic_obj'2
    | 15%positive => Prod'atomic_obj'1
    | 16%positive => Prod'atomic_obj'0
    | 17%positive => Prod'app_obj'1
    | 18%positive => Prod'app_obj'0
    | 19%positive => Prod'ann_obj'0
    | _ => Prod'sort'1
    end)%Z;
    inj_bound := 19%positive }.
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
    (atomic_obj'nt, [T VAR't]%list)
    (fun x =>
             ( Cst.var (snd x) )
)
  | Prod'atomic_obj'2 => box
    (atomic_obj'nt, [T RPAREN't; NT obj'nt; T LPAREN't]%list)
    (fun _3 obj _1 =>
obj
)
  | Prod'define_defns'0 => box
    (define_defns'nt, [NT define_defns'nt; T DOT't; NT param'nt; T DEF_TYPE't]%list)
    (fun define_defns _3 param _1 =>
                                                ( 
      Cst.pi (fst param) Cst.s_knd Cst.s_knd (snd param) define_defns
   )
)
  | Prod'define_defns'1 => box
    (define_defns'nt, [NT define_defns'nt; T DOT't; NT param'nt; T DEF_EXP't]%list)
    (fun define_defns _3 param _1 =>
                                               ( 
      Cst.pi (fst param) Cst.s_typ Cst.s_knd (snd param) define_defns
   )
)
  | Prod'define_defns'2 => box
    (define_defns'nt, [NT define_defns'nt; T DOT't; NT obj'nt; T COLONEQ't; NT param'nt; T LET't]%list)
    (fun define_defns _5 obj _3 param _1 =>
                                                             (
      Cst.pi "#is_var" Cst.s_knd Cst.s_knd 
      (
        Cst.pi "#_" Cst.s_typ Cst.s_knd (snd param) Cst.s_typ
      ) 
      (
        Cst.pi (fst param) Cst.s_typ Cst.s_knd (Cst.app (Cst.var "#is_var") obj) define_defns
      )
    )
)
  | Prod'define_defns'3 => box
    (define_defns'nt, []%list)
    (
    ( Cst.s_typ )
)
  | Prod'obj'0 => box
    (obj'nt, [NT obj'nt; T ARROW't; NT sort'nt; T COLON't; NT params'nt; T PI't]%list)
    (fun obj _5 s _3 params _1 =>
                                                  ( List.fold_left (fun acc arg => Cst.pi (fst arg) Cst.s_typ s (snd arg) acc) params obj )
)
  | Prod'obj'1 => box
    (obj'nt, [NT ann_obj'nt; T ARROW't; NT sort'nt; T COLON't; NT params'nt; T LAMBDA't]%list)
    (fun ann_obj _5 s _3 params _1 =>
                                                          ( 
    fst (
      List.fold_left (
        fun acc arg => (
          Cst.fn (fst arg) Cst.s_typ s (snd arg) (snd acc) (fst acc),
          Cst.pi (fst arg) Cst.s_typ s (snd arg) (snd acc) 
        ) 
      ) params ann_obj
    ))
)
  | Prod'obj'2 => box
    (obj'nt, [NT app_obj'nt]%list)
    (fun app_obj =>
app_obj
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
    (prog'nt, [T EOF't; NT define_defns'nt]%list)
    (fun _2 define_defns =>
                           ( (define_defns, Cst.s_knd) )
)
  | Prod'sort'0 => box
    (sort'nt, [T TYPE't]%list)
    (fun _1 =>
          ( Cst.s_typ )
)
  | Prod'sort'1 => box
    (sort'nt, [T KIND't]%list)
    (fun _1 =>
          ( Cst.s_knd )
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
  | define_defns'nt => true
  | atomic_obj'nt => false
  | app_obj'nt => false
  | ann_obj'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | sort'nt => [TYPE't; KIND't]%list
  | prog'nt => [LET't; EOF't; DEF_TYPE't; DEF_EXP't]%list
  | params'nt => [LPAREN't]%list
  | param'nt => [LPAREN't]%list
  | obj'nt => [VAR't; TYPE't; PI't; LPAREN't; LAMBDA't; KIND't]%list
  | define_defns'nt => [LET't; DEF_TYPE't; DEF_EXP't]%list
  | atomic_obj'nt => [VAR't; TYPE't; LPAREN't; KIND't]%list
  | app_obj'nt => [VAR't; TYPE't; LPAREN't; KIND't]%list
  | ann_obj'nt => [LPAREN't]%list
  end.

Inductive noninitstate' : Set :=
| Nis'51
| Nis'50
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
    | Nis'51 => 1%positive
    | Nis'50 => 2%positive
    | Nis'48 => 3%positive
    | Nis'47 => 4%positive
    | Nis'46 => 5%positive
    | Nis'45 => 6%positive
    | Nis'44 => 7%positive
    | Nis'43 => 8%positive
    | Nis'42 => 9%positive
    | Nis'41 => 10%positive
    | Nis'40 => 11%positive
    | Nis'39 => 12%positive
    | Nis'38 => 13%positive
    | Nis'37 => 14%positive
    | Nis'36 => 15%positive
    | Nis'35 => 16%positive
    | Nis'34 => 17%positive
    | Nis'33 => 18%positive
    | Nis'32 => 19%positive
    | Nis'31 => 20%positive
    | Nis'30 => 21%positive
    | Nis'29 => 22%positive
    | Nis'28 => 23%positive
    | Nis'27 => 24%positive
    | Nis'26 => 25%positive
    | Nis'25 => 26%positive
    | Nis'24 => 27%positive
    | Nis'23 => 28%positive
    | Nis'22 => 29%positive
    | Nis'21 => 30%positive
    | Nis'20 => 31%positive
    | Nis'19 => 32%positive
    | Nis'18 => 33%positive
    | Nis'17 => 34%positive
    | Nis'16 => 35%positive
    | Nis'15 => 36%positive
    | Nis'14 => 37%positive
    | Nis'13 => 38%positive
    | Nis'12 => 39%positive
    | Nis'11 => 40%positive
    | Nis'10 => 41%positive
    | Nis'9 => 42%positive
    | Nis'8 => 43%positive
    | Nis'7 => 44%positive
    | Nis'6 => 45%positive
    | Nis'5 => 46%positive
    | Nis'4 => 47%positive
    | Nis'3 => 48%positive
    | Nis'2 => 49%positive
    | Nis'1 => 50%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'51
    | 2%positive => Nis'50
    | 3%positive => Nis'48
    | 4%positive => Nis'47
    | 5%positive => Nis'46
    | 6%positive => Nis'45
    | 7%positive => Nis'44
    | 8%positive => Nis'43
    | 9%positive => Nis'42
    | 10%positive => Nis'41
    | 11%positive => Nis'40
    | 12%positive => Nis'39
    | 13%positive => Nis'38
    | 14%positive => Nis'37
    | 15%positive => Nis'36
    | 16%positive => Nis'35
    | 17%positive => Nis'34
    | 18%positive => Nis'33
    | 19%positive => Nis'32
    | 20%positive => Nis'31
    | 21%positive => Nis'30
    | 22%positive => Nis'29
    | 23%positive => Nis'28
    | 24%positive => Nis'27
    | 25%positive => Nis'26
    | 26%positive => Nis'25
    | 27%positive => Nis'24
    | 28%positive => Nis'23
    | 29%positive => Nis'22
    | 30%positive => Nis'21
    | 31%positive => Nis'20
    | 32%positive => Nis'19
    | 33%positive => Nis'18
    | 34%positive => Nis'17
    | 35%positive => Nis'16
    | 36%positive => Nis'15
    | 37%positive => Nis'14
    | 38%positive => Nis'13
    | 39%positive => Nis'12
    | 40%positive => Nis'11
    | 41%positive => Nis'10
    | 42%positive => Nis'9
    | 43%positive => Nis'8
    | 44%positive => Nis'7
    | 45%positive => Nis'6
    | 46%positive => Nis'5
    | 47%positive => Nis'4
    | 48%positive => Nis'3
    | 49%positive => Nis'2
    | 50%positive => Nis'1
    | _ => Nis'51
    end)%Z;
    inj_bound := 50%positive }.
Global Instance NonInitStateAlph : MenhirLib.Alphabet.Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T LET't
  | Nis'2 => T LPAREN't
  | Nis'3 => T VAR't
  | Nis'4 => T COLON't
  | Nis'5 => T VAR't
  | Nis'6 => T TYPE't
  | Nis'7 => T PI't
  | Nis'8 => NT params'nt
  | Nis'9 => T COLON't
  | Nis'10 => T KIND't
  | Nis'11 => NT sort'nt
  | Nis'12 => T ARROW't
  | Nis'13 => T LPAREN't
  | Nis'14 => T LAMBDA't
  | Nis'15 => NT params'nt
  | Nis'16 => T COLON't
  | Nis'17 => NT sort'nt
  | Nis'18 => T ARROW't
  | Nis'19 => T LPAREN't
  | Nis'20 => NT sort'nt
  | Nis'21 => NT obj'nt
  | Nis'22 => T COLON't
  | Nis'23 => NT obj'nt
  | Nis'24 => T RPAREN't
  | Nis'25 => NT atomic_obj'nt
  | Nis'26 => NT app_obj'nt
  | Nis'27 => NT atomic_obj'nt
  | Nis'28 => NT ann_obj'nt
  | Nis'29 => NT param'nt
  | Nis'30 => NT param'nt
  | Nis'31 => NT obj'nt
  | Nis'32 => T RPAREN't
  | Nis'33 => NT obj'nt
  | Nis'34 => NT obj'nt
  | Nis'35 => T RPAREN't
  | Nis'36 => NT param'nt
  | Nis'37 => T COLONEQ't
  | Nis'38 => NT obj'nt
  | Nis'39 => T DOT't
  | Nis'40 => T DEF_TYPE't
  | Nis'41 => NT param'nt
  | Nis'42 => T DOT't
  | Nis'43 => T DEF_EXP't
  | Nis'44 => NT param'nt
  | Nis'45 => T DOT't
  | Nis'46 => NT define_defns'nt
  | Nis'47 => NT define_defns'nt
  | Nis'48 => NT define_defns'nt
  | Nis'50 => NT define_defns'nt
  | Nis'51 => T EOF't
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
    | LET't => Shift_act Nis'1 (eq_refl _)
    | EOF't => Reduce_act Prod'define_defns'3
    | DEF_TYPE't => Shift_act Nis'40 (eq_refl _)
    | DEF_EXP't => Shift_act Nis'43 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'2 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'3 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'3 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'4 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'4 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | PI't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LAMBDA't => Shift_act Nis'14 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'5 => Default_reduce_act Prod'atomic_obj'1
  | Ninit Nis'6 => Default_reduce_act Prod'sort'0
  | Ninit Nis'7 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'8 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | COLON't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'9 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'10 => Default_reduce_act Prod'sort'1
  | Ninit Nis'11 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ARROW't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | PI't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LAMBDA't => Shift_act Nis'14 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | PI't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LAMBDA't => Shift_act Nis'14 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'15 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | COLON't => Shift_act Nis'16 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'16 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'17 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ARROW't => Shift_act Nis'18 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'19 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'19 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | PI't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LAMBDA't => Shift_act Nis'14 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'20 => Default_reduce_act Prod'atomic_obj'0
  | Ninit Nis'21 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'22 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'22 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | PI't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LAMBDA't => Shift_act Nis'14 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'23 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'24 => Default_reduce_act Prod'ann_obj'0
  | Ninit Nis'25 => Default_reduce_act Prod'app_obj'1
  | Ninit Nis'26 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | RPAREN't => Reduce_act Prod'obj'2
    | PI't => Reduce_act Prod'obj'2
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LET't => Reduce_act Prod'obj'2
    | LAMBDA't => Reduce_act Prod'obj'2
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | EOF't => Reduce_act Prod'obj'2
    | DOT't => Reduce_act Prod'obj'2
    | DEF_TYPE't => Reduce_act Prod'obj'2
    | DEF_EXP't => Reduce_act Prod'obj'2
    | COLONEQ't => Reduce_act Prod'obj'2
    | COLON't => Reduce_act Prod'obj'2
    | ARROW't => Reduce_act Prod'obj'2
    end)
  | Ninit Nis'27 => Default_reduce_act Prod'app_obj'0
  | Ninit Nis'28 => Default_reduce_act Prod'obj'1
  | Ninit Nis'29 => Default_reduce_act Prod'params'0
  | Ninit Nis'30 => Default_reduce_act Prod'params'1
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'32 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'32 => Default_reduce_act Prod'atomic_obj'2
  | Ninit Nis'33 => Default_reduce_act Prod'obj'0
  | Ninit Nis'34 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'35 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'35 => Default_reduce_act Prod'param'0
  | Ninit Nis'36 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLONEQ't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'37 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'5 (eq_refl _)
    | TYPE't => Shift_act Nis'6 (eq_refl _)
    | PI't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'13 (eq_refl _)
    | LAMBDA't => Shift_act Nis'14 (eq_refl _)
    | KIND't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'38 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'39 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'39 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LET't => Shift_act Nis'1 (eq_refl _)
    | EOF't => Reduce_act Prod'define_defns'3
    | DEF_TYPE't => Shift_act Nis'40 (eq_refl _)
    | DEF_EXP't => Shift_act Nis'43 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'40 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'41 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'42 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'42 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LET't => Shift_act Nis'1 (eq_refl _)
    | EOF't => Reduce_act Prod'define_defns'3
    | DEF_TYPE't => Shift_act Nis'40 (eq_refl _)
    | DEF_EXP't => Shift_act Nis'43 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'43 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'2 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'44 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'45 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'45 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LET't => Shift_act Nis'1 (eq_refl _)
    | EOF't => Reduce_act Prod'define_defns'3
    | DEF_TYPE't => Shift_act Nis'40 (eq_refl _)
    | DEF_EXP't => Shift_act Nis'43 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'46 => Default_reduce_act Prod'define_defns'1
  | Ninit Nis'47 => Default_reduce_act Prod'define_defns'0
  | Ninit Nis'48 => Default_reduce_act Prod'define_defns'2
  | Ninit Nis'50 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EOF't => Shift_act Nis'51 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'51 => Default_reduce_act Prod'prog'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, prog'nt => None  | Init Init'0, define_defns'nt => Some (exist _ Nis'50 (eq_refl _))
  | Ninit Nis'1, param'nt => Some (exist _ Nis'36 (eq_refl _))
  | Ninit Nis'4, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'4, obj'nt => Some (exist _ Nis'34 (eq_refl _))
  | Ninit Nis'4, atomic_obj'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'4, app_obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'7, params'nt => Some (exist _ Nis'8 (eq_refl _))
  | Ninit Nis'7, param'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'8, param'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'9, sort'nt => Some (exist _ Nis'11 (eq_refl _))
  | Ninit Nis'12, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'12, obj'nt => Some (exist _ Nis'33 (eq_refl _))
  | Ninit Nis'12, atomic_obj'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'12, app_obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'13, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'13, obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'13, atomic_obj'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'13, app_obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'14, params'nt => Some (exist _ Nis'15 (eq_refl _))
  | Ninit Nis'14, param'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'15, param'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'16, sort'nt => Some (exist _ Nis'17 (eq_refl _))
  | Ninit Nis'18, ann_obj'nt => Some (exist _ Nis'28 (eq_refl _))
  | Ninit Nis'19, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'19, obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'19, atomic_obj'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'19, app_obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'22, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'22, obj'nt => Some (exist _ Nis'23 (eq_refl _))
  | Ninit Nis'22, atomic_obj'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'22, app_obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'26, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'26, atomic_obj'nt => Some (exist _ Nis'27 (eq_refl _))
  | Ninit Nis'37, sort'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'37, obj'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'37, atomic_obj'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'37, app_obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'39, define_defns'nt => Some (exist _ Nis'48 (eq_refl _))
  | Ninit Nis'40, param'nt => Some (exist _ Nis'41 (eq_refl _))
  | Ninit Nis'42, define_defns'nt => Some (exist _ Nis'47 (eq_refl _))
  | Ninit Nis'43, param'nt => Some (exist _ Nis'44 (eq_refl _))
  | Ninit Nis'45, define_defns'nt => Some (exist _ Nis'46 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []%list
  | Nis'2 => []%list
  | Nis'3 => [T LPAREN't]%list
  | Nis'4 => [T VAR't; T LPAREN't]%list
  | Nis'5 => []%list
  | Nis'6 => []%list
  | Nis'7 => []%list
  | Nis'8 => [T PI't]%list
  | Nis'9 => [NT params'nt; T PI't]%list
  | Nis'10 => []%list
  | Nis'11 => [T COLON't; NT params'nt; T PI't]%list
  | Nis'12 => [NT sort'nt; T COLON't; NT params'nt; T PI't]%list
  | Nis'13 => []%list
  | Nis'14 => []%list
  | Nis'15 => [T LAMBDA't]%list
  | Nis'16 => [NT params'nt; T LAMBDA't]%list
  | Nis'17 => [T COLON't; NT params'nt; T LAMBDA't]%list
  | Nis'18 => [NT sort'nt; T COLON't; NT params'nt; T LAMBDA't]%list
  | Nis'19 => []%list
  | Nis'20 => []%list
  | Nis'21 => [T LPAREN't]%list
  | Nis'22 => [NT obj'nt; T LPAREN't]%list
  | Nis'23 => [T COLON't; NT obj'nt; T LPAREN't]%list
  | Nis'24 => [NT obj'nt; T COLON't; NT obj'nt; T LPAREN't]%list
  | Nis'25 => []%list
  | Nis'26 => []%list
  | Nis'27 => [NT app_obj'nt]%list
  | Nis'28 => [T ARROW't; NT sort'nt; T COLON't; NT params'nt; T LAMBDA't]%list
  | Nis'29 => [NT params'nt]%list
  | Nis'30 => []%list
  | Nis'31 => [T LPAREN't]%list
  | Nis'32 => [NT obj'nt; T LPAREN't]%list
  | Nis'33 => [T ARROW't; NT sort'nt; T COLON't; NT params'nt; T PI't]%list
  | Nis'34 => [T COLON't; T VAR't; T LPAREN't]%list
  | Nis'35 => [NT obj'nt; T COLON't; T VAR't; T LPAREN't]%list
  | Nis'36 => [T LET't]%list
  | Nis'37 => [NT param'nt; T LET't]%list
  | Nis'38 => [T COLONEQ't; NT param'nt; T LET't]%list
  | Nis'39 => [NT obj'nt; T COLONEQ't; NT param'nt; T LET't]%list
  | Nis'40 => []%list
  | Nis'41 => [T DEF_TYPE't]%list
  | Nis'42 => [NT param'nt; T DEF_TYPE't]%list
  | Nis'43 => []%list
  | Nis'44 => [T DEF_EXP't]%list
  | Nis'45 => [NT param'nt; T DEF_EXP't]%list
  | Nis'46 => [T DOT't; NT param'nt; T DEF_EXP't]%list
  | Nis'47 => [T DOT't; NT param'nt; T DEF_TYPE't]%list
  | Nis'48 => [T DOT't; NT obj'nt; T COLONEQ't; NT param'nt; T LET't]%list
  | Nis'50 => []%list
  | Nis'51 => [NT define_defns'nt]%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'39 | Ninit Nis'42 | Ninit Nis'45 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Ninit Nis'1 | Ninit Nis'7 | Ninit Nis'8 | Ninit Nis'14 | Ninit Nis'15 | Ninit Nis'40 | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Ninit Nis'2 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'3 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'4 | Ninit Nis'12 | Ninit Nis'13 | Ninit Nis'19 | Ninit Nis'22 | Ninit Nis'26 | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Ninit Nis'4 | Ninit Nis'9 | Ninit Nis'12 | Ninit Nis'13 | Ninit Nis'16 | Ninit Nis'19 | Ninit Nis'22 | Ninit Nis'26 | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'4 | Ninit Nis'12 | Ninit Nis'13 | Ninit Nis'19 | Ninit Nis'22 | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'7 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'9 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'14 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'15 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'16 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'18 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'19 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'21 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'22 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'23 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Ninit Nis'26 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'7 | Ninit Nis'14 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'15 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Ninit Nis'31 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'12 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Ninit Nis'4 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'34 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'1 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Ninit Nis'36 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition state_set_32 (s:state) : bool :=
  match s with
  | Ninit Nis'38 => true
  | _ => false
  end.
Extract Inlined Constant state_set_32 => "assert false".

Definition state_set_33 (s:state) : bool :=
  match s with
  | Ninit Nis'40 => true
  | _ => false
  end.
Extract Inlined Constant state_set_33 => "assert false".

Definition state_set_34 (s:state) : bool :=
  match s with
  | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_34 => "assert false".

Definition state_set_35 (s:state) : bool :=
  match s with
  | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_35 => "assert false".

Definition state_set_36 (s:state) : bool :=
  match s with
  | Ninit Nis'44 => true
  | _ => false
  end.
Extract Inlined Constant state_set_36 => "assert false".

Definition state_set_37 (s:state) : bool :=
  match s with
  | Ninit Nis'45 => true
  | _ => false
  end.
Extract Inlined Constant state_set_37 => "assert false".

Definition state_set_38 (s:state) : bool :=
  match s with
  | Ninit Nis'42 => true
  | _ => false
  end.
Extract Inlined Constant state_set_38 => "assert false".

Definition state_set_39 (s:state) : bool :=
  match s with
  | Ninit Nis'39 => true
  | _ => false
  end.
Extract Inlined Constant state_set_39 => "assert false".

Definition state_set_40 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_40 => "assert false".

Definition state_set_41 (s:state) : bool :=
  match s with
  | Ninit Nis'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_41 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [state_set_1]%list
  | Nis'2 => [state_set_2]%list
  | Nis'3 => [state_set_3; state_set_2]%list
  | Nis'4 => [state_set_4; state_set_3; state_set_2]%list
  | Nis'5 => [state_set_5]%list
  | Nis'6 => [state_set_6]%list
  | Nis'7 => [state_set_7]%list
  | Nis'8 => [state_set_8; state_set_7]%list
  | Nis'9 => [state_set_9; state_set_8; state_set_7]%list
  | Nis'10 => [state_set_6]%list
  | Nis'11 => [state_set_10; state_set_9; state_set_8; state_set_7]%list
  | Nis'12 => [state_set_11; state_set_10; state_set_9; state_set_8; state_set_7]%list
  | Nis'13 => [state_set_5]%list
  | Nis'14 => [state_set_7]%list
  | Nis'15 => [state_set_12; state_set_7]%list
  | Nis'16 => [state_set_13; state_set_12; state_set_7]%list
  | Nis'17 => [state_set_14; state_set_13; state_set_12; state_set_7]%list
  | Nis'18 => [state_set_15; state_set_14; state_set_13; state_set_12; state_set_7]%list
  | Nis'19 => [state_set_16]%list
  | Nis'20 => [state_set_5]%list
  | Nis'21 => [state_set_17; state_set_16]%list
  | Nis'22 => [state_set_18; state_set_17; state_set_16]%list
  | Nis'23 => [state_set_19; state_set_18; state_set_17; state_set_16]%list
  | Nis'24 => [state_set_20; state_set_19; state_set_18; state_set_17; state_set_16]%list
  | Nis'25 => [state_set_7]%list
  | Nis'26 => [state_set_7]%list
  | Nis'27 => [state_set_21; state_set_7]%list
  | Nis'28 => [state_set_16; state_set_15; state_set_14; state_set_13; state_set_12; state_set_7]%list
  | Nis'29 => [state_set_23; state_set_22]%list
  | Nis'30 => [state_set_22]%list
  | Nis'31 => [state_set_24; state_set_5]%list
  | Nis'32 => [state_set_25; state_set_24; state_set_5]%list
  | Nis'33 => [state_set_26; state_set_11; state_set_10; state_set_9; state_set_8; state_set_7]%list
  | Nis'34 => [state_set_27; state_set_4; state_set_3; state_set_2]%list
  | Nis'35 => [state_set_28; state_set_27; state_set_4; state_set_3; state_set_2]%list
  | Nis'36 => [state_set_29; state_set_1]%list
  | Nis'37 => [state_set_30; state_set_29; state_set_1]%list
  | Nis'38 => [state_set_31; state_set_30; state_set_29; state_set_1]%list
  | Nis'39 => [state_set_32; state_set_31; state_set_30; state_set_29; state_set_1]%list
  | Nis'40 => [state_set_1]%list
  | Nis'41 => [state_set_33; state_set_1]%list
  | Nis'42 => [state_set_34; state_set_33; state_set_1]%list
  | Nis'43 => [state_set_1]%list
  | Nis'44 => [state_set_35; state_set_1]%list
  | Nis'45 => [state_set_36; state_set_35; state_set_1]%list
  | Nis'46 => [state_set_37; state_set_36; state_set_35; state_set_1]%list
  | Nis'47 => [state_set_38; state_set_34; state_set_33; state_set_1]%list
  | Nis'48 => [state_set_39; state_set_32; state_set_31; state_set_30; state_set_29; state_set_1]%list
  | Nis'50 => [state_set_40]%list
  | Nis'51 => [state_set_41; state_set_40]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition lookahead_set_1 : list terminal :=
  [EOF't]%list.
Extract Inlined Constant lookahead_set_1 => "assert false".

Definition lookahead_set_2 : list terminal :=
  [VAR't; TYPE't; RPAREN't; PI't; LPAREN't; LET't; LAMBDA't; KIND't; EOF't; DOT't; DEF_TYPE't; DEF_EXP't; COLONEQ't; COLON't; ARROW't]%list.
Extract Inlined Constant lookahead_set_2 => "assert false".

Definition lookahead_set_3 : list terminal :=
  [COLONEQ't]%list.
Extract Inlined Constant lookahead_set_3 => "assert false".

Definition lookahead_set_4 : list terminal :=
  [LPAREN't; DOT't; COLONEQ't; COLON't]%list.
Extract Inlined Constant lookahead_set_4 => "assert false".

Definition lookahead_set_5 : list terminal :=
  [VAR't; TYPE't; RPAREN't; LPAREN't; KIND't]%list.
Extract Inlined Constant lookahead_set_5 => "assert false".

Definition lookahead_set_6 : list terminal :=
  [RPAREN't]%list.
Extract Inlined Constant lookahead_set_6 => "assert false".

Definition lookahead_set_7 : list terminal :=
  [VAR't; TYPE't; RPAREN't; LPAREN't; KIND't; DOT't; COLON't]%list.
Extract Inlined Constant lookahead_set_7 => "assert false".

Definition lookahead_set_8 : list terminal :=
  [VAR't; TYPE't; RPAREN't; LPAREN't; KIND't; DOT't; COLON't; ARROW't]%list.
Extract Inlined Constant lookahead_set_8 => "assert false".

Definition lookahead_set_9 : list terminal :=
  [RPAREN't; DOT't; COLON't]%list.
Extract Inlined Constant lookahead_set_9 => "assert false".

Definition lookahead_set_10 : list terminal :=
  [LPAREN't; COLON't]%list.
Extract Inlined Constant lookahead_set_10 => "assert false".

Definition lookahead_set_11 : list terminal :=
  [ARROW't]%list.
Extract Inlined Constant lookahead_set_11 => "assert false".

Definition lookahead_set_12 : list terminal :=
  [VAR't; TYPE't; LPAREN't; KIND't; COLON't]%list.
Extract Inlined Constant lookahead_set_12 => "assert false".

Definition lookahead_set_13 : list terminal :=
  [COLON't]%list.
Extract Inlined Constant lookahead_set_13 => "assert false".

Definition lookahead_set_14 : list terminal :=
  [VAR't; TYPE't; LPAREN't; KIND't; DOT't]%list.
Extract Inlined Constant lookahead_set_14 => "assert false".

Definition lookahead_set_15 : list terminal :=
  [DOT't]%list.
Extract Inlined Constant lookahead_set_15 => "assert false".

Definition items_of_state_0 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'prog'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ]%list.
Extract Inlined Constant items_of_state_0 => "assert false".

Definition items_of_state_1 : list item :=
  [ {| prod_item := Prod'define_defns'2; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_1 => "assert false".

Definition items_of_state_2 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_2 => "assert false".

Definition items_of_state_3 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_3 => "assert false".

Definition items_of_state_4 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'param'0; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_4 => "assert false".

Definition items_of_state_5 : list item :=
  [ {| prod_item := Prod'atomic_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_5 => "assert false".

Definition items_of_state_6 : list item :=
  [ {| prod_item := Prod'sort'0; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_6 => "assert false".

Definition items_of_state_7 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_7 => "assert false".

Definition items_of_state_8 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'0; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_8 => "assert false".

Definition items_of_state_9 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_9 => "assert false".

Definition items_of_state_10 : list item :=
  [ {| prod_item := Prod'sort'1; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_10 => "assert false".

Definition items_of_state_11 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_11 => "assert false".

Definition items_of_state_12 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 5; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_12 => "assert false".

Definition items_of_state_13 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_13 => "assert false".

Definition items_of_state_14 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_14 => "assert false".

Definition items_of_state_15 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 2; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'params'0; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_15 => "assert false".

Definition items_of_state_16 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 3; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |} ]%list.
Extract Inlined Constant items_of_state_16 => "assert false".

Definition items_of_state_17 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 4; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_17 => "assert false".

Definition items_of_state_18 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 5; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_18 => "assert false".

Definition items_of_state_19 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |} ]%list.
Extract Inlined Constant items_of_state_19 => "assert false".

Definition items_of_state_20 : list item :=
  [ {| prod_item := Prod'atomic_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_20 => "assert false".

Definition items_of_state_21 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_21 => "assert false".

Definition items_of_state_22 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_22 => "assert false".

Definition items_of_state_23 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_23 => "assert false".

Definition items_of_state_24 : list item :=
  [ {| prod_item := Prod'ann_obj'0; dot_pos_item := 5; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_24 => "assert false".

Definition items_of_state_25 : list item :=
  [ {| prod_item := Prod'app_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_25 => "assert false".

Definition items_of_state_26 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_26 => "assert false".

Definition items_of_state_27 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_27 => "assert false".

Definition items_of_state_28 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 6; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_28 => "assert false".

Definition items_of_state_29 : list item :=
  [ {| prod_item := Prod'params'0; dot_pos_item := 2; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_29 => "assert false".

Definition items_of_state_30 : list item :=
  [ {| prod_item := Prod'params'1; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_30 => "assert false".

Definition items_of_state_31 : list item :=
  [ {| prod_item := Prod'atomic_obj'2; dot_pos_item := 2; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_31 => "assert false".

Definition items_of_state_32 : list item :=
  [ {| prod_item := Prod'atomic_obj'2; dot_pos_item := 3; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_32 => "assert false".

Definition items_of_state_33 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 6; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_33 => "assert false".

Definition items_of_state_34 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 4; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_34 => "assert false".

Definition items_of_state_35 : list item :=
  [ {| prod_item := Prod'param'0; dot_pos_item := 5; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_35 => "assert false".

Definition items_of_state_36 : list item :=
  [ {| prod_item := Prod'define_defns'2; dot_pos_item := 2; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_36 => "assert false".

Definition items_of_state_37 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'atomic_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'define_defns'2; dot_pos_item := 3; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |};
    {| prod_item := Prod'sort'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'sort'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |} ]%list.
Extract Inlined Constant items_of_state_37 => "assert false".

Definition items_of_state_38 : list item :=
  [ {| prod_item := Prod'define_defns'2; dot_pos_item := 4; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_38 => "assert false".

Definition items_of_state_39 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'2; dot_pos_item := 5; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_39 => "assert false".

Definition items_of_state_40 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |} ]%list.
Extract Inlined Constant items_of_state_40 => "assert false".

Definition items_of_state_41 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 2; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_41 => "assert false".

Definition items_of_state_42 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'0; dot_pos_item := 3; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_42 => "assert false".

Definition items_of_state_43 : list item :=
  [ {| prod_item := Prod'define_defns'1; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'param'0; dot_pos_item := 0; lookaheads_item := lookahead_set_15 |} ]%list.
Extract Inlined Constant items_of_state_43 => "assert false".

Definition items_of_state_44 : list item :=
  [ {| prod_item := Prod'define_defns'1; dot_pos_item := 2; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_44 => "assert false".

Definition items_of_state_45 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'1; dot_pos_item := 3; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'define_defns'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_45 => "assert false".

Definition items_of_state_46 : list item :=
  [ {| prod_item := Prod'define_defns'1; dot_pos_item := 4; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_46 => "assert false".

Definition items_of_state_47 : list item :=
  [ {| prod_item := Prod'define_defns'0; dot_pos_item := 4; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_47 => "assert false".

Definition items_of_state_48 : list item :=
  [ {| prod_item := Prod'define_defns'2; dot_pos_item := 6; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_48 => "assert false".

Definition items_of_state_50 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 1; lookaheads_item := lookahead_set_2 |} ]%list.
Extract Inlined Constant items_of_state_50 => "assert false".

Definition items_of_state_51 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 2; lookaheads_item := lookahead_set_2 |} ]%list.
Extract Inlined Constant items_of_state_51 => "assert false".

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
  | Ninit Nis'50 => items_of_state_50
  | Ninit Nis'51 => items_of_state_51
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
  | Ninit Nis'50 => 50%N
  | Ninit Nis'51 => 51%N
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
