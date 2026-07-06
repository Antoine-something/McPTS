open Alphabet
open Datatypes
open Frontend
open Grammar
open List
open Main
open Nat
open Specif

type __ = Obj.t

type loc = Lexing.position * Lexing.position

module Coq__1 : sig
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
 | LAMBDA of loc
 | INT of (loc * int)
 | EOF of loc
 | END of loc
 | DOT of loc
 | DARROW of loc
 | COMMA of loc
 | COLON of loc
 | BAR of loc
 | ARROW of loc
end
include module type of struct include Coq__1 end

module Gram :
 sig
  type terminal' =
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
  | ZERO't

  type terminal = terminal'

  val terminalNum : terminal coq_Numbered

  val coq_TerminalAlph : terminal coq_Alphabet

  type nonterminal' =
  | Coq_ann_obj'nt
  | Coq_app_obj'nt
  | Coq_atomic_obj'nt
  | Coq_obj'nt
  | Coq_param'nt
  | Coq_params'nt
  | Coq_prog'nt

  type nonterminal = nonterminal'

  val nonterminalNum : nonterminal coq_Numbered

  val coq_NonTerminalAlph : nonterminal coq_Alphabet

  type symbol =
  | T of terminal
  | NT of nonterminal

  val symbol_rect : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

  val coq_SymbolAlph : symbol coq_Alphabet

  type terminal_semantic_type = __

  type nonterminal_semantic_type = __

  type symbol_semantic_type = __

  type token = Coq__1.token

  val token_term : token -> terminal

  val token_sem : token -> symbol_semantic_type

  type production' =
  | Prod'prog'0
  | Prod'params'1
  | Prod'params'0
  | Prod'param'0
  | Prod'obj'4
  | Prod'obj'3
  | Prod'obj'2
  | Prod'obj'1
  | Prod'obj'0
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

  val productionNum : production coq_Numbered

  val coq_ProductionAlph : production coq_Alphabet

  val prod_contents :
    production -> (nonterminal * symbol list, symbol_semantic_type
    arrows_right) sigT

  val prod_lhs : production -> nonterminal

  val prod_rhs_rev : production -> symbol list

  val prod_action : production -> symbol_semantic_type arrows_right

  type parse_tree =
  | Terminal_pt of token
  | Non_terminal_pt of production * token list * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of symbol list * token list * parse_tree_list * symbol
     * token list * parse_tree

  val parse_tree_rect :
    (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1) ->
    symbol -> token list -> parse_tree -> 'a1

  val parse_tree_rec :
    (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1) ->
    symbol -> token list -> parse_tree -> 'a1

  val parse_tree_list_rect :
    'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol ->
    token list -> parse_tree -> 'a1) -> symbol list -> token list ->
    parse_tree_list -> 'a1

  val parse_tree_list_rec :
    'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol ->
    token list -> parse_tree -> 'a1) -> symbol list -> token list ->
    parse_tree_list -> 'a1

  val pt_sem : symbol -> token list -> parse_tree -> symbol_semantic_type

  val ptl_sem :
    symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1

  val pt_size : symbol -> token list -> parse_tree -> int

  val ptl_size : symbol list -> token list -> parse_tree_list -> int
 end
module Coq__2 : module type of struct include Gram end

module Aut :
 sig
  module Gram :
   sig
    type terminal' = Gram.terminal' =
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
    | ZERO't

    type terminal = terminal'

    val terminalNum : terminal coq_Numbered

    val coq_TerminalAlph : terminal coq_Alphabet

    type nonterminal' = Gram.nonterminal' =
    | Coq_ann_obj'nt
    | Coq_app_obj'nt
    | Coq_atomic_obj'nt
    | Coq_obj'nt
    | Coq_param'nt
    | Coq_params'nt
    | Coq_prog'nt

    type nonterminal = nonterminal'

    val nonterminalNum : nonterminal coq_Numbered

    val coq_NonTerminalAlph : nonterminal coq_Alphabet

    type symbol = Gram.symbol =
    | T of terminal
    | NT of nonterminal

    val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val coq_SymbolAlph : symbol coq_Alphabet

    type terminal_semantic_type = __

    type nonterminal_semantic_type = __

    type symbol_semantic_type = __

    type token = Coq__1.token

    val token_term : token -> terminal

    val token_sem : token -> symbol_semantic_type

    type production' = Gram.production' =
    | Prod'prog'0
    | Prod'params'1
    | Prod'params'0
    | Prod'param'0
    | Prod'obj'4
    | Prod'obj'3
    | Prod'obj'2
    | Prod'obj'1
    | Prod'obj'0
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

    val productionNum : production coq_Numbered

    val coq_ProductionAlph : production coq_Alphabet

    val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT

    val prod_lhs : production -> nonterminal

    val prod_rhs_rev : production -> symbol list

    val prod_action : production -> symbol_semantic_type arrows_right

    type parse_tree = Gram.parse_tree =
    | Terminal_pt of token
    | Non_terminal_pt of production * token list * parse_tree_list
    and parse_tree_list = Gram.parse_tree_list =
    | Nil_ptl
    | Cons_ptl of symbol list * token list * parse_tree_list * symbol
       * token list * parse_tree

    val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val pt_sem : symbol -> token list -> parse_tree -> symbol_semantic_type

    val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1

    val pt_size : symbol -> token list -> parse_tree -> int

    val ptl_size : symbol list -> token list -> parse_tree_list -> int
   end

  module GramDefs :
   sig
    type terminal' = Coq__2.terminal' =
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
    | ZERO't

    type terminal = terminal'

    val terminalNum : terminal coq_Numbered

    val coq_TerminalAlph : terminal coq_Alphabet

    type nonterminal' = Coq__2.nonterminal' =
    | Coq_ann_obj'nt
    | Coq_app_obj'nt
    | Coq_atomic_obj'nt
    | Coq_obj'nt
    | Coq_param'nt
    | Coq_params'nt
    | Coq_prog'nt

    type nonterminal = nonterminal'

    val nonterminalNum : nonterminal coq_Numbered

    val coq_NonTerminalAlph : nonterminal coq_Alphabet

    type symbol = Coq__2.symbol =
    | T of terminal
    | NT of nonterminal

    val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val coq_SymbolAlph : symbol coq_Alphabet

    type terminal_semantic_type = __

    type nonterminal_semantic_type = __

    type symbol_semantic_type = __

    type token = Coq__1.token

    val token_term : token -> terminal

    val token_sem : token -> symbol_semantic_type

    type production' = Coq__2.production' =
    | Prod'prog'0
    | Prod'params'1
    | Prod'params'0
    | Prod'param'0
    | Prod'obj'4
    | Prod'obj'3
    | Prod'obj'2
    | Prod'obj'1
    | Prod'obj'0
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

    val productionNum : production coq_Numbered

    val coq_ProductionAlph : production coq_Alphabet

    val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT

    val prod_lhs : production -> nonterminal

    val prod_rhs_rev : production -> symbol list

    val prod_action : production -> symbol_semantic_type arrows_right

    type parse_tree = Coq__2.parse_tree =
    | Terminal_pt of token
    | Non_terminal_pt of production * token list * parse_tree_list
    and parse_tree_list = Coq__2.parse_tree_list =
    | Nil_ptl
    | Cons_ptl of symbol list * token list * parse_tree_list * symbol
       * token list * parse_tree

    val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val pt_sem : symbol -> token list -> parse_tree -> symbol_semantic_type

    val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1

    val pt_size : symbol -> token list -> parse_tree -> int

    val ptl_size : symbol list -> token list -> parse_tree_list -> int
   end

  val nullable_nterm : Coq__2.nonterminal -> bool

  val first_nterm : Coq__2.nonterminal -> Coq__2.terminal list

  type noninitstate' =
  | Nis'56
  | Nis'55
  | Nis'54
  | Nis'53
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

  val noninitstateNum : noninitstate coq_Numbered

  val coq_NonInitStateAlph : noninitstate coq_Alphabet

  val last_symb_of_non_init_state : noninitstate -> Coq__2.symbol

  type initstate' =
  | Init'0

  type initstate = initstate'

  val initstateNum : initstate coq_Numbered

  val coq_InitStateAlph : initstate coq_Alphabet

  type state =
  | Init of initstate
  | Ninit of noninitstate

  val state_rect : (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1

  val state_rec : (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1

  val coq_StateAlph : state coq_Alphabet

  type lookahead_action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act

  val lookahead_action_rect :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> lookahead_action -> 'a1

  val lookahead_action_rec :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> lookahead_action -> 'a1

  type action =
  | Default_reduce_act of Gram.production
  | Lookahead_act of (Gram.terminal -> lookahead_action)

  val action_rect :
    (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) -> 'a1)
    -> action -> 'a1

  val action_rec :
    (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) -> 'a1)
    -> action -> 'a1

  type item = { prod_item : Gram.production; dot_pos_item : int;
                lookaheads_item : Gram.terminal list }

  val prod_item : item -> Gram.production

  val dot_pos_item : item -> int

  val lookaheads_item : item -> Gram.terminal list

  val start_nt : initstate -> Coq__2.nonterminal

  val action_table : state -> action

  val goto_table : state -> Coq__2.nonterminal -> noninitstate option

  val past_symb_of_non_init_state : noninitstate -> Coq__2.symbol list

  val past_state_of_non_init_state : noninitstate -> (state -> bool) list

  val items_of_state : state -> item list

  val coq_N_of_state : state -> int
 end

module MenhirLibParser :
 sig
  module Inter :
   sig
    module ValidSafe :
     sig
      val singleton_state_pred : Aut.state -> Aut.state -> bool

      val past_state_of_state : Aut.state -> (Aut.state -> bool) list

      val head_symbs_of_state : Aut.state -> Aut.Gram.symbol list

      val head_states_of_state : Aut.state -> (Aut.state -> bool) list

      val is_prefix : Aut.Gram.symbol list -> Aut.Gram.symbol list -> bool

      val is_prefix_pred :
        (Aut.state -> bool) list -> (Aut.state -> bool) list -> bool

      val is_state_valid_after_pop :
        Aut.state -> Aut.Gram.symbol list -> (Aut.state -> bool) list -> bool

      val is_safe : unit -> bool
     end

    type coq_Decidable = bool

    val decide : coq_Decidable -> bool

    val comparable_decidable_eq :
      'a1 coq_Comparable -> 'a1 -> 'a1 -> coq_Decidable

    val list_decidable_eq :
      ('a1 -> 'a1 -> coq_Decidable) -> 'a1 list -> 'a1 list -> coq_Decidable

    val cast : 'a1 -> 'a1 -> (unit -> coq_Decidable) -> 'a2 -> 'a2

    type buffer = __buffer Lazy.t
    and __buffer =
    | Buf_cons of Aut.Gram.token * buffer

    val buf_head : buffer -> Aut.Gram.token

    val buf_tail : buffer -> buffer

    val app_buf : Aut.Gram.token list -> buffer -> buffer

    type noninitstate_type = Aut.Gram.symbol_semantic_type

    type stack = (Aut.noninitstate, noninitstate_type) sigT list

    val state_of_stack : Aut.initstate -> stack -> Aut.state

    val state_stack_of_stack :
      Aut.initstate -> stack -> (Aut.state -> bool) list

    val symb_stack_of_stack : stack -> Aut.Gram.symbol list

    val pop : Aut.Gram.symbol list -> stack -> 'a1 arrows_right -> stack * 'a1

    type step_result =
    | Fail_sr_full of Aut.state * Aut.Gram.token
    | Accept_sr of Aut.Gram.symbol_semantic_type * buffer
    | Progress_sr of stack * buffer

    val step_result_rect :
      Aut.initstate -> (Aut.state -> Aut.Gram.token -> 'a1) ->
      (Aut.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1

    val step_result_rec :
      Aut.initstate -> (Aut.state -> Aut.Gram.token -> 'a1) ->
      (Aut.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1

    val reduce_step :
      Aut.initstate -> stack -> Aut.Gram.production -> buffer -> step_result

    val step : Aut.initstate -> stack -> buffer -> step_result

    val parse_fix : Aut.initstate -> stack -> buffer -> int -> step_result

    type 'a parse_result =
    | Fail_pr_full of Aut.state * Aut.Gram.token
    | Timeout_pr
    | Parsed_pr of 'a * buffer

    val parse_result_rect :
      (Aut.state -> Aut.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2)
      -> 'a1 parse_result -> 'a2

    val parse_result_rec :
      (Aut.state -> Aut.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2)
      -> 'a1 parse_result -> 'a2

    val parse :
      Aut.initstate -> buffer -> int -> Aut.Gram.symbol_semantic_type
      parse_result
   end

  module Correct :
   sig
   end

  module Complete :
   sig
    module Valid :
     sig
      module TerminalComparableM :
       sig
        type t = Aut.Gram.terminal

        val tComparable : t coq_Comparable
       end

      module TerminalOrderedType :
       sig
        module Alt :
         sig
          type t = TerminalComparableM.t

          val compare : t -> t -> comparison
         end

        type t = Alt.t

        val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare

        val eq_dec : Alt.t -> Alt.t -> bool
       end

      module StateProdPosComparableM :
       sig
        type t = (Aut.state * Aut.Gram.production) * int

        val tComparable : t coq_Comparable
       end

      module StateProdPosOrderedType :
       sig
        module Alt :
         sig
          type t = StateProdPosComparableM.t

          val compare : t -> t -> comparison
         end

        type t = Alt.t

        val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare

        val eq_dec : Alt.t -> Alt.t -> bool
       end

      module TerminalSet :
       sig
        module X' :
         sig
          type t = TerminalOrderedType.Alt.t

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
         end

        module MSet :
         sig
          module Raw :
           sig
            type elt = TerminalOrderedType.Alt.t

            type tree =
            | Leaf
            | Node of Int.Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree

            val empty : tree

            val is_empty : tree -> bool

            val mem : TerminalOrderedType.Alt.t -> tree -> bool

            val min_elt : tree -> elt option

            val max_elt : tree -> elt option

            val choose : tree -> elt option

            val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

            val elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list

            val elements : tree -> TerminalOrderedType.Alt.t list

            val rev_elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list

            val rev_elements : tree -> TerminalOrderedType.Alt.t list

            val cardinal : tree -> int

            val maxdepth : tree -> int

            val mindepth : tree -> int

            val for_all : (elt -> bool) -> tree -> bool

            val exists_ : (elt -> bool) -> tree -> bool

            type enumeration =
            | End
            | More of elt * tree * enumeration

            val cons : tree -> enumeration -> enumeration

            val compare_more :
              TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
              enumeration -> comparison

            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration -> comparison

            val compare_end : enumeration -> comparison

            val compare : tree -> tree -> comparison

            val equal : tree -> tree -> bool

            val subsetl :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

            val subsetr :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

            val subset : tree -> tree -> bool

            type t = tree

            val height : t -> Int.Z_as_Int.t

            val singleton : TerminalOrderedType.Alt.t -> tree

            val create : t -> TerminalOrderedType.Alt.t -> t -> tree

            val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree

            val bal : t -> TerminalOrderedType.Alt.t -> t -> tree

            val add : TerminalOrderedType.Alt.t -> tree -> tree

            val join : tree -> elt -> t -> t

            val remove_min : tree -> elt -> t -> t * elt

            val merge : tree -> tree -> tree

            val remove : TerminalOrderedType.Alt.t -> tree -> tree

            val concat : tree -> tree -> tree

            type triple = { t_left : t; t_in : bool; t_right : t }

            val t_left : triple -> t

            val t_in : triple -> bool

            val t_right : triple -> t

            val split : TerminalOrderedType.Alt.t -> tree -> triple

            val inter : tree -> tree -> tree

            val diff : tree -> tree -> tree

            val union : tree -> tree -> tree

            val filter : (elt -> bool) -> tree -> tree

            val partition : (elt -> bool) -> t -> t * t

            val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool

            val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool

            val isok : tree -> bool

            module MX :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end

                module TO :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end

              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
             end

            module L :
             sig
              module MO :
               sig
                module OrderTac :
                 sig
                  module OTF :
                   sig
                    type t = TerminalOrderedType.Alt.t

                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison

                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end

                  module TO :
                   sig
                    type t = TerminalOrderedType.Alt.t

                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison

                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                 end

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool

                val lt_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool

                val eqb :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end

            val flatten_e : enumeration -> elt list

            type coq_R_bal =
            | R_bal_0 of t * TerminalOrderedType.Alt.t * t
            | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_4 of t * TerminalOrderedType.Alt.t * t
            | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_8 of t * TerminalOrderedType.Alt.t * t

            type coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * (t * elt)
               * coq_R_remove_min * t * elt

            type coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * elt

            type coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * elt

            type coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * bool * t * 
               tree * coq_R_inter * tree * coq_R_inter
            | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * bool * t * 
               tree * coq_R_inter * tree * coq_R_inter

            type coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * bool * t * 
               tree * coq_R_diff * tree * coq_R_diff
            | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * bool * t * 
               tree * coq_R_diff * tree * coq_R_diff

            type coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_union_2 of tree * tree * Int.Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Int.Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree * t * bool * t * 
               tree * coq_R_union * tree * coq_R_union
           end

          module E :
           sig
            type t = TerminalOrderedType.Alt.t

            val compare :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              comparison

            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end

          type elt = TerminalOrderedType.Alt.t

          type t_ = Raw.t
            (* singleton inductive, whose constructor was Mkt *)

          val this : t_ -> Raw.t

          type t = t_

          val mem : elt -> t -> bool

          val add : elt -> t -> t

          val remove : elt -> t -> t

          val singleton : elt -> t

          val union : t -> t -> t

          val inter : t -> t -> t

          val diff : t -> t -> t

          val equal : t -> t -> bool

          val subset : t -> t -> bool

          val empty : t

          val is_empty : t -> bool

          val elements : t -> elt list

          val choose : t -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

          val cardinal : t -> int

          val filter : (elt -> bool) -> t -> t

          val for_all : (elt -> bool) -> t -> bool

          val exists_ : (elt -> bool) -> t -> bool

          val partition : (elt -> bool) -> t -> t * t

          val eq_dec : t -> t -> bool

          val compare : t -> t -> comparison

          val min_elt : t -> elt option

          val max_elt : t -> elt option
         end

        type elt = TerminalOrderedType.Alt.t

        type t = MSet.t

        val empty : t

        val is_empty : t -> bool

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val singleton : elt -> t

        val remove : elt -> t -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val eq_dec : t -> t -> bool

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val filter : (elt -> bool) -> t -> t

        val partition : (elt -> bool) -> t -> t * t

        val cardinal : t -> int

        val elements : t -> elt list

        val choose : t -> elt option

        module MF :
         sig
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end

        val min_elt : t -> elt option

        val max_elt : t -> elt option

        val compare : t -> t -> t OrderedType.coq_Compare

        module E :
         sig
          type t = TerminalOrderedType.Alt.t

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            TerminalOrderedType.Alt.t OrderedType.coq_Compare

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
       end

      module StateProdPosMap :
       sig
        module E :
         sig
          type t = StateProdPosOrderedType.Alt.t

          val compare :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            StateProdPosOrderedType.Alt.t OrderedType.coq_Compare

          val eq_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool
         end

        module Raw :
         sig
          type key = StateProdPosOrderedType.Alt.t

          type 'elt tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t

          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val height : 'a1 tree -> Int.Z_as_Int.t

          val cardinal : 'a1 tree -> int

          val empty : 'a1 tree

          val is_empty : 'a1 tree -> bool

          val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool

          val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option

          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

          val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree

          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                               t_right : 'elt tree }

          val t_left : 'a1 triple -> 'a1 tree

          val t_opt : 'a1 triple -> 'a1 option

          val t_right : 'a1 triple -> 'a1 tree

          val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple

          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

          val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

          val elements : 'a1 tree -> (key * 'a1) list

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          type 'elt enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration

          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

          val equal_more :
            ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            ('a1 enumeration -> bool) -> 'a1 enumeration -> bool

          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool

          val equal_end : 'a1 enumeration -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree

          module Proofs :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = StateProdPosOrderedType.Alt.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end

            module L :
             sig
              module MX :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end

              module PX :
               sig
                module MO :
                 sig
                  module TO :
                   sig
                    type t = StateProdPosOrderedType.Alt.t
                   end

                  module IsTO :
                   sig
                   end

                  module OrderTac :
                   sig
                   end

                  val eq_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool

                  val lt_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool

                  val eqb :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool
                 end
               end

              type key = StateProdPosOrderedType.Alt.t

              type 'elt t = (StateProdPosOrderedType.Alt.t * 'elt) list

              val empty : 'a1 t

              val is_empty : 'a1 t -> bool

              val mem : key -> 'a1 t -> bool

              val find : key -> 'a1 t -> 'a1 option

              val add : key -> 'a1 -> 'a1 t -> 'a1 t

              val remove : key -> 'a1 t -> 'a1 t

              val elements : 'a1 t -> 'a1 t

              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

              val option_cons :
                key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t

              val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key * 'a3) list

              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
              'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool
              -> 'a1 coq_R_mem -> 'a2

            val coq_R_mem_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
              'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool
              -> 'a1 coq_R_mem -> 'a2

            type 'elt coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
              coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
              coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val coq_R_find_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
              coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
              coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            type 'elt coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * 
               key * 'elt * 'elt tree * Int.Z_as_Int.t
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
              'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
              tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
              -> 'a1 coq_R_bal -> 'a2

            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
              'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
              tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
              -> 'a1 coq_R_bal -> 'a2

            type 'elt coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
              -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
              -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_add -> 'a2

            type 'elt coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t
               * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min
               * 'elt tree * (key * 'elt)

            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            type 'elt coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * (key * 'elt)
               * key * 'elt

            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1)
              -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_merge -> 'a2

            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1)
              -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_merge -> 'a2

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove

            val coq_R_remove_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2

            val coq_R_remove_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2

            type 'elt coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * (key * 'elt)

            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1)
              -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_concat -> 'a2

            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1
              -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1)
              -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_concat -> 'a2

            type 'elt coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree

            val coq_R_split_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
              option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple ->
              'a1 coq_R_split -> 'a2

            val coq_R_split_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
              option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple ->
              'a1 coq_R_split -> 'a2

            type ('elt, 'x) coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Int.Z_as_Int.t * 'x * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Int.Z_as_Int.t * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option

            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
              __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
              'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
              ('a1, 'a2) coq_R_map_option -> 'a3

            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
              __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
              'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
              ('a1, 'a2) coq_R_map_option -> 'a3

            type ('elt, 'x0, 'x) coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'x0 tree
            | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t
            | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 
               'x0 tree * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
               * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 
               'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 
               'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
              Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
              __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
              -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
              tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2
              tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
              -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3)
              coq_R_map2_opt -> 'a4

            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Int.Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
              Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
              __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
              -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
              tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2
              tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
              -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3)
              coq_R_map2_opt -> 'a4

            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

            val flatten_e : 'a1 enumeration -> (key * 'a1) list
           end
         end

        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)

        val this : 'a1 bst -> 'a1 Raw.tree

        type 'elt t = 'elt bst

        type key = StateProdPosOrderedType.Alt.t

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> int

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      val nullable_symb : Aut.Gram.symbol -> bool

      val nullable_word : Aut.Gram.symbol list -> bool

      val first_nterm_set : Aut.Gram.nonterminal -> TerminalSet.t

      val first_symb_set : Aut.Gram.symbol -> TerminalSet.t

      val first_word_set : Aut.Gram.symbol list -> TerminalSet.t

      val future_of_prod : Aut.Gram.production -> int -> Aut.Gram.symbol list

      val items_map : unit -> TerminalSet.t StateProdPosMap.t

      val find_items_map :
        TerminalSet.t StateProdPosMap.t -> Aut.state -> Aut.Gram.production
        -> int -> TerminalSet.t

      val forallb_items :
        TerminalSet.t StateProdPosMap.t -> (Aut.state -> Aut.Gram.production
        -> int -> TerminalSet.t -> bool) -> bool

      val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool

      val is_complete_0 : TerminalSet.t StateProdPosMap.t -> bool

      val is_complete : unit -> bool
     end

    type pt_zipper =
    | Top_ptz
    | Cons_ptl_ptz of Aut.Gram.symbol list * Aut.Gram.token list
       * Aut.GramDefs.parse_tree_list * Aut.Gram.symbol * Aut.Gram.token list
       * ptl_zipper
    and ptl_zipper =
    | Non_terminal_pt_ptlz of Aut.Gram.production * Aut.Gram.token list
       * pt_zipper
    | Cons_ptl_ptlz of Aut.Gram.symbol list * Aut.Gram.token list
       * Aut.Gram.symbol * Aut.Gram.token list * Aut.GramDefs.parse_tree
       * ptl_zipper

    val pt_zipper_rect :
      Aut.initstate -> Aut.Gram.token list -> 'a1 -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> Aut.Gram.symbol
      -> Aut.Gram.token list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> 'a1

    val pt_zipper_rec :
      Aut.initstate -> Aut.Gram.token list -> 'a1 -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> Aut.Gram.symbol
      -> Aut.Gram.token list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> 'a1

    val ptl_zipper_rect :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> pt_zipper -> 'a1) -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.Gram.symbol -> Aut.Gram.token list ->
      Aut.GramDefs.parse_tree -> ptl_zipper -> 'a1 -> 'a1) -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> 'a1

    val ptl_zipper_rec :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> pt_zipper -> 'a1) -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.Gram.symbol -> Aut.Gram.token list ->
      Aut.GramDefs.parse_tree -> ptl_zipper -> 'a1 -> 'a1) -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> 'a1

    type pt_dot =
    | Reduce_ptd of Aut.Gram.production * Aut.Gram.token list
       * Aut.GramDefs.parse_tree_list * pt_zipper
    | Shift_ptd of Aut.Gram.token * Aut.Gram.symbol list
       * Aut.Gram.token list * Aut.GramDefs.parse_tree_list * ptl_zipper

    val pt_dot_rect :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> pt_zipper ->
      'a1) -> (Aut.Gram.token -> Aut.Gram.symbol list -> Aut.Gram.token list
      -> Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

    val pt_dot_rec :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> pt_zipper ->
      'a1) -> (Aut.Gram.token -> Aut.Gram.symbol list -> Aut.Gram.token list
      -> Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

    val ptlz_sem :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> (__ -> __ arrows_right -> __) ->
      Aut.Gram.symbol_semantic_type

    val ptz_sem :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> Aut.Gram.symbol_semantic_type ->
      Aut.Gram.symbol_semantic_type

    val ptd_sem :
      Aut.initstate -> Aut.Gram.token list -> pt_dot ->
      Aut.Gram.symbol_semantic_type

    val ptlz_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> Inter.buffer

    val ptz_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      -> Aut.Gram.token list -> pt_zipper -> Inter.buffer

    val ptd_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> pt_dot ->
      Inter.buffer

    val ptlz_prod :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> Aut.Gram.production

    val ptlz_future :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> Aut.Gram.symbol list

    val ptlz_lookahead :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> Aut.Gram.terminal

    val build_pt_dot_from_pt :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree -> pt_zipper -> pt_dot

    val build_pt_dot_from_pt_rec :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> ptl_zipper ->
      pt_dot

    val build_pt_dot_from_ptl :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> ptl_zipper ->
      pt_dot

    val next_ptd :
      Aut.initstate -> Aut.Gram.token list -> pt_dot -> pt_dot option

    val next_ptd_iter :
      Aut.initstate -> Aut.Gram.token list -> pt_dot -> int -> pt_dot option

    val ptlz_cost :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> int

    val ptz_cost :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> int

    val ptd_cost : Aut.initstate -> Aut.Gram.token list -> pt_dot -> int
   end

  val complete_validator : unit -> bool

  val safe_validator : unit -> bool

  val parse :
    Aut.initstate -> int -> Inter.buffer -> Aut.Gram.symbol_semantic_type
    Inter.parse_result
 end

val prog :
  int -> MenhirLibParser.Inter.buffer -> (Cst.obj * Cst.obj)
  MenhirLibParser.Inter.parse_result
