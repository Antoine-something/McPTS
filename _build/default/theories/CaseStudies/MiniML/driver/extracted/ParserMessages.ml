
(* This file was auto-generated based on "theories/CaseStudies/MiniML/parserMessages.messages". *)

(* Please note that the function [message] can raise [Not_found]. *)

let message =
  fun s ->
    match s with
    | 62 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 61 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 60 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 56 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 54 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 53 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 52 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 51 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 50 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 49 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 48 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 47 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 46 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 45 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 44 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 43 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 42 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 41 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 40 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 39 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 35 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 34 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 32 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 30 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 29 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 22 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 21 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 20 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 18 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 17 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 16 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 15 ->
        "A parenthesized paremeter is expect.\nFor example,\n  \"(x : Nat)\" in \"fun (x : Nat) -> (x : Nat)\"\n"
    | 14 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 13 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 12 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 11 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 10 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 9 ->
        "A parenthesized paremeter is expect.\nFor example,\n  \"(x : Nat)\" in \"fun (x : Nat) -> (x : Nat)\"\n"
    | 8 ->
        "A list of parenthesized parameters is expected.\nFor example,\n  \"(x : Nat) (y : Nat)\" in \"forall (x : Nat) (y : Nat) -> Nat\"\n"
    | 7 ->
        "A scrutinee expression is expected.\nThis token is invalid for the beginning of an expression.\n"
    | 6 ->
        "Empty brackets are not allowed\n"
    | 4 ->
        "Expected an expression after 'succ'\n"
    | 0 ->
        "This token is invalid for the beginning of a program.\n"
    | _ ->
        raise Not_found
