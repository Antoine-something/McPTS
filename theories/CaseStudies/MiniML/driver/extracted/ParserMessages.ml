
(* This file was auto-generated based on "theories/CaseStudies/MiniML/parserMessages.messages". *)

(* Please note that the function [message] can raise [Not_found]. *)

let message =
  fun s ->
    match s with
    | 62 ->
        "Expected token \"EOF\"\n"
    | 61 ->
        "Expected an expression.\nThis token is invalid for the beginning of an expression.\n"
    | 60 ->
        "Either an expression or \":\" is expected.\nThis token is invalid for the beginning of an expression.\n"
    | 56 ->
        "Either an expression or \")\" is expected.\nThis token is invalid for the beginning of an expression.\n"
    | 54 ->
        "Expected token \"end\" after successor branch\n"
    | 53 ->
        "Expected expression in the successor branch\n"
    | 52 ->
        "Expected token \"=>\" after variable name in successor branch\n"
    | 51 ->
        "Expected variable name after token \",\"\n"
    | 50 ->
        "Expected token \",\" after variable name\n"
    | 49 ->
        "Expected variable binding after \"succ\"\n"
    | 48 ->
        "Expected token \"succ\" in the successor branch\n"
    | 47 ->
        "Expected token \"|\" at the start of successor branch\n"
    | 46 ->
        "Expected an expression in the \"zero\" branch\nThis token is invalid for the beginning of an expression.\n"
    | 45 ->
        "Expected symbol \"=>\" in the \"zero\" branch\n"
    | 44 ->
        "Expected token \"zero\"\n"
    | 43 ->
        "Expected token \"|\"\n"
    | 42 ->
        "Expected expression after \".\"\nThis token is invalid for the beginning of an expression.\n"
    | 41 ->
        "\".\" is expected after the scrutinee name of the motive of a natural number recursion.\n"
    | 40 ->
        "Expected a variable name after \"return\" keyword\n"
    | 39 ->
        "Either an expression or \"return\" keyword is expected.\nThis token is invalid for the beginning of an expression.\n"
    | 35 ->
        "Expected output type\n"
    | 34 ->
        "Expected symbol \"->\" after list of parameters in function type\n"
    | 32 ->
        "Ill-formed type in parameter of a function\n"
    | 30 ->
        "Expected annotated expression in body of \"let\"-expression\n"
    | 29 ->
        "Expected one expression in definition\n"
    | 22 ->
        "Expected closing parenthesis\n"
    | 21 ->
        "Expected type annotation \"?type\" in body of a function\n"
    | 20 ->
        "Expected annotated expression in body of a function\n"
    | 18 ->
        "Expected annotated expression in body of a function.\n\"()\" is not a valid a function body\n"
    | 17 ->
        "Expected annotated expression in body of a function\n"
    | 16 ->
        "Expected symbol '->'\n"
    | 15 ->
        "A parenthesized paremeter is expected.\nFor example,\n  \"(x : Nat)\" in \"fun (x : Nat) -> (x : Nat)\"\n"
    | 14 ->
        "Expected annotated expression in body of 'let'-expression\n"
    | 13 ->
        "Expected a value for the variable\n"
    | 12 ->
        "A variable binding is expected after a \"let\"\n"
    | 11 ->
        "A parameter should have \"?type\" after \":\",\nwhere \"?type\" is the type of the parameter.\n"
    | 10 ->
        "A parameter should have \": ?type\" after the parameter name,\nwhere \"?type\" is the type of the parameter.\n"
    | 9 ->
        "A parameter should start with a valid identifier.\n"
    | 8 ->
        "A list of parenthesized parameters is expected.\nFor example,\n  \"(x : Nat) (y : Nat)\" in \"forall (x : Nat) (y : Nat) -> Nat\"\n"
    | 7 ->
        "A scrutinee expression is expected.\nThis token is invalid for the beginning of an expression.\n"
    | 6 ->
        "\"()\" is an invalid expression.\n\"()\" should have an expression in it to be an expression.\n"
    | 4 ->
        "Expected an expression after 'succ'\n"
    | 0 ->
        "This token is invalid for the beginning of a program.\n"
    | _ ->
        raise Not_found
