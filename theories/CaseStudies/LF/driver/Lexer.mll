{
  open Lexing
  open McptsExtracted_LF.Parser

  let get_range lexbuf = (lexbuf.lex_start_p, lexbuf.lex_curr_p)

  let format_position (f: Format.formatter) (p: position): unit =
    Format.fprintf
      f
      "line %d, column %d"
      p.pos_lnum
      (p.pos_cnum - p.pos_bol + 1)

  let format_range (f: Format.formatter) (p: position * position): unit =
    Format.fprintf
      f
      "@[<h>%a - %a@]"
      format_position (fst p)
      format_position (snd p)

  let token_to_string : token -> string =
    function
    | ARROW _ -> "->"
    | COLON _ -> ":"
    | LPAREN _ -> "("
    | RPAREN _ -> ")"
    | LAMBDA _ -> "fun"
    | PI _ -> "forall"
    | TYPE _ -> "type"
    | KIND _ -> "kind"
    | VAR (_, s) -> s
    | EOF _ -> "<EOF>"
    | DOT _ -> "."
    | LET _ -> "let"
    | COLONEQ _ -> ":="
    | DEF_TYPE _ -> "def@type"
    | DEF_EXP _ -> "def@exp"
      
  let get_range_of_token : token -> (position * position) =
    function
    | ARROW r
    | COLON r
    | LPAREN r
    | RPAREN r
    | LAMBDA r
    | PI r
    | TYPE r
    | KIND r
    | EOF r
    | DOT r
    | LET r
    | COLONEQ r
    | DEF_TYPE r
    | DEF_EXP r
    | VAR (r, _) -> r
    

  let format_token (f: Format.formatter) (t: token): unit =
    Format.fprintf
      f
      "@[<h>\"%s\" (at %a)@]"
      (token_to_string t)
      format_range (get_range_of_token t)
}

let ident = ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']*

rule read =
  parse
  | "->" { ARROW (get_range lexbuf) }
  | ':' { COLON (get_range lexbuf) }
  | "(*" { comment lexbuf }
  | '(' { LPAREN (get_range lexbuf) }
  | ')' { RPAREN (get_range lexbuf) }
  | "fun" { LAMBDA (get_range lexbuf) }
  | "forall" { PI (get_range lexbuf) }
  | [' ' '\t'] { read lexbuf }
  | ['\n'] { new_line lexbuf; read lexbuf }
  | "type" { TYPE (get_range lexbuf) }
  | "kind" { KIND (get_range lexbuf) }
  | eof { EOF (get_range lexbuf) }
  | "." { DOT (get_range lexbuf) }
  | "let" {LET (get_range lexbuf) }
  | ":=" {COLONEQ (get_range lexbuf) }
  | "def@type" {DEF_TYPE (get_range lexbuf) }
  | "def@exp" {DEF_EXP (get_range lexbuf) }
  | ident { VAR (get_range lexbuf, Lexing.lexeme lexbuf) }
  | _ as c { failwith (Format.asprintf "@[<v 2>Lexer error:@ @[<v 2>Unexpected character %C@ at %a@]@]@." c format_position lexbuf.lex_start_p) }
and comment =
  parse
  | "*)" { read lexbuf }
  | _ { comment lexbuf }

{
  let rec lexbuf_to_token_buffer lexbuf =
    lazy
      begin
        try
          MenhirLibParser.Inter.Buf_cons (read lexbuf, lexbuf_to_token_buffer lexbuf)
        with
        | Failure s -> prerr_string s; raise Exit
      end
}
