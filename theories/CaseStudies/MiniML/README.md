# Description

MiniML is a language containing simple function spaces and recursion over natural numbers. 

# Grammar

A program in the front-end language is a typed expression. 
The grammar is defined [here](Parser.vy) and is given as follows:

```
<prog>        ::=
               | <expr> ":" <expr> EOF

<expr>        ::=
               | "forall" <params> "->" <expr>           # Pi types
               | "fun" <params> "->" <ann_expr>          # Functions
               | <app_expr>                              # Function application or atomic expressions
               | "rec" <expr> "return" VAR "." <expr>    # Natural recursion
                 "|" "zero" "=>" <expr>
                 "|" "succ" VAR "," VAR "=>" <expr>
                 "end"
               | "succ" <atomic_expr>                    # Successor
               | "let" <let_defns> "in" <ann_expr>       # Let expressions

<app_expr>    ::=
               | <app_expr> <atomic_expr>
               | <atomic_expr>

<atomic_expr> ::=
               | "Type"
               | "Nat"
               | "zero"
               | INT
               | VAR
               | "(" <expr> ")"
                
<params>      ::=
               | <params> <param>
               | <param>

<param>       ::=
               | "(" VAR ":" <expr> ")"

<ann_expr>    ::=
               | "(" <expr> ":" <expr> ")"

<let_defns>   ::=
               | <let_defns> <let_defn>
               | <let_defn>

<let_defn>    ::= 
               | "(" <param> ":=" <expr> ")"
```

## Terminals
- `INT`: Natural numbers
- `VAR`: Variable names starting with a letter or an underscore, containing letters, underscores, and digits
- `EOF`: End of file

## Notes
- McPTS requires codomain annotations on functions, so the function and let rules take `ann_expr`
- Because let definitions and parameters are both enclosed in parentheses, let definitions take the form
`let ((x : Nat) := 0) in ...`

# Running the compiler

Once McPTS is compiled and MiniML is extracted following the instructions
in the [top-level README](../../../README.md), examples can be run as follows:

```bash
dune exec mcpts_miniml <path/to/file.miniml>
```

A number of examples can be found in McPTS/theories/CaseStudies/MiniML/examples.