# Description

MLTTCumul implements a Martin-Löf type theory with a cumulative universe hierarchy.
Formally, it is defined with the following signature:

```
St := ℕ
Ax_typ := {(i, S i) | i ∈ ℕ}
Ax_sub := {(i, S i) | i ∈ ℕ}
Ru_nat := {0}
Ru_pi := {(i, j, max(i, j)) | i ∈ ℕ}
```


# Grammar

A program in the front-end language is a typed expression. 
The grammar is defined [here](Parser.vy) and is given as follows:

```
<prog>        ::=
               | <expr> ":" <expr> EOF

<expr>        ::=
               | "forall" <params> ":" <level> "->" <expr>      # Pi types
               | "fun" <params> ":" <level> "->" <ann_expr>     # Functions
               | <app_expr>                                     # Function application or atomic expressions
               | "rec" <expr> "return" VAR "." <expr>           # Natural recursion
                 "|" "zero" "=>" <expr>
                 "|" "succ" VAR "," VAR "=>" <expr>
                 "end"
               | "succ" <atomic_expr>                           # Successor
               | "let" <let_defns> ":" <level> "in" <ann_expr>  # Let expressions

<level>       ::=
               | "Type" "@" INT

<app_expr>    ::=
               | <app_expr> <atomic_expr>
               | <atomic_expr>

<atomic_expr> ::=
               | <level>
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
- Instead of a full rule annotation, only the higher `<level>` between the domain and codomain is given in the pi, function, and let rules just take `type` or `kind` for simple and dependent functions, respectively
- Because let definitions and parameters are both enclosed in parentheses, let definitions take the form
`let ((x : Nat) := 0) : Type@0 in ...`

# Running the compiler

Once McPTS is compiled and MLTTCumul is extracted following the instructions
in the [top-level README](../../../README.md), examples can be run as follows:

```bash
dune exec mcpts_mlttcumul <path/to/file.mltt>
```

A number of examples can be found in `McPTS/theories/CaseStudies/MLTTCumul/examples`.