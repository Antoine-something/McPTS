# Description

LF is a language containing two sorts, ★ and □ (of types and kinds, respectively). Typically, it contains the function rules
(★, ★, ★) and (★, □, □), allowing for simple and dependent function spaces.
A typical LF program is a list of declarations.
Since we do not currently support declarations, we elaborate the LF program into a big function space, where each declaration becomes a variable.
Since the LF PTS* signature does not allow type variables, we cannot represent type declarations in this way.
To work around the issue, we extend this with another rule, (□, □, □), giving us function spaces like `Π(x: ★).★`, where we interpret `x` as a type declaration.

Thus, the signature for our implementation is formally defined as follows:

```
St := {★, □}
Ax_typ := {(★, □)}
Ax_sub := {}
Ru_nat := {}
Ru_pi := {(★, ★, ★), (★, □, □), (□, □, □)}
```

# Grammar

A program in the front-end language is a series of definitions and let expressions. 
The grammar is defined [here](Parser.vy) and is given as follows:

```
<prog>         ::=
                | <define_defns> EOF                         # Series of definitions and let expressions

<expr>         ::=
                | "forall" <params> ":" <sort> "->" <expr>   # Pi types
                | "fun" <params> ":" <sort> "->" <ann_expr>  # Functions
                | <app_expr>                                 # Function application or atomic expressions

<sort>         ::=
                | "type"
                | "kind"

<app_expr>     ::=
                | <app_expr> <atomic_expr>
                | <atomic_expr>

<atomic_expr>  ::=
                | <sort>
                | VAR
                | "(" <expr> ")"
                
<params>       ::=
                | <params> <param>
                | <param>

<param>        ::=
                | "(" VAR ":" <expr> ")"

<ann_expr>     ::=
                | "(" <expr> ":" <expr> ")"

<define_defns> ::=
                | "def@type" <param> "." <define_defns>         # Type variable definitions
                | "def@exp" <param> "." <define_defns>          # Term variable definitions
                | "let" <param> ":=" <expr> "." <define_defns>  # Let expressions
```

## Terminals
- `VAR`: Variable names starting with a letter or an underscore, containing letters, underscores, and digits
- `EOF`: End of file

## Notes
- McPTS requires codomain annotations on functions, so the function and let rules take `ann_expr`
- Because the extended rule (□, □, □) is only used in type variable definitions, the pi, function, and let rules are only annotated with `type` or `kind` for simple and dependent functions, respectively
- Unlike in the MiniML and MLTTCumul case studies, let expressions only take one definition.

# Running the compiler

Once McPTS is compiled and LF is extracted following the instructions
in the [top-level README](../../../README.md), examples can be run as follows:

```bash
dune exec mcpts_lf <path/to/file.lf>
```

A number of examples can be found in `McPTS/theories/CaseStudies/LF/examples`.