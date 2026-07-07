open Frontend
open NbE
open Parser
open Signature
open Syntax
open TypeCheck

type main_result =
| AllGood of Cst.obj * Cst.obj * exp * exp * nf
| TypeCheckingFailure of exp * exp
| ElaborationFailure of Cst.obj
| ParserFailure of Aut.state * Aut.Gram.token
| ParserTimeout of int

val main : int -> MenhirLibParser.Inter.buffer -> main_result
