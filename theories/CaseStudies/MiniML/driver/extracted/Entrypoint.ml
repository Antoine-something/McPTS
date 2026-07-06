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

(** val main : int -> MenhirLibParser.Inter.buffer -> main_result **)

let main log_fuel buf =
  match prog log_fuel buf with
  | MenhirLibParser.Inter.Fail_pr_full (s, t) -> ParserFailure (s, t)
  | MenhirLibParser.Inter.Timeout_pr -> ParserTimeout log_fuel
  | MenhirLibParser.Inter.Parsed_pr (p, _) ->
    let (o, o0) = p in
    (match elaborate' o0 [] with
     | Some e ->
       (match elaborate' o [] with
        | Some e0 ->
          if type_check_closed coq_P coq_MiniML_Decidable
               coq_MiniML_Predicative e e0
          then AllGood (o0, o, e, e0, (nbe_impl coq_MiniML_Sig [] e0 e))
          else TypeCheckingFailure (e, e0)
        | None -> ElaborationFailure o)
     | None -> ElaborationFailure o0)
