open Decidability
open NbE
open Predicativity
open Signatures
open Specif
open Subtyping
open Syntax

type __ = Obj.t

val lookup : coq_PtsSig -> coq_DecidableSig -> exp list -> int -> exp option

val type_aty_functional :
  (coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> __ -> exp list ->
  exp -> __ -> exp -> __ -> bool) -> (coq_PtsSig -> coq_DecidableSig ->
  coq_PredicativeSig -> __ -> exp list -> __ -> exp -> __ -> bool) ->
  (coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> __ -> exp list ->
  __ -> exp -> __ -> nf option) -> coq_PtsSig -> coq_DecidableSig ->
  coq_PredicativeSig -> exp list -> exp -> bool

val type_check :
  coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp list -> exp ->
  exp -> bool

val type_aty :
  coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp list -> exp ->
  bool

val type_infer :
  coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp list -> exp ->
  nf option

val type_check_closed :
  coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp -> exp -> bool
