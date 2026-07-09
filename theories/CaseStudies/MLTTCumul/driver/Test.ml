(* Unit test cases for parsing *)

open Main
open McptsExtracted_MLTTCumul.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(** Real tests *)
(* We never expect parser timeout. 2^500 fuel should be large enough! *)

let%expect_test "let_nary.mltt works" = 
  let _ = main_of_example "let_nary.mltt" in
  [%expect
    {|
    Parsed:
      (fun (Nary : forall (n : Nat) : Type@1 -> Type@0)
           (toNat : forall (f : Nary 0) : Type@0 -> Nat)
           (appNary : forall (n : Nat)
                             (f : Nary (succ n))
                             (arg : Nat) : Type@0
                        -> Nary n)
           (n : Nat)
           (f : Nary n) : Type@1
        -> ((rec n return y . forall (g : Nary y) : Type@0 -> Nat
             | zero => toNat
             | succ m, r =>
               fun (g : Nary (succ m)) : Type@0
                 -> (r (appNary m g (succ m)) : Nat)
             end)
              f : Nat))
        (fun (n : Nat) : Type@1
          -> (rec n return y . Type@0
              | zero => Nat
              | succ m, r => forall (a : Nat) : Type@0 -> r
              end : Type@0))
        (fun (f : Nat) : Type@0 -> (f : Nat))
        (fun (n : Nat)
             (f : rec succ n return y . Type@0
                  | zero => Nat
                  | succ m, r => forall (a : Nat) : Type@0 -> r
                  end)
             (arg : Nat) : Type@0
          -> (f arg : rec n return y . Type@0
                      | zero => Nat
                      | succ m, r => forall (a : Nat) : Type@0 -> r
                      end))
        3
        ((fun (add : forall (a : Nat)
                            (b : Nat) : Type@0
                       -> Nat)
              (a : Nat)
              (b : Nat)
              (c : Nat) : Type@0
           -> (Nat : add a (add b c)))
          (fun (a : Nat)
               (b : Nat) : Type@0
            -> (Nat : rec a return y . Nat | zero => b | succ m, r => succ r end)))
      : Nat
    Elaborated:
      (fun (x1 : forall (x2 : Nat) : Type@1 -> Type@0)
           (x11 : forall (x12 : x1 0) : Type@0 -> Nat)
           (x19 : forall (x20 : Nat)
                         (x21 : x1 (succ x20))
                         (x22 : Nat) : Type@0
                    -> x1 x20)
           (x25 : Nat)
           (x27 : x1 x25) : Type@1
        -> ((rec x25 return x28 . forall (x31 : x1 x28) : Type@0 -> Nat
             | zero => x11
             | succ x29, x30 =>
               fun (x32 : x1 (succ x29)) : Type@0
                 -> (x30 (x19 x29 x32 (succ x29)) : Nat)
             end)
              x27 : Nat))
        (fun (x33 : Nat) : Type@1
          -> (rec x33 return x34 . Type@0
              | zero => Nat
              | succ x35, A1 => forall (x36 : Nat) : Type@0 -> A1
              end : Type@0))
        (fun (x37 : Nat) : Type@0 -> (x37 : Nat))
        (fun (x38 : Nat)
             (x47 : rec succ x38 return x48 . Type@0
                    | zero => Nat
                    | succ x49, A4 => forall (x50 : Nat) : Type@0 -> A4
                    end)
             (x55 : Nat) : Type@0
          -> (x47 x55 : rec x38 return x56 . Type@0
                        | zero => Nat
                        | succ x57, A6 => forall (x58 : Nat) : Type@0 -> A6
                        end))
        3
        ((fun (x59 : forall (x60 : Nat)
                            (x61 : Nat) : Type@0
                       -> Nat)
              (x65 : Nat)
              (x68 : Nat)
              (x70 : Nat) : Type@0
           -> (Nat : x59 x65 (x59 x68 x70)))
          (fun (x71 : Nat)
               (x73 : Nat) : Type@0
            -> (Nat : rec x71 return x74 . Nat
                      | zero => x73
                      | succ x75, x76 => succ x76
                      end)))
      : Nat
    Normalized Result:
      6 : Nat
    |}]

let%expect_test "let_two_vars.mltt works" = 
  let _ = main_of_example "let_two_vars.mltt" in
  [%expect
    {|
    Parsed:
      (fun (x : Nat)
           (f : forall (y : Nat) : Type@0 -> Nat) : Type@0
        -> (Nat : f x))
        0
        (fun (n : Nat) : Type@0 -> (n : Nat))
      : Nat
    Elaborated:
      (fun (x1 : Nat)
           (x4 : forall (x5 : Nat) : Type@0 -> Nat) : Type@0
        -> (Nat : x4 x1))
        0
        (fun (x6 : Nat) : Type@0 -> (x6 : Nat))
      : Nat
    Normalized Result:
      0 : Nat
    |}]

let%expect_test "simple-fn.mltt works" = 
  let _ = main_of_example "simple-fn.mltt" in
  [%expect
    {|
    Parsed:
      fun (x : Nat) : Type@0 -> (x : Nat) : forall (x : Nat) : Type@0 -> Nat
    Elaborated:
      fun (x1 : Nat) : Type@0 -> (x1 : Nat) : forall (x1 : Nat) : Type@0 -> Nat
    Normalized Result:
      fun (x1 : Nat) : Type@0 -> (x1 : Nat) : forall (x1 : Nat) : Type@0 -> Nat
    |}]

let%expect_test "simple-let.mltt works" = 
  let _ = main_of_example "simple-let.mltt" in
  [%expect
    {|
    Parsed:
      (fun (x : Type@0)
           (y : Nat) : Type@1
        -> (Nat : succ y)) Nat 0 : Nat
    Elaborated:
      (fun (A1 : Type@0)
           (x2 : Nat) : Type@1
        -> (Nat : succ x2)) Nat 0 : Nat
    Normalized Result:
      1 : Nat
    |}]

let%expect_test "simple-nat.mltt works" = 
  let _ = main_of_example "simple-nat.mltt" in
  [%expect
    {|
    Parsed:
      4 : Nat
    Elaborated:
      4 : Nat
    Normalized Result:
      4 : Nat
    |}]

let%expect_test "simple-rec.mltt works" = 
  let _ = main_of_example "simple-rec.mltt" in
  [%expect
    {|
    Parsed:
      fun (x : Nat) : Type@0
        -> (rec x return y . Nat | zero => 1 | succ n, r => succ r end : Nat)
      : forall (x : Nat) : Type@0 -> Nat
    Elaborated:
      fun (x1 : Nat) : Type@0
        -> (rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end : Nat)
      : forall (x1 : Nat) : Type@0 -> Nat
    Normalized Result:
      fun (x1 : Nat) : Type@0
        -> (rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end : Nat)
      : forall (x1 : Nat) : Type@0 -> Nat
    |}]    