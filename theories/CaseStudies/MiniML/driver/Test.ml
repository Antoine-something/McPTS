(* Unit test cases for parsing *)

open Main
open McptsExtracted_MiniML.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(** Real tests *)
(* We never expect parser timeout. 2^500 fuel should be large enough! *)

let%expect_test "let-two-vars.miniml works" = 
  let _ = main_of_example "let-two-vars.miniml" in
  [%expect {|
    Parsed:
      (fun (x : Nat)
           (f : forall (y : Nat) -> Nat)
        -> f x) 0 (fun (n : Nat) -> n)
      : Nat
    Elaborated:
      (fun (x1 : Nat)
           (x4 : forall (x5 : Nat) -> Nat)
        -> x4 x1) 0
        (fun (x6 : Nat) -> x6)
      : Nat
    Normalized Result:
      0 : Nat
    |}]

let%expect_test "add-numbers.miniml works" = 
  let _ = main_of_example "add-numbers.miniml" in
  [%expect
    {|
    Parsed:
      (fun (x : Nat)
           (y : Nat)
        -> rec x return z . Nat | zero => y | succ n, r => succ r end)
        3
        4
      : Nat
    Elaborated:
      (fun (x1 : Nat)
           (x3 : Nat)
        -> rec x1 return x4 . Nat | zero => x3 | succ x5, x6 => succ x6 end)
        3
        4
      : Nat
    Normalized Result:
      7 : Nat
    |}]

let%expect_test "add.miniml works" = 
  let _ = main_of_example "add.miniml" in
  [%expect
    {|
    Parsed:
      fun (x : Nat)
          (y : Nat)
        -> rec x return z . Nat | zero => y | succ n, r => succ r end
      : forall (x : Nat)
               (y : Nat)
          -> Nat
    Elaborated:
      fun (x1 : Nat)
          (x3 : Nat)
        -> rec x1 return x4 . Nat | zero => x3 | succ x5, x6 => succ x6 end
      : forall (x1 : Nat)
               (x2 : Nat)
          -> Nat
    Normalized Result:
      fun (x1 : Nat)
          (x3 : Nat)
        -> rec x1 return x4 . Nat | zero => x3 | succ x5, x6 => succ x6 end
      : forall (x1 : Nat)
               (x2 : Nat)
          -> Nat
    |}]

let%expect_test "let-mult.miniml works" = 
  let _ = main_of_example "let-mult.miniml" in
  [%expect
    {|
    Parsed:
      (fun (add : forall (x : Nat)
                         (y : Nat)
                    -> Nat)
        -> (fun (mult : forall (x : Nat)
                               (y : Nat)
                          -> Nat) -> mult 3 5)
             (fun (x : Nat)
                  (y : Nat)
               -> rec x return z . Nat | zero => 0 | succ n, r => add r y end))
        (fun (x : Nat)
             (y : Nat)
          -> rec x return z . Nat | zero => y | succ n, r => succ r end)
      : Nat
    Elaborated:
      (fun (x1 : forall (x2 : Nat)
                        (x3 : Nat)
                   -> Nat)
        -> (fun (x4 : forall (x5 : Nat)
                             (x6 : Nat)
                        -> Nat) -> x4 3 5)
             (fun (x7 : Nat)
                  (x9 : Nat)
               -> rec x7 return x10 . Nat
                  | zero => 0
                  | succ x11, x12 => x1 x12 x9
                  end))
        (fun (x13 : Nat)
             (x15 : Nat)
          -> rec x13 return x16 . Nat
             | zero => x15
             | succ x17, x18 => succ x18
             end)
      : Nat
    Normalized Result:
      15 : Nat
    |}]

let%expect_test "simple-fn.miniml works" = 
  let _ = main_of_example "simple-fn.miniml" in
  [%expect
    {|
    Parsed:
      fun (x : Nat) -> x : forall (x : Nat) -> Nat
    Elaborated:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
    Normalized Result:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "simple-let.miniml works" = 
  let _ = main_of_example "simple-let.miniml" in
  [%expect
    {|
    Parsed:
      (fun (x : Nat) -> succ x) 0 : Nat
    Elaborated:
      (fun (x1 : Nat) -> succ x1) 0 : Nat
    Normalized Result:
      1 : Nat
    |}]

let%expect_test "simple-nat.miniml works" = 
  let _ = main_of_example "simple-nat.miniml" in
  [%expect
    {|
    Parsed:
      4 : Nat
    Elaborated:
      4 : Nat
    Normalized Result:
      4 : Nat
    |}]
