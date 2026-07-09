(* Unit test cases for parsing *)

open Main
open McptsExtracted_LF.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(** Real tests *)
(* We never expect parser timeout. 2^500 fuel should be large enough! *)

let%expect_test "hoas.lf works" = 
  let _ = main_of_example "hoas.lf" in
  [%expect
    {|
    Parsed:
      forall (exp : Type)
             (b : exp)
             (let_hoas : forall (e : exp)
                                (f : forall (e2 : exp) : Type -> exp)
                           : Type -> exp)
             (#is_var : forall (#_ : exp) : Kind -> Type)
             (e : #is_var (let_hoas b (fun (x : exp) : Type -> (x : exp))))
        : Kind -> Type
      : Kind
    Elaborated:
      forall (A1 : Type)
             (x1 : A1)
             (x2 : forall (x3 : A1)
                          (x4 : forall (x5 : A1) : Type -> A1)
                     : Type -> A1)
             (x6 : forall (x7 : A1) : Kind -> Type)
             (x8 : x6 (x2 x1 (fun (x9 : A1) : Type -> (x9 : A1))))
        : Kind -> Type
      : Kind
    Normalized Result:
      forall (A1 : Type)
             (x1 : A1)
             (x2 : forall (x3 : A1)
                          (x4 : forall (x5 : A1) : Type -> A1)
                     : Type -> A1)
             (x6 : forall (x7 : A1) : Kind -> Type)
             (x8 : x6 (x2 x1 (fun (x9 : A1) : Type -> (x9 : A1))))
        : Kind -> Type
      : Kind
    |}]

let%expect_test "lambda.lf works" = 
  let _ = main_of_example "lambda.lf" in
  [%expect
    {|
    Parsed:
      forall (tm : Type)
             (lam : forall (M : forall (x : tm) : Type -> tm) : Type -> tm)
             (app : forall (M : tm)
                           (N : tm)
                      : Type -> tm)
             (step : forall (M : tm)
                            (N : tm)
                       : Kind -> Type)
             (beta : forall (M : forall (x : tm) : Type -> tm)
                            (N : tm)
                       : Type -> step (app (lam M) N) (M N))
             (lam_cong : forall (M1 : forall (x : tm) : Type -> tm)
                                (M2 : forall (x : tm) : Type -> tm)
                                (s_M1_M2 : forall (x : tm)
                                                  (s_x_x : step x x)
                                             : Type -> step (M1 x) (M2 x))
                           : Type -> step (lam M1) (lam M2))
             (app_cong1 : forall (M1 : tm)
                                 (M2 : tm)
                                 (N : tm)
                                 (s_m1_m2 : step M1 M2)
                            : Type -> step (app M1 N) (app M2 N))
             (app_cong2 : forall (M : tm)
                                 (N1 : tm)
                                 (N2 : tm)
                                 (s_n1_n2 : step N1 N2)
                            : Type -> step (app M N1) (app M N2))
             (tp : Type)
             (base : tp)
             (arr : forall (A : tp)
                           (B : tp)
                      : Type -> tp)
             (oft : forall (M : tm)
                           (A : tp)
                      : Kind -> Type)
             (oft_lam : forall (M : forall (x : tm) : Type -> tm)
                               (A : tp)
                               (B : tp)
                               (oft_M : forall (x : tm)
                                               (oft_x : oft x A)
                                          : Type -> oft (M x) B)
                          : Type -> oft (lam M) (arr A B))
             (oft_app : forall (M : tm)
                               (N : tm)
                               (A : tp)
                               (B : tp)
                               (oft_M : oft M (arr A B))
                               (oft_n : oft N A)
                          : Type -> oft (app M N) B)
        : Kind -> Type
      : Kind
    Elaborated:
      forall (A1 : Type)
             (x1 : forall (x2 : forall (x3 : A1) : Type -> A1) : Type -> A1)
             (x4 : forall (x5 : A1)
                          (x6 : A1)
                     : Type -> A1)
             (x7 : forall (x8 : A1)
                          (x9 : A1)
                     : Kind -> Type)
             (x10 : forall (x11 : forall (x12 : A1) : Type -> A1)
                           (x13 : A1)
                      : Type -> x7 (x4 (x1 x11) x13) (x11 x13))
             (x14 : forall (x15 : forall (x16 : A1) : Type -> A1)
                           (x17 : forall (x18 : A1) : Type -> A1)
                           (x19 : forall (x20 : A1)
                                         (x21 : x7 x20 x20)
                                    : Type -> x7 (x15 x20) (x17 x20))
                      : Type -> x7 (x1 x15) (x1 x17))
             (x22 : forall (x23 : A1)
                           (x24 : A1)
                           (x25 : A1)
                           (x26 : x7 x23 x24)
                      : Type -> x7 (x4 x23 x25) (x4 x24 x25))
             (x27 : forall (x28 : A1)
                           (x29 : A1)
                           (x30 : A1)
                           (x31 : x7 x29 x30)
                      : Type -> x7 (x4 x28 x29) (x4 x28 x30))
             (A2 : Type)
             (x32 : A2)
             (x33 : forall (x34 : A2)
                           (x35 : A2)
                      : Type -> A2)
             (x36 : forall (x37 : A1)
                           (x38 : A2)
                      : Kind -> Type)
             (x39 : forall (x40 : forall (x41 : A1) : Type -> A1)
                           (x42 : A2)
                           (x43 : A2)
                           (x44 : forall (x45 : A1)
                                         (x46 : x36 x45 x42)
                                    : Type -> x36 (x40 x45) x43)
                      : Type -> x36 (x1 x40) (x33 x42 x43))
             (x47 : forall (x48 : A1)
                           (x49 : A1)
                           (x50 : A2)
                           (x51 : A2)
                           (x52 : x36 x48 (x33 x50 x51))
                           (x53 : x36 x49 x50)
                      : Type -> x36 (x4 x48 x49) x51)
        : Kind -> Type
      : Kind
    Normalized Result:
      forall (A1 : Type)
             (x1 : forall (x2 : forall (x3 : A1) : Type -> A1) : Type -> A1)
             (x4 : forall (x5 : A1)
                          (x6 : A1)
                     : Type -> A1)
             (x7 : forall (x8 : A1)
                          (x9 : A1)
                     : Kind -> Type)
             (x10 : forall (x11 : forall (x12 : A1) : Type -> A1)
                           (x13 : A1)
                      : Type -> x7
                                  (x4
                                     (x1
                                       (fun (x14 : A1) : Type -> (x11 x14 : A1)))
                                    x13)
                                  (x11 x13))
             (x15 : forall (x16 : forall (x17 : A1) : Type -> A1)
                           (x18 : forall (x19 : A1) : Type -> A1)
                           (x20 : forall (x21 : A1)
                                         (x22 : x7 x21 x21)
                                    : Type -> x7 (x16 x21) (x18 x21))
                      : Type -> x7 (x1 (fun (x23 : A1) : Type -> (x16 x23 : A1)))
                                  (x1 (fun (x24 : A1) : Type -> (x18 x24 : A1))))
             (x25 : forall (x26 : A1)
                           (x27 : A1)
                           (x28 : A1)
                           (x29 : x7 x26 x27)
                      : Type -> x7 (x4 x26 x28) (x4 x27 x28))
             (x30 : forall (x31 : A1)
                           (x32 : A1)
                           (x33 : A1)
                           (x34 : x7 x32 x33)
                      : Type -> x7 (x4 x31 x32) (x4 x31 x33))
             (A2 : Type)
             (x35 : A2)
             (x36 : forall (x37 : A2)
                           (x38 : A2)
                      : Type -> A2)
             (x39 : forall (x40 : A1)
                           (x41 : A2)
                      : Kind -> Type)
             (x42 : forall (x43 : forall (x44 : A1) : Type -> A1)
                           (x45 : A2)
                           (x46 : A2)
                           (x47 : forall (x48 : A1)
                                         (x49 : x39 x48 x45)
                                    : Type -> x39 (x43 x48) x46)
                      : Type -> x39
                                  (x1 (fun (x50 : A1) : Type -> (x43 x50 : A1)))
                                  (x36 x45 x46))
             (x51 : forall (x52 : A1)
                           (x53 : A1)
                           (x54 : A2)
                           (x55 : A2)
                           (x56 : x39 x52 (x36 x54 x55))
                           (x57 : x39 x53 x54)
                      : Type -> x39 (x4 x52 x53) x55)
        : Kind -> Type
      : Kind
    |}]

let%expect_test "plus.lf works" = 
  let _ = main_of_example "plus.lf" in
  [%expect
    {|
    Parsed:
      forall (nat : Type)
             (z : nat)
             (s : forall (n : nat) : Type -> nat)
             (plus : forall (m : nat)
                            (n : nat)
                            (p : nat)
                       : Kind -> Type)
             (p_z : forall (N : nat) : Type -> plus z N N)
             (p_s : forall (N1 : nat)
                           (N2 : nat)
                           (N3 : nat)
                           (p1 : plus N1 N2 N3)
                      : Type -> plus (s N1) N2 (s N3))
             (#is_var : forall (#_ : forall (N : nat)
                                       : Type -> plus (s z) N (s N))
                          : Kind -> Type)
             (p_sz_n_sn : #is_var
                            (fun (N : nat)
                              : Type -> (p_s z N N (p_z N) : plus (s z) N (s N))))
        : Kind -> Type
      : Kind
    Elaborated:
      forall (A1 : Type)
             (x1 : A1)
             (x2 : forall (x3 : A1) : Type -> A1)
             (x4 : forall (x5 : A1)
                          (x6 : A1)
                          (x7 : A1)
                     : Kind -> Type)
             (x8 : forall (x9 : A1) : Type -> x4 x1 x9 x9)
             (x10 : forall (x11 : A1)
                           (x12 : A1)
                           (x13 : A1)
                           (x14 : x4 x11 x12 x13)
                      : Type -> x4 (x2 x11) x12 (x2 x13))
             (x15 : forall (x16 : forall (x17 : A1)
                                    : Type -> x4 (x2 x1) x17 (x2 x17))
                      : Kind -> Type)
             (x18 : x15
                      (fun (x19 : A1)
                        : Type -> (x10 x1 x19 x19 (x8 x19) : x4 (x2 x1) x19
                                                               (x2 x19))))
        : Kind -> Type
      : Kind
    Normalized Result:
      forall (A1 : Type)
             (x1 : A1)
             (x2 : forall (x3 : A1) : Type -> A1)
             (x4 : forall (x5 : A1)
                          (x6 : A1)
                          (x7 : A1)
                     : Kind -> Type)
             (x8 : forall (x9 : A1) : Type -> x4 x1 x9 x9)
             (x10 : forall (x11 : A1)
                           (x12 : A1)
                           (x13 : A1)
                           (x14 : x4 x11 x12 x13)
                      : Type -> x4 (x2 x11) x12 (x2 x13))
             (x15 : forall (x16 : forall (x17 : A1)
                                    : Type -> x4 (x2 x1) x17 (x2 x17))
                      : Kind -> Type)
             (x18 : x15
                      (fun (x19 : A1)
                        : Type -> (x10 x1 x19 x19 (x8 x19) : x4 (x2 x1) x19
                                                               (x2 x19))))
        : Kind -> Type
      : Kind
    |}]
