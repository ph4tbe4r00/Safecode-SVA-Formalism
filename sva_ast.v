(** * SVA-AST *)

(* Contains definitions for the "SVA" language. 
 * 
 * Notes: Taken straight from SafeCode paper. We removed characters as a
 * primitive type because it doesn't say anything interesting about what
 * pool allocation does. *)

Add LoadPath "./CompCert-Toolkit".
Require Import Coqlib.
Require Import Integers.
Require Import Values.

Definition var := positive.
Definition nodevar := positive.

Inductive value : Type :=
  | Uninit : value                   (* unitialized *)
  | Int : int -> value               (* 32-bit machine integer *)
  | Byte : byte -> value             (* 8-bit machine integer *)
  | Pointer : block -> int -> value  (* CompCert pointer *)
  | Region : nodevar -> value.       (* region handle *)

Inductive value_v : value -> Prop :=
  | Uninit_v : value_v Uninit
  | Int_v : forall n,
      value_v (Int n)
  | Byte_v : forall n,
      value_v (Byte n)
  | Pointer_v : forall b n,
      value_v (Pointer b n)
  | Region_v : forall rho,
      value_v (Region rho).

Inductive tipe : Type :=
  | Int_t : tipe
(*  | Char_t : tipe  *)
  | Unknown_t : tipe
  | Pts_t : tipe -> nodevar -> tipe
  | Handle_t : nodevar -> tipe -> tipe.

Inductive binop : Type :=
  | Plus : binop
  | Minus : binop
  | Times : binop
  | Div : binop
  | Eq : binop
  | Neq : binop
  | Lt : binop
  | Lte : binop
  | Gt : binop
  | Gte : binop
  | Plus_ptr : binop.

Inductive exp : Type :=
  | Var : var -> exp
  | Val : value -> exp
  | Binop : exp -> binop -> exp -> exp
  | Load : exp -> exp
  | LoadFromU : exp -> exp -> exp
(*  | Loadc : exp -> exp  *)
(*  | LoadcFromU : exp -> exp -> exp  *)
  | Cast : exp -> tipe -> exp
  | PoolAlloc : exp -> exp -> exp 
(*  | Addr : exp -> exp -> exp -> exp  *)
  | CastI2Ptr : exp -> exp -> tipe -> exp
  | ErrorExp : exp. (* Error state, program should never have this as an expression *)

Inductive stmt : Type :=
  | Epsilon : stmt
  | Seq : stmt -> stmt -> stmt
  | Assign : var -> exp -> stmt
  | Store : exp -> exp -> stmt
  | StoreToU : exp -> exp -> exp -> stmt
(*  | Storec : exp -> exp -> stmt  *)
(*  | StorecToU : exp -> exp -> exp -> stmt  *)
  | PoolFree : exp -> exp -> stmt
  | PoolInit : nodevar -> tipe -> var -> stmt -> stmt
  | PoolPop : stmt -> nodevar -> stmt
  | ErrorStmt : stmt. (* Error state, program should never have this as a statment *)
