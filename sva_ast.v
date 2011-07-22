(** * SVA-AST *)

(** Contains definitions for the "SVA" language. *)

Add LoadPath "./CompCert-Toolkit".
Require Import Coqlib.

Definition var := positive.
Definition nodevar := positive.

Inductive value : Type :=
  | Uninit : value
  | Int : nat -> value
  | Region : nodevar -> value.

Inductive tipe : Type :=
  | Int_t : tipe
  | Char_t : tipe
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
  | Gte : binop.

Inductive exp : Type :=
  | Var : var -> exp
  | Val : value -> exp
  | Binop : exp -> binop -> exp -> exp
  | Load : exp -> exp
  | LoadFromU : exp -> exp -> exp
  | Loadc : exp -> exp
  | LoadcFromU : exp -> exp -> exp
  | Cast : exp -> tipe -> exp
  | PoolAlloc : exp -> exp -> exp
  | Addr : exp -> exp -> exp -> exp
  | CastI2Ptr : exp -> exp -> tipe -> exp.

Inductive value_v : value -> Prop :=
  | Uninit_v : value_v Uninit
  | Int_v : forall n,
      value_v (Int n)
  | Region_v : forall rho,
      value_v (Region rho).

Inductive stmt : Type :=
  | Epsilon : stmt
  | Seq : stmt -> stmt -> stmt
  | Assign : var -> exp -> stmt
  | Store : exp -> exp -> stmt
  | StoreToU : exp -> exp -> exp -> stmt
  | Storec : exp -> exp -> stmt
  | StorecToU : exp -> exp -> exp -> stmt
  | PoolFree : exp -> exp -> stmt
  | PoolInit : nodevar -> tipe -> var -> stmt -> stmt
  | PoolPop : stmt -> nodevar -> stmt.
