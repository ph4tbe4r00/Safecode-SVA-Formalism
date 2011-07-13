Require String.

Definition var := String.string.
Definition nodevar := String.string.

Inductive value : Type :=
  | Uninit_v : value
  | Int_v : value
  | Region_v : nodevar -> value.

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
  | Var : exp
  | Val : exp
  | Binop : exp -> binop -> exp -> exp
  | Load : exp -> exp
  | LoadFromU : var -> exp -> exp
  | Loadc : exp -> exp
  | LoadcFromU : exp -> exp
  | Cast : exp -> tipe -> exp
  | PoolAlloc : var -> exp -> exp
  | Addr : var -> exp -> exp -> exp
  | CastI2Ptr : var -> exp -> tipe -> exp.

Inductive stmt : Type :=
  | Epsilon : stmt
  | Seq : stmt -> stmt -> stmt
  | Assign : var -> exp -> stmt
  | Store : exp -> exp -> stmt
  | StoreToU : var -> exp -> exp -> stmt
  | Storec : exp -> exp -> stmt
  | StorecToU : exp -> exp -> stmt
  | PoolFree : exp -> exp -> stmt
  | PoolInit : nodevar -> tipe -> var -> stmt -> stmt
  | PoolPop : stmt -> nodevar -> stmt.
