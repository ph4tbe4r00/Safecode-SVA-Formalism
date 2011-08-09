(** * SVA allocator *)

(* CompCert imports *)
Add LoadPath "./CompCert-Toolkit".
Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.

Require Import sva_ast.

Definition val2CCval (v : sva_ast.value) : Values.val := 
  match v with
  | Uninit => Vundef 
  | Int n => Vint n
  | Byte _ => Vundef (* not right? *)
  | Pointer b ofs => Vptr b ofs
  | Region _ => Vundef (* not right? *)
  end.

Definition CCval2val (v : Values.val) : (sva_ast.value) :=
  match v with
  | Vundef => Uninit
  | Vint n => Int n
  | Vptr b ofs => Pointer b ofs
  | Vfloat _ => Uninit
  end.

Record sva_heap : Type := mk_sva_heap {
  sva_mem : Mem.mem;    (* CompCert memory *)
  size_map : ZMap.t Z   (* block -> size (default is -1) *)
}.

Definition sva_init_heap :=
  (mk_sva_heap Mem.empty (ZMap.init (-1))).

(* Allocates CompCert block of size s bytes, offset starting at 0 *)
Definition sva_alloc (h : sva_heap) (size : Z) : (sva_heap * Values.block) :=
  let (mem', b) := Mem.alloc (sva_mem h) 0 size in
  (mk_sva_heap mem' (ZMap.set b size (size_map h)), b).

Definition sva_store (h : sva_heap) (b : Values.block) (ofs : int)
                     (c : AST.memory_chunk) (v : sva_ast.value) : sva_heap :=
  let opt_mem := Mem.store c (sva_mem h) b (Int.unsigned ofs) (val2CCval v) in
  match opt_mem with
  | None => h
  | Some mem' => mk_sva_heap mem' (size_map h)
  end.

Definition sva_load (h : sva_heap) (b : Values.block) (ofs : int)
                    (c : AST.memory_chunk) : option sva_ast.value :=
  let opt_val := Mem.load c (sva_mem h) b (Int.unsigned ofs) in
  match opt_val with
  | None => None
  | Some v => Some (CCval2val v)
  end.