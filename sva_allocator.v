Add LoadPath "./CompCert-Toolkit".
Require Import Coqlib.
Require Import Integers.

(* Allocator for a pool. By automatic pool allocation, each pool is a 
 * block of memory that is completely isolated from any other pool.
 * This allocates offsets into the pool. *) 

(* An allocator for a specific pool contains the next offset to be
 * given out and a freelist *)
Record Allocator : Type := mk_allocator {
  offset : Z;       (* offset is modeled as mathematical integer *)
  freelist : list Z (* list containing freed addresses *)  
}.

(* Initialize a new allocator for a pool *)
Definition new_allocator :=
  (mk_allocator 0 nil).

(* First try to allocate from the free list. Otherwise, hand out the
 * next address. If there are no free addresses, return None. *)
Definition alloc_1 (a : Allocator) : option (int * Allocator) := 
  match (freelist a) with
  | nil => 
      if Zge_bool (offset a) Int.modulus
      then None
      else Some (Int.repr (offset a), mk_allocator (Zsucc (offset a)) (freelist a))
  | addr::fl => Some ((Int.repr addr, mk_allocator (offset a) fl))
  end.

(* See if we can allocate n-units. If we can, hand out the first address
 * to the contiguous chunk of addresses given out. *)
Definition alloc_n (a : Allocator) (n : Z) : option (int * Allocator) :=
  if Zge_bool ((offset a) + n - 1) Int.modulus
  then None
  else Some (Int.repr (offset a), mk_allocator ((offset a) + n) (freelist a)).

Definition alloc (a : Allocator) (n : Z) : option (int * Allocator) :=
  if Zeq_bool n 1 then alloc_1 a else alloc_n a n.

(* Adds the address to the free list *)
Definition free (a : Allocator) (n : int) : Allocator :=
  mk_allocator (offset a) ((Int.unsigned n)::(freelist a)).
