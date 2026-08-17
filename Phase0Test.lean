import Lean

open Lean Elab Command

/-! Phase 0 test module for the Rust reimplementation of lean4export.

This module declares constants of every kind that the NDJSON export format
supports, so that golden reference outputs can be generated and diffed
byte-for-byte against the Rust implementation.
-/

namespace Phase0Test

/-! ## Axioms -/

axiom myAxiom (n : Nat) : Nat

axiom myAxiomPoly.{u} (α : Sort u) : α

/-! ## Definitions -/

def myDef (n : Nat) : Nat := n + 1

abbrev myAbbrev (n : Nat) : Nat := n

def polyId.{u} (α : Sort u) (a : α) : α := a

def withLet (n : Nat) : Nat :=
  let x := n + 1
  x + 1

def withNatLit : Nat := 42

def withBigNat : Nat := 100000000000000023456789

def withStrLit : String := "hello"

/-! ## Opaques -/

opaque myOpaque : Nat → Nat

opaque myOpaqueImpl : Nat → Nat := fun n => n + 1

/-! ## Theorems -/

theorem myThm (n : Nat) : n = n := rfl

theorem polyThm.{u} (α : Sort u) : True := True.intro

/-! ## Unsafe / partial -/

unsafe def myUnsafe : Nat := 0

partial def myPartial (n : Nat) : Nat := myPartial n

unsafe inductive UnsafeInd where
  | mk : UnsafeInd

/-! ## Inductives -/

inductive MyInd where
  | mk : Nat → MyInd

mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end

/-! Reflexive inductive (Acc-like). -/
inductive MyAcc (r : Nat → Nat → Prop) : Nat → Prop where
  | intro : ∀ {x : Nat}, (∀ y, r y x → MyAcc r y) → MyAcc r x

/-! Nested inductive. -/
inductive NestedInd where
  | mk : List NestedInd → NestedInd

/-! ## Structures (inductive with projections) -/

structure MyStruct where
  x : Nat
  y : String

def useStruct (s : MyStruct) : Nat := s.x

/-! ## Quotient reference -/

def useQuot (r : Nat → Nat → Prop) : Quot r → Quot r := id

/-! ## Deep expression (>1000 nested binders, exercises the isDeepExpr path) -/

elab "mk_deep_axiom" n:ident : command => do
  let name := n.getId
  let mut ty : Expr := mkSort Level.zero
  for i in List.range 1500 do
    ty := mkForall (Name.mkNum `x i) .default (mkSort Level.zero) ty
  liftCoreM <| addDecl <| Declaration.axiomDecl {
    name := name, levelParams := [], type := ty, isUnsafe := false }

mk_deep_axiom deepAxiom

end Phase0Test
