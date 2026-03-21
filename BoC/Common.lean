import Mathlib.Logic.Relation

@[reducible]
def Cown := Nat

def c0 : Cown := 0
def c1 : Cown := 1
def c2 : Cown := 2
def c3 : Cown := 3
def c4 : Cown := 4

@[reducible]
def BId := Nat

def b0 : BId := 0
def b1 : BId := 1
def b2 : BId := 2
def b3 : BId := 3
def b4 : BId := 4

-- TODO: This stuff is in Mathlib, but I couldn't get it to work properly.
@[simp]
def is_reflective {α : Type} (r : α → α → Prop) : Prop :=
  ∀a : α, r a a

@[simp]
def is_transitive {α : Type} (r : α → α → Prop) : Prop :=
  ∀a b c : α, r a b → r b c → r a c

@[simp]
def is_antisymmetric {α : Type} (r : α → α → Prop) : Prop :=
  ∀a b : α, r a b → r b a → a = b

structure is_partial_order {α : Type} (r : α → α → Prop) : Prop where
  mk ::
  is_reflective : is_reflective r
  is_transitive : is_transitive r
  is_antisymmetric : is_antisymmetric r

structure is_strict_partial_order {α : Type} (r : α → α → Prop) : Prop where
  mk ::
  is_reflective : is_reflective r
  is_transitive : is_transitive r
  is_antisymmetric : is_antisymmetric r

@[reducible]
def is_acyclic {α : Type} (r : α → α → Prop) : Prop :=
  ∀a b, ¬(r a b ∧ r b a ∧ a ≠ b)

theorem is_partial_order_is_acyclic {α : Type} {r : α → α → Prop} :
    is_partial_order r →
    is_acyclic r :=
  by
    intro h_po a b h_contra
    rcases h_contra with ⟨h_ab, h_ba, h_neq⟩
    have h_ba := h_po.is_antisymmetric a b h_ab
    grind

theorem is_strict_partial_order_is_acyclic {α : Type} {r : α → α → Prop} :
    is_strict_partial_order r →
    is_acyclic r :=
  by
    intro h_po a b h_contra
    rcases h_contra with ⟨h_ab, h_ba, h_neq⟩
    have h_ba := h_po.is_antisymmetric a b h_ab
    grind

-- Notations for relations
instance RelationUnionInst {α : Type*} : Union (α → α → Prop) where
  union r1 r2 := fun a b => r1 a b ∨ r2 a b

infixr:80 " ∘ "  => Relation.Comp
postfix:80 " + " => Relation.TransGen
postfix:80 " * " => Relation.ReflTransGen

/-
theorem non_empty_middle_inv {A : Type} {l : List A} :
    List.length l > 0 →
    ∃ l1 x l2, l = l1 ++ x :: l2 :=
    by
    intro h_len
    cases l with
    | nil => simp at *
    | cons hd tl =>
      exists [], hd, tl
-/
