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

instance BIdDecEq : DecidableEq BId := by
  intros bid1 bid2
  apply Nat.decEq

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


-- Relation lemmas
lemma rel_clos_weaken {A} {R S : A → A → Prop} {x y : A} :
  (∀x y, R x y → S x y) →
  (R*) x y →
  (S*) x y :=
  by
    introv h_subset h_clos
    induction h_clos with
    | refl => constructor
    | @tail z w h_clos h_infix ih =>
      apply Relation.ReflTransGen.tail ih
      apply h_subset
      assumption

lemma rel_trans_clos_weaken {A} {R S : A → A → Prop} {x y : A} :
  (∀x y, R x y → S x y) →
  (R+) x y →
  (S+) x y :=
  by
    introv h_subset h_clos
    induction h_clos with
    | single h_infix =>
      constructor
      apply h_subset
      assumption
    | @tail z w h_clos h_infix ih =>
      apply Relation.TransGen.tail ih
      apply h_subset
      assumption

lemma refl_trans_clos_exists_pick {A} {B} {x y : A} {P : A → A → B → Prop} {b : B} :
    ((fun e1 e2 ↦ P e1 e2 b)*) x y →
    ((fun e1 e2 ↦ ∃ b, P e1 e2 b)*) x y :=
  by
    introv h_clos
    induction h_clos with
    | refl => constructor
    | @tail z w h_clos h_infix ih =>
      apply Relation.ReflTransGen.tail ih
      exists b

lemma trans_clos_exists_pick {A} {B} {x y : A} {P : A → A → B → Prop} {b : B} :
    ((fun e1 e2 ↦ P e1 e2 b)+) x y →
    ((fun e1 e2 ↦ ∃ b, P e1 e2 b)+) x y :=
  by
    introv h_clos
    induction h_clos with
    | @single a =>
      constructor
      exists b
    | @tail z w h_clos h_infix ih =>
      apply Relation.TransGen.tail ih
      exists b

-- List lemmas
lemma pair_infix_inv {A} {l : List A} {x1 x2} :
    [x1, x2] <:+: l →
    (∃l', l = x1 :: x2 :: l') ∨ [x1, x2] <:+: l.tail :=
  by
    introv h_infix
    rcases h_infix with ⟨init, tail, h_eq⟩
    subst h_eq
    cases init with
    | nil => left; simp
    | cons y ys =>
      right; simp
      exists ys, tail
      simp

lemma pair_infix_mem {A} {l : List A} {x1 x2} :
    [x1, x2] <:+: l →
    x1 ∈ l ∧ x2 ∈ l :=
  by
    introv h_infix
    rcases h_infix with ⟨init, tail, h_eq⟩
    subst h_eq
    simp

lemma no_dup_pair_eq_r {A} {l : List A} {x1 x2 x3} :
    List.Pairwise (· ≠ ·) l →
    [x1, x2] <:+: l →
    [x1, x3] <:+: l →
    x2 = x3 :=
  by
    introv h_no_dup h_in1 h_in2
    induction l with
    | nil =>
      simp at h_in1
    | cons y ys h_ih =>
      simp at h_no_dup
      rcases h_no_dup with ⟨h_nin, h_no_dup'⟩
      have h_or1 := pair_infix_inv h_in1
      have h_or2 := pair_infix_inv h_in2
      cases h_or1 with
      | inl h_ex1 =>
        rcases h_ex1 with ⟨l', h_eq1⟩
        cases h_or2 with
        | inl h_ex2 =>
          rcases h_ex2 with ⟨l'', h_eq2⟩
          rw [h_eq1] at h_eq2
          simp at h_eq2
          exact h_eq2.1
        | inr h_infix2 =>
          simp at h_infix2
          have h_y_eq : y = x1 := by
            simp at h_eq1
            exact h_eq1.1
          have h_x1_nin : x1 ∉ ys := by
            intro h_mem
            exact (h_nin x1 h_mem) h_y_eq
          have h_x1_mem : x1 ∈ ys := by
            rcases h_infix2 with ⟨init, tail, h_eq⟩
            rw [← h_eq]
            simp
          exfalso
          exact h_x1_nin h_x1_mem
      | inr h_infix1 =>
        cases h_or2 with
        | inl h_ex2 =>
          rcases h_ex2 with ⟨l'', h_eq2⟩
          have h_y_eq : y = x1 := by
            simp at h_eq2
            exact h_eq2.1
          have h_x1_nin : x1 ∉ ys := by
            intro h_mem
            exact (h_nin x1 h_mem) h_y_eq
          simp at h_infix1
          have h_x1_mem : x1 ∈ ys := by
            rcases h_infix1 with ⟨init, tail, h_eq⟩
            rw [← h_eq]
            simp
          exfalso
          exact h_x1_nin h_x1_mem
        | inr h_infix2 =>
          exact h_ih h_no_dup' h_infix1 h_infix2

lemma no_dup_pair_eq_l {A} {l : List A} {x1 x2 x3} :
    List.Pairwise (· ≠ ·) l →
    [x1, x3] <:+: l →
    [x2, x3] <:+: l →
    x1 = x2 :=
  by
    introv h_no_dup h_in1 h_in2
    induction l with
    | nil =>
      simp at h_in1
    | cons y ys h_ih =>
      simp at h_no_dup
      rcases h_no_dup with ⟨h_nin, h_no_dup'⟩
      have h_or := pair_infix_inv h_in1
      cases h_or with
      | inl h_ex =>
        rcases h_ex with ⟨l', h_eq⟩
        rw [h_eq] at h_in2
        have h_or' := pair_infix_inv h_in2
        cases h_or' with
        | inl h_ex' =>
          grind
        | inr h_infix' =>
          simp at h_infix'
          simp at h_eq
          rcases h_eq with ⟨h_eq_y, h_eq_ys⟩
          subst h_eq_y
          subst h_eq_ys
          have h_in : x3 ∈ l' := by
            rcases h_infix' with ⟨init, tail, h_eq⟩
            rcases init <;> grind
          simp at h_no_dup'
          grind
      | inr h_infix =>
        simp at h_infix
        have h_or' := pair_infix_inv h_in2
        cases h_or' with
        | inl h_ex =>
          rcases h_ex with ⟨l', h_eq⟩
          simp at h_eq
          rcases h_eq with ⟨h_eq_y, h_eq_ys⟩
          subst h_eq_y
          subst h_eq_ys
          have h_in : x3 ∈ l' := by
            rcases h_infix with ⟨init, tail, h_eq⟩
            rcases init <;> grind
          simp at h_no_dup'
          grind
        | inr h_infix' =>
          simp at h_infix'
          grind

lemma pair_sublist_iff {A} {l : List A} {x1 x2} :
    [x1, x2].Sublist l ↔
    (∃init mid tail, l = init ++ x1 :: mid ++ x2 :: tail) :=
  by
    refine ⟨?_, ?_⟩
    · introv h_sub
      induction l with
      | nil => simp at h_sub
      | cons y ys =>
        by_cases h_eq : (y = x1)
        · subst h_eq
          rw [List.cons_sublist_cons] at h_sub
          simp at h_sub

          exists []
          simp
          exact List.mem_iff_append.mp h_sub
        · cases h_sub <;> grind
    · introv h_ex
      rcases h_ex with ⟨init, mid, tail, h_eq⟩
      subst h_eq
      simp

lemma no_dup_middle_inv {A} {x : A} {l1 l2 l1' l2' : List A} :
  List.Pairwise (· ≠ ·) (l1 ++ x :: l2) →
  l1 ++ x :: l2 = l1' ++ x :: l2' →
  l1 = l1' ∧ l2 = l2' :=
  by
    introv h_no_dup h_eq
    induction l1 generalizing l1' with
    | nil =>
      cases l1' with
      | nil =>
        simp at h_eq
        subst h_eq
        simp
      | cons a l1'' =>
        simp at h_eq
        rcases h_eq with ⟨h_xa, h_rest⟩
        have h_x_nin : x ∉ l2 := by
          intro h_mem
          exact ((List.pairwise_cons.1 h_no_dup).1 x h_mem) rfl
        have h_x_mem : x ∈ l2 := by
          rw [h_rest]
          simp
        exfalso
        exact h_x_nin h_x_mem
    | cons a l1 ih =>
      cases l1' with
      | nil =>
        simp at h_eq
        rcases h_eq with ⟨h_ax, h_rest⟩
        have h_a_nin : a ∉ l1 ++ x :: l2 := by
          intro h_mem
          exact ((List.pairwise_cons.1 h_no_dup).1 a h_mem) rfl
        have h_a_mem : a ∈ l1 ++ x :: l2 := by
          rw [h_ax]
          simp
        exfalso
        exact h_a_nin h_a_mem
      | cons a' l1'' =>
        simp at h_eq
        rcases h_eq with ⟨h_head, h_tail⟩
        subst h_head
        have h_no_dup_tail : List.Pairwise (· ≠ ·) (l1 ++ x :: l2) := by
          simpa [List.cons_append] using (List.pairwise_cons.1 h_no_dup).2
        rcases ih h_no_dup_tail h_tail with ⟨h_l1, h_l2⟩
        constructor
        · simp [h_l1]
        · exact h_l2

lemma pair_infix_refl_trans_clos_append_left {A} {l1 l2 : List A} {x y} :
  ((fun e1 e2 ↦ [e1, e2] <:+: l1)*) x y →
  ((fun e1 e2 ↦ [e1, e2] <:+: l1 ++ l2)*) x y :=
  by
    intro h_clos
    induction h_clos with
    | refl =>
      constructor
    | @tail b c h_clos h_infix ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases h_infix with ⟨init, tail, h_eq⟩
      refine ⟨init, tail ++ l2, ?_⟩
      rw [← h_eq]
      simp [List.append_assoc]

lemma pair_infix_refl_trans_clos_append_right {A} {l1 l2 : List A} {x y} :
  ((fun e1 e2 ↦ [e1, e2] <:+: l2)*) x y →
  ((fun e1 e2 ↦ [e1, e2] <:+: l1 ++ l2)*) x y :=
  by
    intro h_clos
    induction h_clos with
    | refl =>
      constructor
    | @tail b c h_clos h_infix ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases h_infix with ⟨init, tail, h_eq⟩
      refine ⟨l1 ++ init, tail, ?_⟩
      rw [← h_eq]
      simp [List.append_assoc]

lemma pair_infix_trans_clos_append_left {A} {l1 l2 : List A} {x y} :
  ((fun e1 e2 ↦ [e1, e2] <:+: l1)+) x y →
  ((fun e1 e2 ↦ [e1, e2] <:+: l1 ++ l2)+) x y :=
  by
    intro h_clos
    induction h_clos with
    | @single a h_infix =>
      apply Relation.TransGen.single
      rcases h_infix with ⟨init, tail, h_eq⟩
      refine ⟨init, tail ++ l2, ?_⟩
      rw [← h_eq]
      simp [List.append_assoc]
    | @tail b c h_clos h_infix ih =>
      refine Relation.TransGen.tail ih ?_
      rcases h_infix with ⟨init, tail, h_eq⟩
      refine ⟨init, tail ++ l2, ?_⟩
      rw [← h_eq]
      simp [List.append_assoc]

lemma pair_infix_trans_clos_append_right {A} {l1 l2 : List A} {x y} :
  ((fun e1 e2 ↦ [e1, e2] <:+: l2)+) x y →
  ((fun e1 e2 ↦ [e1, e2] <:+: l1 ++ l2)+) x y :=
  by
    intro h_clos
    induction h_clos with
    | @single a h_infix =>
      apply Relation.TransGen.single
      rcases h_infix with ⟨init, tail, h_eq⟩
      refine ⟨l1 ++ init, tail, ?_⟩
      rw [← h_eq]
      simp [List.append_assoc]
    | @tail b c h_clos h_infix ih =>
      refine Relation.TransGen.tail ih ?_
      rcases h_infix with ⟨init, tail, h_eq⟩
      refine ⟨l1 ++ init, tail, ?_⟩
      rw [← h_eq]
      simp [List.append_assoc]

lemma pair_infix_clos_middle {A} {x y : A} {mid tail : List A} :
  ((fun e1 e2 ↦ [e1, e2] <:+: (x :: mid ++ y :: tail))*) x y :=
  by
    induction mid generalizing x with
    | nil =>
      refine Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) ?_
      refine ⟨[], tail, ?_⟩
      simp
    | cons z zs ih =>
      have h_tail :
          ((fun e1 e2 ↦ [e1, e2] <:+: (z :: zs ++ y :: tail))*) z y := by
        exact ih
      have h_tail' :
          ((fun e1 e2 ↦ [e1, e2] <:+: (x :: z :: zs ++ y :: tail))*) z y := by
        simpa using
          (pair_infix_refl_trans_clos_append_right
            (l1 := [x])
            (l2 := z :: zs ++ y :: tail)
            h_tail)
      have h_xz : [x, z] <:+: (x :: z :: zs ++ y :: tail) := by
        refine ⟨[], zs ++ y :: tail, ?_⟩
        simp
      have h_xz_clos :
          ((fun e1 e2 ↦ [e1, e2] <:+: (x :: z :: zs ++ y :: tail))*) x z := by
        exact Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) h_xz
      exact Relation.ReflTransGen.trans h_xz_clos h_tail'

lemma pair_infix_trans_clos_middle {A} {x y : A} {mid tail : List A} :
  ((fun e1 e2 ↦ [e1, e2] <:+: (x :: mid ++ y :: tail))+) x y :=
  by
    induction mid generalizing x with
    | nil =>
      apply Relation.TransGen.single
      refine ⟨[], tail, ?_⟩
      simp
    | cons z zs ih =>
      have h_tail :
          ((fun e1 e2 ↦ [e1, e2] <:+: (z :: zs ++ y :: tail))+) z y := by
        exact ih
      have h_tail' :
          ((fun e1 e2 ↦ [e1, e2] <:+: (x :: z :: zs ++ y :: tail))+) z y := by
        simpa using
          (pair_infix_trans_clos_append_right
            (l1 := [x])
            (l2 := z :: zs ++ y :: tail)
            h_tail)
      have h_xz : [x, z] <:+: (x :: z :: zs ++ y :: tail) := by
        refine ⟨[], zs ++ y :: tail, ?_⟩
        simp
      exact Relation.TransGen.trans (Relation.TransGen.single h_xz) h_tail'

lemma pair_refl_trans_iff {A} {x y : A} {l} :
  List.Pairwise (· ≠ ·) l →
  (((fun e1 e2 ↦ [e1, e2] <:+: l)*) x y ↔
  x = y ∨ List.Sublist [x, y] l) :=
  by
    introv h_no_dup
    refine ⟨?_, ?_⟩
    · intro h_clos
      induction h_clos with
      | refl => simp
      | @tail b c h_clos h_infix ih =>
        rcases ih with (h_eq | h_sub)
        · subst h_eq
          right
          exact List.IsInfix.sublist h_infix
        · right
          rcases h_infix with ⟨init, tail, h_eq⟩
          subst h_eq
          simp at *
          have h_nin : b ∉ init ∧ b ∉ tail := by
            rw [List.pairwise_append] at h_no_dup
            simp at h_no_dup
            grind
          rw [pair_sublist_iff] at h_sub
          rcases h_sub with ⟨init', mid, tail', h_eq'⟩
          have ⟨h_l1, h_l2⟩ := no_dup_middle_inv (h_no_dup) h_eq'
          subst h_l1 h_l2
          grind
    · intro h_disj
      cases h_disj with
      | inl h_eq =>
        subst h_eq
        constructor
      | inr h_sub =>
        rw [pair_sublist_iff] at h_sub
        rcases h_sub with ⟨init, mid, tail, h_eq⟩
        subst h_eq
        simp [List.append_assoc]
        apply pair_infix_refl_trans_clos_append_right
        exact pair_infix_clos_middle

lemma pair_trans_iff {A} {x y : A} {l} :
  List.Pairwise (· ≠ ·) l →
  (((fun e1 e2 ↦ [e1, e2] <:+: l)+) x y ↔
  List.Sublist [x, y] l) :=
  by
    introv h_no_dup
    refine ⟨?_, ?_⟩
    · intro h_clos
      induction h_clos with
      | @single a h_infix =>
        exact List.IsInfix.sublist h_infix
      | @tail b c h_clos h_infix ih =>
        rcases h_infix with ⟨init, tail, h_eq⟩
        subst h_eq
        simp at *
        have h_nin : b ∉ init ∧ b ∉ tail := by
          rw [List.pairwise_append] at h_no_dup
          simp at h_no_dup
          grind
        rw [pair_sublist_iff] at ih
        rcases ih with ⟨init', mid, tail', h_eq'⟩
        have ⟨h_l1, h_l2⟩ := no_dup_middle_inv (h_no_dup) h_eq'
        subst h_l1 h_l2
        grind
    · intro h_sub
      rw [pair_sublist_iff] at h_sub
      rcases h_sub with ⟨init, mid, tail, h_eq⟩
      subst h_eq
      simp [List.append_assoc]
      apply pair_infix_trans_clos_append_right
      exact pair_infix_trans_clos_middle

lemma no_dup_lookup_disjoint {A} {l : List A} {x y : A} {i j : Nat} :
  List.Pairwise (· ≠ ·) l →
  l[i]? = some x →
  l[j]? = some y →
  i ≠ j →
  x ≠ y :=
  by
    introv h_no_dup h_lookup_i h_lookup_j h_neq
    induction l generalizing i j x y with
    | nil =>
      simp at h_lookup_i
    | cons a l ih =>
      rcases (List.pairwise_cons.1 h_no_dup) with ⟨h_notin, h_no_dup'⟩
      cases i with
      | zero =>
        simp at h_lookup_i
        subst h_lookup_i
        cases j with
        | zero =>
          exfalso
          contradiction
        | succ j =>
          simp at h_lookup_j
          intro h_eq
          subst h_eq
          have h_mem_a : a ∈ l := by
            exact (List.mem_iff_getElem?).2 ⟨j, h_lookup_j⟩
          grind
      | succ i =>
        simp at h_lookup_i
        cases j with
        | zero =>
          simp at h_lookup_j
          intro h_eq
          have h_mem_a : x ∈ l := (List.mem_iff_getElem?).2 ⟨i, h_lookup_i⟩
          grind
        | succ j =>
          simp at h_lookup_j
          apply ih h_no_dup' h_lookup_i h_lookup_j
          intro h_eq
          subst h_eq
          contradiction

lemma list_snoc_cases {A} {l : List A} :
  l = [] ∨ ∃l' x, l = l' ++ [x] :=
  by
    induction l with
    | nil => simp
    | cons y ys ih =>
      simp
      cases ih with
      | inl h_eq =>
        subst h_eq
        exists [], y
      | inr h_snoc =>
        rcases h_snoc with ⟨l', x, h_eq⟩
        subst h_eq
        exists (y :: l'), x

lemma list_snoc_eq_inv {A} {l1 l2 : List A} {x1 x2 : A} :
  l1 ++ [x1] = l2 ++ [x2] →
  (l1 = l2 ∧ x1 = x2) :=
  by
    simp

lemma pairwise_ne_of_pair_ordered {A} {ord : A → Nat} {l : List A} :
    (∀ e1 e2, [e1, e2] <:+: l → ord e1 < ord e2) →
    List.Pairwise (· ≠ ·) l := by
  intro h_ts
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons]
    refine ⟨?_, ih (fun e1 e2 h_inf => h_ts e1 e2 (by
      rcases h_inf with ⟨i, tl, h_eq⟩; subst h_eq; exact ⟨x :: i, tl, rfl⟩))⟩
    intro y h_mem
    rcases List.mem_iff_append.mp h_mem with ⟨mid, tl, h_eq⟩
    have h_path : ((fun e1 e2 => [e1, e2] <:+: (x :: xs))+) x y := by
      rw [h_eq]
      simpa [List.append_assoc] using
        pair_infix_trans_clos_middle (x := x) (y := y) (mid := mid) (tail := tl)
    have close_lt : ∀ {u v : A}, ((fun e1 e2 => [e1, e2] <:+: (x :: xs))+) u v → ord u < ord v := by
      intro u v h
      induction h with
      | single h => exact h_ts _ _ h
      | tail _ h ih_step => exact Nat.lt_trans ih_step (h_ts _ _ h)
    exact fun h_eq => (Nat.ne_of_lt (close_lt h_path)) (congrArg ord h_eq)

lemma head_lt_of_mem_ordered {A} {ord : A → Nat} {x : A} {xs : List A} {y : A} :
    y ∈ xs →
    (∀ e1 e2, [e1, e2] <:+: (x :: xs) → ord e1 < ord e2) →
    ord x < ord y := by
  intro h_mem h_ord
  rcases List.mem_iff_append.mp h_mem with ⟨mid, tail, h_split⟩
  have h_path : ((fun e1 e2 ↦ [e1, e2] <:+: (x :: xs))+) x y := by
    rw [h_split]
    simpa [List.append_assoc] using
      (pair_infix_trans_clos_middle (x := x) (y := y) (mid := mid) (tail := tail))
  have h_ord_path : ((fun e1 e2 ↦ ord e1 < ord e2)+) x y := by
    exact rel_trans_clos_weaken (fun _ _ h_infix => h_ord _ _ h_infix) h_path
  have h_close_lt :
      ∀ {u v : A}, ((fun e1 e2 ↦ ord e1 < ord e2)+) u v → ord u < ord v := by
    intro u v h_clos
    induction h_clos with
    | single h_step => exact h_step
    | tail h_prev h_step ih => exact Nat.lt_trans ih h_step
  exact h_close_lt h_ord_path

lemma list_order_lt_inv {A} {l : List A} {a b : A} {ord : A → ℕ} :
    ord a < ord b →
    a ∈ l →
    b ∈ l →
    (∀e1 e2, [e1, e2] <:+: l → ord e1 < ord e2) →
    ∃ init mid tail, l = init ++ a :: mid ++ b :: tail :=
  by
    induction l with
    | nil =>
      intro h_lt h_a_mem
      cases h_a_mem
    | cons x xs ih =>
      intro h_lt h_a_mem h_b_mem h_ord
      simp at h_a_mem h_b_mem
      cases h_a_mem with
      | inl h_ax =>
        subst h_ax
        cases h_b_mem with
        | inl h_bx =>
          subst h_bx
          exact False.elim (Nat.lt_irrefl _ h_lt)
        | inr h_b_tail =>
          rcases List.mem_iff_append.mp h_b_tail with ⟨mid, tail, h_split⟩
          exact ⟨[], mid, tail, by simp [h_split]⟩
      | inr h_a_tail =>
        cases h_b_mem with
        | inl h_bx =>
          subst h_bx
          have h_ba : ord b < ord a := head_lt_of_mem_ordered h_a_tail h_ord
          exact False.elim (Nat.lt_asymm h_lt h_ba)
        | inr h_b_tail =>
          have h_ord_tail :
              ∀e1 e2, [e1, e2] <:+: xs → ord e1 < ord e2 := by
            intro e1 e2 h_infix
            apply h_ord
            rcases h_infix with ⟨init, tail, h_eq⟩
            exact ⟨x :: init, tail, by simp [h_eq]⟩
          rcases ih h_lt h_a_tail h_b_tail h_ord_tail with ⟨init, mid, tail, h_eq⟩
          exact ⟨x :: init, mid, tail, by simp [h_eq, List.append_assoc]⟩

lemma list_index_lt_inv {A} {x y : A} {l : List A} {i j : Nat} :
  l[i]? = some x →
  l[j]? = some y →
  i < j →
  ∃init mid tail, l = init ++ x :: mid ++ y :: tail :=
  by
    introv h_i h_j h_lt
    induction l generalizing i j with
    | nil => rcases i <;> simp at h_i
    | cons z zs ih =>
      cases h_lt with
      | refl =>
        simp at h_i h_j
        cases i with
        | zero =>
          simp at h_i h_j
          subst h_i
          cases zs with
          | nil => simp at h_j
          | cons z' zs' =>
            simp at h_j
            subst h_j
            exists [], [], zs'
        | succ i' =>
          simp at h_i
          have ⟨init, mid, tail, h_eq⟩ := ih h_i h_j (by simp)
          subst h_eq
          grind
      | @step k h_le =>
        cases i with
        | zero =>
          simp at h_i h_j
          subst h_i
          have h_in : y ∈ zs := by
            grind
          have ⟨init, tail, h_eq⟩ : exists init tail, zs = init ++ y :: tail := by
            rcases List.mem_iff_append.mp h_in with ⟨init, tail, h_eq⟩
            exists init, tail
          subst h_eq
          exists [], init, tail
        | succ i' =>
          simp at h_i h_j
          have h_lt : i' < k := by grind
          have ⟨init, mid, tail, h_eq⟩ := ih h_i h_j h_lt
          grind

lemma list_two_pairs_inv {A} {a b c d : A} {l init init' tail tail' : List A} :
  a ≠ c →
  a ≠ d →
  b ≠ c →
  l = init' ++ a :: b :: tail' →
  l = init ++ c :: d :: tail →
  (∃init'' mid tail'', l = init'' ++ a :: b :: mid ++ c :: d :: tail'') ∨
  (∃init'' mid tail'', l = init'' ++ c :: d :: mid ++ a :: b :: tail'') :=
  by
    intro h_ac h_ad h_bc h_ab h_cd
    induction init' generalizing l init with
    | nil =>
      simp at h_ab
      rcases init with _ | ⟨x, init'⟩ <;> simp at h_cd; · grind
      rcases init' with _ | ⟨y, init''⟩ <;> simp at h_cd; · grind
      subst h_cd
      simp at h_ab
      rcases h_ab with ⟨h_eq1, h_eq2, h_eq3⟩
      subst h_eq1 h_eq2
      left
      exists [], init'', tail
    | cons x xs ih =>
      simp at h_ab
      cases init with
      | nil =>
        simp at h_cd
        rcases xs with _ | ⟨y, ys⟩ <;> simp at h_ab; · grind
        subst h_cd
        simp at h_ab
        rcases h_ab with ⟨h_eq1, h_eq2, h_eq3⟩
        subst h_eq1 h_eq2 h_eq3
        right
        exists [], ys, tail'
      | cons y ys =>
        simp at h_cd
        subst h_cd
        simp at h_ab
        rcases h_ab with ⟨h_eq1, h_eq2⟩
        subst h_eq1
        rw [←h_eq2] at ih
        cases (ih (l := ys ++ c :: d :: tail) (init := ys) rfl rfl) <;> grind
