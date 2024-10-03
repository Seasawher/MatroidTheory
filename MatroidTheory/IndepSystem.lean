import Mathlib.Tactic
import Mathlib.Data.Set.Card

/-- 独立性システム

* `ℱ` の要素は独立であると呼ばれる
* `Set E \ ℱ` の要素は従属であると呼ばれる
-/
class IndepSystem {α : Type} (E : Finset α) (ℱ : Set (Set E)) where
  /-- 空集合は含まれる -/
  empty : ∅ ∈ ℱ

  /-- 独立集合の部分集合は独立集合 -/
  sub_closed {X Y : Set E} (hx : X ∈ ℱ) (hsub : Y ⊆ X) : Y ∈ ℱ

variable {α : Type}

/-- 極小な従属集合をサーキットと呼ぶ -/
def IndepSystem.circuit (E : Finset α) (ℱ : Set (Set E)) [IndepSystem E ℱ] (C : Set E) : Prop :=
  C ∉ ℱ ∧ ∀ e ∈ C, C \ {e} ∈ ℱ

-- /-- 極大な独立集合を基(base)と呼ぶ -/
-- def IndepSystem.base (E : Finset α) (ℱ : Set (Set E)) [IndepSystem E ℱ] (B : Set E) : Prop :=
--   B ∈ ℱ ∧ ∀ e ∈ E, e ∉ B → B ∪ {e} ∉ ℱ
