import Mathlib.Tactic
import Mathlib.Data.Set.Card

/-- マトロイド -/
class Matroid {α : Type} (E : Finset α) (I : Set (Set E)) where
  /-- 空集合は独立集合 -/
  empty : ∅ ∈ I

  /-- 独立集合の部分集合は独立集合 -/
  sub_closed {X Y : Set E} : X ∈ I → Y ⊆ X → Y ∈ I

  /-- 増加公理 -/
  augment {X Y : Set E} (hx : X ∈ I) (hy : Y ∈ I) :
    X.ncard > Y.ncard → ∃ e ∈ X \ Y, ({e} ∪ Y) ∈ I

variable {α : Type} {E : Finset α} (I : Set (Set E))

/-- マトロイドの基(base)。極大な独立集合。
`Matroid.Base I B` で、`B` がマトロイド `I` の基であることを意味する。-/
def Matroid.Base (I : Set (Set E)) [Matroid E I] (B : Set E) : Prop :=
  B ∈ I ∧ ∀ e ∈ Bᶜ, ({e} ∪ B) ∉ I

/-- `B` がマトロイド `M = (E, I)` の基なら、その部分集合はすべて独立 -/
theorem Matroid.base_up_closed (I : Set (Set E)) [Matroid E I] {B : Set E} (hB : Matroid.Base I B) {X : Set E} :
    X ⊆ B → X ∈ I := by
  -- B は I の基なので、`B ∈ I`
  have : B ∈ I := by exact hB.left

  -- `X ⊆ B` なので、独立集合の部分集合は独立集合だから `X ∈ I`
  exact Matroid.sub_closed this

/-- マトロイドの基の濃度は等しい -/
theorem Matroid.base_equicardinality (I : Set (Set E)) [Matroid E I] {B B' : Set E}
    (hB : Matroid.Base I B) (hB' : Matroid.Base I B') : B.ncard = B'.ncard := by
  -- 背理法で示す。`|B| ≠ |B'|` と仮定する
  by_contra! hne

  -- 一般性を失うことなく、`|B| < |B'|` と仮定してよい。
  wlog hlt : B.ncard < B'.ncard with H

  -- なぜなら、もし `|B| < |B'|` のとき成立していたなら、
  -- 他の場合も `B` と `B'` を入れ替えることで示せるからだ。
  case inr =>
    replace hlt : B.ncard > B'.ncard := by omega
    apply @H α E I _ B' B <;> try assumption
    omega

  -- そこで `|B| < |B'|` と仮定して示す。
  guard_hyp hlt : B.ncard < B'.ncard
  clear hne

  -- `B, B'` は `I` の基なので、`B, B' ∈ I`
  have indb : B ∈ I := by exact hB.left
  replace hB' : B' ∈ I := by exact hB'.left

  -- 増加公理より、ある `e ∈ B' \ B` が存在して `B ∪ {e} ∈ I` を満たす
  replace hB' : ∃ e ∈ B' \ B, ({e} ∪ B) ∈ I := by
    apply Matroid.augment hB' indb
    omega

  -- これは `B` が `I` の基であることに矛盾する。よって示せた。
  have := hB.right
  aesop

/-- 任意の独立集合 `X ∈ I` に対して、`X ⊆ B` となる基が存在する -/
theorem Matroid.base_of_ind (I : Set (Set E)) [Matroid E I] {X : Set E} (hX : X ∈ I) :
    ∃ B, Matroid.Base I B ∧ X ⊆ B := by
  -- `|E \ X|` に関する帰納法を使う
  induction' h : (Xᶜ : Set E).ncard generalizing X

  -- `|E \ X|` = 0 のとき。
  case zero =>
    -- `Set.ncard` の定義から、無限集合または空集合になる
    replace h : X = Set.univ ∨ Xᶜ.Infinite := by
      simp_all [Set.ncard]

    -- E は無限集合ではないので空集合
    replace h : Xᶜ = ∅ := by
      rcases h with h | h
      · simp_all
      · exfalso
        simp_all [Set.toFinite Xᶜ]

    -- このとき `X = E`
    replace h : X = Set.univ := by
      simp_all

    use X

    -- `X ⊆ X` は明らかなので `X` が基であることを示せばよい。
    refine ⟨?_, by simp⟩

    dsimp [Base]
    refine ⟨by assumption, ?_⟩
    intro e he
    exfalso
    simp [h] at he

  -- `|E \ X| = n` まで成り立つと仮定する
  case succ n ih =>
    sorry
