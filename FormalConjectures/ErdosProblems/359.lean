/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 359

*Reference:* [erdosproblems.com/359](https://www.erdosproblems.com/359)
-/

@[expose] public section

namespace Erdos359

open Filter Asymptotics

/-- The predicate that `A` is monotone, `A 0 = n` and for all `j`, `A (j + 1)` is the smallest natural number that
cannot be written as a sum of consecutive terms of `A 0, ..., A j` -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)

/-- Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the
least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k \to \infty$. -/
@[category research open, AMS 11]
theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry

/-- Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the
least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k ^ {1 + c} \to 0$
for any $c > 0$. -/
@[category research open, AMS 11]
theorem erdos_359.parts.ii (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c):
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  sorry

/-- If `A` is good for `n` and agrees with `f` up to index `j`, then `A (j + 1)` is the least
`v > f j` that is not a sum of consecutive terms of `f 0, ..., f j`. -/
@[category API, AMS 11]
theorem isGoodFor_step {A f : ℕ → ℕ} {n j v : ℕ} (hA : IsGoodFor A n)
    (hf : ∀ i ≤ j, A i = f i) (hv : f j < v)
    (hgood : ∀ a ≤ j, ∀ b ≤ j, a ≤ b → v ≠ ∑ i ∈ Finset.Icc a b, f i)
    (hbad : ∀ m < v, f j < m → ∃ a ≤ j, ∃ b ≤ j, a ≤ b ∧ m = ∑ i ∈ Finset.Icc a b, f i) :
    A (j + 1) = v := by
  have hS := hA.2.2 j
  have hsum : ∀ a b, b ≤ j → ∑ i ∈ Finset.Icc a b, A i = ∑ i ∈ Finset.Icc a b, f i :=
    fun a b hb => Finset.sum_congr rfl fun i hi => hf i (by simp at hi; omega)
  apply le_antisymm
  · refine hS.2 ⟨by rw [hf j le_rfl]; exact hv, fun a b hab => ?_⟩
    by_cases h : a ≤ b
    · have hb : b ≤ j := by simpa using hab (Finset.mem_Icc.2 ⟨h, le_rfl⟩)
      rw [hsum a b hb]
      exact hgood a (h.trans hb) b hb h
    · rw [Finset.Icc_eq_empty h, Finset.sum_empty]
      omega
  · by_contra hlt
    obtain ⟨a, ha, b, hb, hab, hm⟩ :=
      hbad (A (j + 1)) (by omega) (by rw [← hf j le_rfl]; exact hS.1.1)
    refine hS.1.2 a b (fun i hi => ?_) (by rw [hsum a b hb]; exact hm)
    simp at hi ⊢
    omega

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then the first few terms of $A$ are $1,2,4,5,8,10,14,15,...$. -/
@[category test, AMS 11]
theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  let f : ℕ → ℕ := fun i => [1, 2, 4, 5, 8, 10, 14, 15].getD i 0
  have key : ∀ j ≤ 7, ∀ i ≤ j, A i = f i := by
    intro j hj
    induction j with
    | zero => intro i hi; obtain rfl : i = 0 := by omega
              exact hA.1
    | succ j ih =>
      intro i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact ih (by omega) i (by omega)
      · obtain rfl : i = j + 1 := by omega
        have hj7 : j < 7 := by omega
        refine isGoodFor_step hA (ih (by omega)) ?_ ?_ ?_ <;>
          interval_cases j <;> decide
  rw [Set.image_congr (s := Set.Iic 7) fun i hi => key 7 le_rfl i hi]
  ext x
  simp only [Set.mem_image, Set.mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp [f]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
      ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩, ⟨7, by decide, rfl⟩]

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then it is conjectured that $$a_k ~ \frac{k \log k}{\log \log k}$$. -/
@[category research open, AMS 11]
theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log) := by
  sorry

end Erdos359
