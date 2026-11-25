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
# Busy Beaver

The Busy Beaver problem asks for the maximum number of steps that an n-state, 2-symbol Turing
machine can take before halting, when started on an empty tape.

*References:*

- [The Busy Beaver Challenge](https://wiki.bbchallenge.org/wiki/Main_Page)
-/

@[expose] public section

universe u v

open Turing BusyBeaver

namespace BusyBeaver

structure Candidate (n : ℕ) where
  Γ : Type
  Λ : Type
  Γ_fintype : Fintype Γ
  Γ_card : Fintype.card Γ = 2
  Γ_inhabited : Inhabited Γ
  Λ_fintype : Fintype Λ
  Λ_card : Fintype.card Λ = n
  Λ_inhabited : Inhabited Λ
  M : Machine Γ Λ
  M_isHalting : M.IsHalting

instance {n : ℕ} {M : Candidate n} : Fintype M.Γ := M.Γ_fintype
instance {n : ℕ} {M : Candidate n} : Fintype M.Λ := M.Λ_fintype
instance {n : ℕ} {M : Candidate n} : Inhabited M.Γ := M.Γ_inhabited
instance {n : ℕ} {M : Candidate n} : Inhabited M.Λ := M.Λ_inhabited

/--
`BB(n)` is the `n`-th Busy Beaver number.
*This is the maximum shifts function*, not the "number of ones function"
-/
noncomputable def BB (n : ℕ) : ℕ :=
  sSup { N | ∃ C : Candidate n, C.M.haltingNumber = N}

/--
To compute `BB n`, we need only consider machines with states and symbols indexed in `Fin`.
-/
@[category API, AMS 3]
theorem sanity_check (n : ℕ) [NeZero n] :
    BB n = sSup {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting),
      M.haltingNumber = N} := by
  sorry

/-- A halting machine with a single state halts after at most one step. -/
@[category API, AMS 3]
theorem haltingNumber_le_one_of_subsingleton {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    [Subsingleton Λ] (M : Machine Γ Λ) [hM : M.IsHalting] : M.haltingNumber ≤ 1 := by
  have h0 : (Tape.mk₁ ([] : List Γ)).head = default := rfl
  have hl : (Tape.mk₁ ([] : List Γ)).left = default := rfl
  have hr : (Tape.mk₁ ([] : List Γ)).right = default := rfl
  have h1 : (default : ListBlank Γ).head = default := rfl
  have h2 : (default : ListBlank Γ).tail = default := rfl
  rcases h : M default default with _ | ⟨_ | q, ⟨a, d⟩⟩
  · refine sInf_le ⟨1, ?_, rfl⟩
    simp [Machine.HaltsAfter, Machine.step, Machine.init, h0, h]
  · refine sInf_le ⟨1, ?_, rfl⟩
    simp [Machine.HaltsAfter, Machine.step, Machine.init, h0, h]
  · exfalso
    let P : Cfg Γ Λ → Prop := fun c => c.q = some default ∧ c.tape.head = default ∧
      (match d with | .left => c.tape.left | .right => c.tape.right) = default
    have hstep : ∀ c, P c → ∃ c', M.step c = some c' ∧ P c' := by
      rintro ⟨_, ⟨hd, L, R⟩⟩ ⟨hq, hh, hs⟩
      simp only at hq hh hs
      subst hq
      refine ⟨_, by simp [Machine.step, hh, h]; rfl, ?_⟩
      cases d <;> simp_all [P, Subsingleton.elim q default, Tape.move]
    have key : ∀ n, ∃ c, M.multiStep (Machine.init []) n = some c ∧ P c := by
      intro n
      induction n with
      | zero => exact ⟨_, rfl, rfl, h0, by cases d <;> simp [Machine.init, hl, hr]⟩
      | succ n ih =>
        obtain ⟨c, hc, hP⟩ := ih
        obtain ⟨c', h1, h2⟩ := hstep c hP
        exact ⟨c', by simp [Machine.multiStep_succ, hc, h1], h2⟩
    refine (Machine.not_isHalting_iff_forall_isSome_multiStep M).2 (fun n => ?_) hM
    obtain ⟨c, hc, -⟩ := key (n + 1)
    rw [hc]
    rfl

/-- The value of the Busy Beaver function for 1 state is 1. -/
@[category test, AMS 3]
theorem BB_1 : BB 1 = 1 := by
  let M₁ : Machine Bool Unit := fun _ _ => some (none, ⟨default, Dir.right⟩)
  have hM₁ : M₁.multiStep (Machine.init []) 2 = none := rfl
  have hH : M₁.IsHalting := (Machine.isHalting_iff_exists_haltsAt M₁).2 ⟨1, hM₁⟩
  let C : Candidate 1 := ⟨Bool, Unit, inferInstance, rfl, inferInstance, inferInstance, rfl,
    inferInstance, M₁, hH⟩
  have hC : C.M.haltingNumber = (1 : ℕ) := Machine.haltingNumber_def _ 1 ⟨_, rfl⟩ hM₁
  have hle : ∀ N : ℕ, N ∈ {N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = N} → N ≤ 1 := by
    rintro N ⟨C, hC⟩
    have : Subsingleton C.Λ := Fintype.card_le_one_iff_subsingleton.1 C.Λ_card.le
    have := C.M_isHalting
    have := haltingNumber_le_one_of_subsingleton C.M
    rw [hC] at this
    exact_mod_cast this
  exact le_antisymm (csSup_le ⟨1, C, hC⟩ hle) (le_csSup ⟨1, hle⟩ ⟨C, hC⟩)

/-- The value of the Busy Beaver function for 2 states is 6. -/
@[category textbook, AMS 3]
theorem BB_2 : BB 2 = 6 := by
  sorry

/-- The value of the Busy Beaver function for 3 states is 21. -/
@[category textbook, AMS 3]
theorem BB_3 : BB 3 = 21 := by
  sorry

/-- The value of the Busy Beaver function for 4 states is 107. -/
@[category textbook, AMS 3]
theorem BB_4 : BB 4 = 107 := by
  sorry

/-- The value of the Busy Beaver function for 5 states is 47176870. -/
@[category research solved, AMS 3]
theorem BB_5 : BB 5 = 47176870 := by
  sorry

def BB_6.answer : ℕ := sorry

/--
Determine the value of the Busy Beaver function at n = 6.
-/
@[category research open, question value, AMS 3]
theorem BB_6 : BB 6 = BB_6.answer := by
  sorry

end BusyBeaver
