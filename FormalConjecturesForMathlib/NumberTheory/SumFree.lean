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

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

variable {d : ℕ}

/-- The d-dimensional grid [N]^d = {1,...,N}^d. -/
def grid (N d : ℕ) : Set (Fin d → ℕ) :=
  {x : Fin d → ℕ | ∀ i, 1 ≤ x i ∧ x i ≤ N}

/-- A set A ⊆ [N]^d is sum-free if there are no x,y,z ∈ A such that x + y = z. -/
def IsSumFree {N : ℕ} (A : Set (Fin d → ℕ)) : Prop :=
  ∀ x y z ∈ A, x + y ≠ z

/-- The parity construction: all vectors with odd sum of coordinates. -/
def paritySet (N d : ℕ) : Set (Fin d → ℕ) :=
  {x : Fin d → ℕ | ∑ i, x i % 2 = 1}

/-- The parity construction is sum-free. -/
lemma paritySet_isSumFree (N d : ℕ) : IsSumFree (paritySet N d) := by
  intro x y z hx hyz hz hsum
  have : (∑ i, (x + y) i) % 2 = (∑ i, x i + y i) % 2 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  have : (∑ i, (x + y) i) % 2 = ((∑ i, x i) + (∑ i, y i)) % 2 := by
    rw [← Finset.sum_add_distrib]
  rw [hsum] at hz
  have : (∑ i, z i) % 2 = 1 := by rwa [hz] at hyz
  have : ((∑ i, x i) + (∑ i, y i)) % 2 = 1 := by rwa [← hsum] at hz
  have : ((∑ i, x i) % 2 + (∑ i, y i) % 2) % 2 = 1 := by
    rw [Nat.add_mod_mod, this]
  rw [hx, hyz] at this
  simp only [Nat.mod_eq_of_lt] at this
  exact absurd this (by decide)

/-- Density of a set A ⊆ [N]^d. -/
def density {N : ℕ} (A : Set (Fin d → ℕ)) : ℝ :=
  (Nat.cast (Finset.card (A.toFinset))) / (Nat.cast (N ^ d))

/-- The parity construction has density 1/2. -/
lemma paritySet_density (N d : ℕ) (hN : 0 < N) : density (paritySet N d) = 1 / 2 := by
  sorry -- This requires counting arguments about parity distribution

/-- CONJECTURE: For fixed d, the maximum density of a sum-free subset of [N]^d
    approaches 1/2 as N → ∞. -/
 conjecture sumFreeDensityOptimal :
  ∀ᶠ N in Filter.atTop,
    ∀ A : Set (Fin d → ℕ),
      IsSumFree A → A ⊆ grid N d →
        density A ≤ 1 / 2 + o(1)
