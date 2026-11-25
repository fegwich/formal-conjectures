/-
Copyright 2026 The Formal Conjectures Authors.

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
# Hanna's exponential series for $\binom{n+k-1}{k}^{n}$

The sequence lists the coefficients of
$$\exp\Bigl(\sum_{n \ge 1} \Bigl[\sum_{k \ge 0} \binom{n+k-1}{k}^{n} x^k\Bigr]
  \frac{x^n}{n}\Bigr).$$

*References:*
- [A181076](https://oeis.org/A181076), Paul D. Hanna, 2010.
-/

@[expose] public section

namespace OeisA181076

open PowerSeries

/-- The series $\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr] \frac{x^n}{n}$ over
$\mathbb{Q}$. Its coefficient of $x^m$ is $\sum_{n=1}^{m} f(n, m-n)/n$. -/
noncomputable def hannaLog (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, (f n (m - n) : ℚ) / n

/-- The series $\exp\Bigl(\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr]
\frac{x^n}{n}\Bigr)$ over $\mathbb{Q}$. -/
noncomputable def hannaExp (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ := subst (hannaLog f) (exp ℚ)

/-- The coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n} x^k] x^n/n\bigr)$. -/
noncomputable def a (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ n)

/-- The series `hannaLog f` has zero constant coefficient. -/
@[category API, AMS 11]
theorem X_dvd_hannaLog (f : ℕ → ℕ → ℤ) : X ∣ hannaLog f := by
  rw [X_dvd_iff]; simp [hannaLog]

/-- The coefficient of $x^m$ in `hannaExp f` is the truncated exponential series
$\sum_{d \le m} [x^m]\,L^d / d!$ with $L$ = `hannaLog f`. -/
@[category API, AMS 11]
theorem coeff_hannaExp (f : ℕ → ℕ → ℤ) (m : ℕ) :
    coeff m (hannaExp f) =
      ∑ d ∈ Finset.range (m + 1), (d.factorial : ℚ)⁻¹ * coeff m (hannaLog f ^ d) := by
  have hs : HasSubst (hannaLog f) :=
    HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 (X_dvd_hannaLog f))
  rw [hannaExp, coeff_subst' hs, finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))]
  · simp [coeff_exp, smul_eq_mul]
  · intro d hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    have : coeff m (hannaLog f ^ d) = 0 :=
      X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_hannaLog f) d) m (by omega)
    simp [this]

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rw [a, coeff_hannaExp]
  simp [hannaLog]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [a, coeff_hannaExp]
  simp [Finset.sum_range_succ, pow_succ, hannaLog]

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  rw [a, coeff_hannaExp]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, hannaLog,
    Finset.sum_Icc_succ_top]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  rw [a, coeff_hannaExp]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, hannaLog,
    Finset.sum_Icc_succ_top]
  norm_num

set_option maxHeartbeats 1000000 in
@[category test, AMS 11]
theorem a_4 : a 4 = 20 := by
  rw [a, coeff_hannaExp]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, hannaLog,
    Finset.sum_Icc_succ_top]
  norm_num

/--
"Conjecture: this sequence consists entirely of integers."
- Paul D. Hanna, Oct 02 2010.

Proved in Lean in
[the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing/blob/c1844f0c1727c369b715eabd9dd475974e8dcb5c/D5/S1/Recurrence/Algebraic/HannaA181076Integrality.lean)
on November 13, 2026. The linked formal proof is an independent proof by Wentao Li, with AI
assistance.
-/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem conjecture (m : ℕ) : ∃ z : ℤ, a m = z := by
  sorry

end OeisA181076

end
