import FormalConjectures.ErdosProblems.«143»

/-!
# Disproof of Erdős Problem 143 (part ii)

We construct a countably infinite well-separated set $A \subset (1, \infty)$
(satisfying $|k x - y| \ge 1$ for all distinct $x, y \in A$ and integers $k \ge 1$)
for which $\sum_{x \in A} \frac{1}{x \log x}$ diverges, following Mattia Apicella's
private-prime rational-block construction (with elementary primitive level selection).
-/

-- Problem: Erdős Problem 143 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/143.lean:64 (declaration Erdos143.erdos_143.parts.ii)
-- Credit: @Goidelg (the owner of the agent is credited as the solver)
-- Refute EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos143Disproof

open Filter Finset BigOperators

/- ### Part 1: Elementary weight and prime-sum estimates -/

private noncomputable def w (x : ℝ) : ℝ :=
  1 / (x * Real.log x)

private noncomputable def W (S : Finset ℝ) : ℝ :=
  ∑ x ∈ S, w x

private noncomputable def Wnat (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, w (n : ℝ)

private lemma w_pos {x : ℝ} (hx : 1 < x) : 0 < w x := by
  unfold w
  have h1 : 0 < x := by linarith
  have h2 : 0 < Real.log x := Real.log_pos hx
  positivity

private lemma w_anti {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) : w y ≤ w x := by
  unfold w
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hprod : x * Real.log x ≤ y * Real.log y := by
    calc
      x * Real.log x ≤ y * Real.log x := mul_le_mul_of_nonneg_right hxy (le_of_lt hlogx)
      _ ≤ y * Real.log y := mul_le_mul_of_nonneg_left hlogy (by linarith)
  exact one_div_le_one_div_of_le (mul_pos hx0 hlogx) hprod

private lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

private lemma exp_one_lt_three : Real.exp 1 < 3 := by
  have h := Real.exp_one_lt_d9
  linarith

private lemma log_log_step_le {m M : ℕ} (hm : 2 ≤ m) (hM : 1 ≤ M) :
    Real.log (Real.log ((M * (m + 1) : ℕ) : ℝ)) - Real.log (Real.log ((M * m : ℕ) : ℝ)) ≤
      1 / ((m : ℝ) * Real.log ((M * m : ℕ) : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hM_ge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMm_gt1 : (1 : ℝ) < ((M * m : ℕ) : ℝ) := by
    have : 2 ≤ M * m := by nlinarith
    exact_mod_cast (by omega : 1 < M * m)
  have hMm1_gt1 : (1 : ℝ) < ((M * (m + 1) : ℕ) : ℝ) := by
    have : 2 ≤ M * (m + 1) := by nlinarith
    exact_mod_cast (by omega : 1 < M * (m + 1))
  set u := Real.log ((M * m : ℕ) : ℝ)
  set v := Real.log ((M * (m + 1) : ℕ) : ℝ)
  have hu : 0 < u := Real.log_pos hMm_gt1
  have hv : 0 < v := Real.log_pos hMm1_gt1
  have h1 : Real.log v - Real.log u ≤ (v - u) / u := by
    rw [← Real.log_div (ne_of_gt hv) (ne_of_gt hu)]
    have hlog := Real.log_le_sub_one_of_pos (div_pos hv hu)
    have heq : v / u - 1 = (v - u) / u := by field_simp
    linarith
  have hvu : v - u ≤ 1 / (m : ℝ) := by
    have hpos1 : (0 : ℝ) < ((M * (m + 1) : ℕ) : ℝ) := by linarith
    have hpos2 : (0 : ℝ) < ((M * m : ℕ) : ℝ) := by linarith
    have hdiv : ((M * (m + 1) : ℕ) : ℝ) / ((M * m : ℕ) : ℝ) = ((m : ℝ) + 1) / (m : ℝ) := by
      push_cast
      have hM0 : (M : ℝ) ≠ 0 := by linarith
      field_simp
    dsimp only [u, v]
    rw [← Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2), hdiv]
    have hlog := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < (m : ℝ) + 1) hm_pos)
    have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by field_simp; ring
    linarith
  calc
    Real.log v - Real.log u ≤ (v - u) / u := h1
    _ ≤ (1 / (m : ℝ)) / u := div_le_div_of_nonneg_right hvu (le_of_lt hu)
    _ = 1 / ((m : ℝ) * u) := by field_simp

private lemma sum_inv_mul_log_ge {a b M : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hM : 1 ≤ M) :
    Real.log (Real.log ((M * b : ℕ) : ℝ)) - Real.log (Real.log ((M * a : ℕ) : ℝ)) ≤
      ∑ m ∈ Finset.Ico a b, 1 / ((m : ℝ) * Real.log ((M * m : ℕ) : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp
  | succ k ih =>
    have hsub : Finset.Ico a (a + (k + 1)) = insert (a + k) (Finset.Ico a (a + k)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotmem : a + k ∉ Finset.Ico a (a + k) := by simp
    rw [hsub, Finset.sum_insert hnotmem]
    have hih := ih (Nat.le_add_right a k)
    have hstep := log_log_step_le (m := a + k) (M := M) (by omega) hM
    have heq : a + (k + 1) = (a + k) + 1 := by omega
    rw [heq]
    linarith

private lemma inv_mul_log_le_log_log_step {n : ℕ} (hn : 3 ≤ n) :
    w (n : ℝ) ≤ Real.log (Real.log (n : ℝ)) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
  have hn1_gt1 : (1 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - 1)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  set u := Real.log ((n - 1 : ℕ) : ℝ)
  set v := Real.log (n : ℝ)
  have hu : 0 < u := Real.log_pos hn1_gt1
  have hv : 0 < v := Real.log_pos hn_gt1
  have h1 : (v - u) / v ≤ Real.log v - Real.log u := by
    rw [← Real.log_div (ne_of_gt hv) (ne_of_gt hu)]
    have hlog := one_sub_inv_le_log (div_pos hv hu)
    have heq : 1 - (v / u)⁻¹ = (v - u) / v := by field_simp
    linarith
  have hvu : 1 / (n : ℝ) ≤ v - u := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
    dsimp only [u, v]
    rw [← Real.log_div (ne_of_gt hn_pos) (ne_of_gt hn1_pos)]
    have hlog := one_sub_inv_le_log (div_pos hn_pos hn1_pos)
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have heq : 1 - ((n : ℝ) / ((n - 1 : ℕ) : ℝ))⁻¹ = 1 / (n : ℝ) := by
      rw [hcast]
      field_simp
      ring
    linarith
  calc
    w (n : ℝ) = (1 / (n : ℝ)) / v := by unfold w; dsimp only [v]; field_simp
    _ ≤ (v - u) / v := div_le_div_of_nonneg_right hvu (le_of_lt hv)
    _ ≤ Real.log v - Real.log u := h1

private lemma sum_w_Icc_le (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ Finset.Icc 2 X, w (n : ℝ) ≤ Real.log (Real.log (X : ℝ)) + 2 := by
  have htele : ∀ k : ℕ,
      ∑ n ∈ Finset.Icc 2 (2 + k), w (n : ℝ) ≤
        w 2 + (Real.log (Real.log ((2 + k : ℕ) : ℝ)) - Real.log (Real.log 2)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsub : Finset.Icc 2 (2 + (k + 1)) = insert (2 + (k + 1)) (Finset.Icc 2 (2 + k)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : 2 + (k + 1) ∉ Finset.Icc 2 (2 + k) := by simp
      rw [hsub, Finset.sum_insert hnotmem]
      have hstep := inv_mul_log_le_log_log_step (n := 2 + (k + 1)) (by omega)
      have heq : 2 + (k + 1) - 1 = 2 + k := by omega
      rw [heq] at hstep
      linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hX
  have h1 := htele k
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two
  have hw2 : w 2 < 1 := by
    unfold w
    rw [div_lt_one (by linarith : (0 : ℝ) < 2 * Real.log 2)]
    linarith
  have hll2 : -1 < Real.log (Real.log 2) := by
    have h := one_sub_inv_le_log (by linarith : (0 : ℝ) < Real.log 2)
    have hinv : (Real.log 2)⁻¹ < 2 := by
      rw [inv_lt_comm₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  linarith

private lemma rpow_neg_step_le {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    (n : ℝ) ^ (-(1 + s)) ≤
      (((n - 1 : ℕ) : ℝ) ^ (-s) - (n : ℝ) ^ (-s)) / s := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hlog_ge : 1 / (n : ℝ) ≤ Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    have h := one_sub_inv_le_log (div_pos hn_pos hn1_pos)
    have heq : 1 - ((n : ℝ) / ((n - 1 : ℕ) : ℝ))⁻¹ = 1 / (n : ℝ) := by
      rw [hcast]
      field_simp
      ring
    linarith
  have hlog_le : Real.log (1 + s / (n : ℝ)) ≤ s / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + s / (n : ℝ))
    linarith
  have hcomb : Real.log (1 + s / (n : ℝ)) ≤ s * Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_ge (le_of_lt hs)
    have heq : s * (1 / (n : ℝ)) = s / (n : ℝ) := by ring
    linarith
  have hexp : 1 + s / (n : ℝ) ≤ ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ^ s := by
    rw [Real.rpow_def_of_pos (div_pos hn_pos hn1_pos), mul_comm]
    calc
      1 + s / (n : ℝ) = Real.exp (Real.log (1 + s / (n : ℝ))) :=
        (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (s * Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) :=
        Real.exp_le_exp.mpr hcomb
  have hpow : (n : ℝ) ^ (-s) * ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ^ s = ((n - 1 : ℕ) : ℝ) ^ (-s) := by
    rw [Real.div_rpow (le_of_lt hn_pos) (le_of_lt hn1_pos)]
    rw [← mul_div_assoc, ← Real.rpow_add hn_pos, neg_add_cancel, Real.rpow_zero, one_div]
    rw [Real.rpow_neg (le_of_lt hn1_pos)]
  have hmul : (n : ℝ) ^ (-s) * (1 + s / (n : ℝ)) ≤ ((n - 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (le_of_lt hn_pos) (-s))
  have hstep : s * (n : ℝ) ^ (-(1 + s)) ≤ ((n - 1 : ℕ) : ℝ) ^ (-s) - (n : ℝ) ^ (-s) := by
    have hsplit : (n : ℝ) ^ (-(1 + s)) = (n : ℝ) ^ (-s) / (n : ℝ) := by
      rw [show -(1 + s) = -s + (-1) by ring, Real.rpow_add hn_pos, Real.rpow_neg_one, div_eq_mul_inv]
    rw [hsplit]
    have heq : (n : ℝ) ^ (-s) * (1 + s / (n : ℝ)) = (n : ℝ) ^ (-s) + s * ((n : ℝ) ^ (-s) / (n : ℝ)) := by
      ring
    linarith
  exact (le_div_iff₀ hs).mpr (by linarith)

private lemma sum_rpow_neg_le (Y : ℕ) {s : ℝ} (hs : 0 < s) :
    ∑ n ∈ Finset.Icc 1 Y, (n : ℝ) ^ (-(1 + s)) ≤ 1 + 1 / s := by
  by_cases hY : Y = 0
  · subst hY
    simp only [Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.sum_empty]
    positivity
  have htele : ∀ k : ℕ,
      ∑ n ∈ Finset.Icc 1 (1 + k), (n : ℝ) ^ (-(1 + s)) ≤
        1 + (1 - ((1 + k : ℕ) : ℝ) ^ (-s)) / s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsub : Finset.Icc 1 (1 + (k + 1)) = insert (1 + (k + 1)) (Finset.Icc 1 (1 + k)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : 1 + (k + 1) ∉ Finset.Icc 1 (1 + k) := by simp
      rw [hsub, Finset.sum_insert hnotmem]
      have hstep := rpow_neg_step_le (n := 1 + (k + 1)) (by omega) hs
      have heq : 1 + (k + 1) - 1 = 1 + k := by omega
      rw [heq] at hstep
      have hcomb : (1 - ((1 + k : ℕ) : ℝ) ^ (-s)) / s +
          (((1 + k : ℕ) : ℝ) ^ (-s) - ((1 + (k + 1) : ℕ) : ℝ) ^ (-s)) / s =
          (1 - ((1 + (k + 1) : ℕ) : ℝ) ^ (-s)) / s := by
        field_simp
        ring
      linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hY)
  have h1 := htele k
  have hnonneg : 0 ≤ ((1 + k : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) (-s)
  have h2 : (1 - ((1 + k : ℕ) : ℝ) ^ (-s)) / s ≤ 1 / s :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hs)
  linarith

private lemma finite_euler_prod_step {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (K : ℕ) {s : ℝ} :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, 1 ≤ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ∈ S) ∧
      ∏ p ∈ S, (∑ k ∈ Finset.range (K + 1), ((p : ℝ) ^ (-(1 + s))) ^ k) =
        ∑ n ∈ T, (n : ℝ) ^ (-(1 + s)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨{1}, ?_, by simp⟩
    intro n hn
    rw [Finset.mem_singleton] at hn
    subst hn
    exact ⟨le_rfl, fun q hq hd => absurd hd hq.not_dvd_one⟩
  | @insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨T, hT_prop, hT_eq⟩ := ih hS'
    let f : ℕ × ℕ → ℕ := fun km => p ^ km.1 * km.2
    let dom := Finset.range (K + 1) ×ˢ T
    have hinj : Set.InjOn f (dom : Set (ℕ × ℕ)) := by
      rintro ⟨k₁, m₁⟩ h₁ ⟨k₂, m₂⟩ h₂ hfeq
      simp only [dom, Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
      have hm1 : 1 ≤ m₁ := (hT_prop m₁ h₁.2).1
      have hm2 : 1 ≤ m₂ := (hT_prop m₂ h₂.2).1
      have hpnd1 : ¬ p ∣ m₁ := fun hd => hpS ((hT_prop m₁ h₁.2).2 p hp hd)
      have hpnd2 : ¬ p ∣ m₂ := fun hd => hpS ((hT_prop m₂ h₂.2).2 p hp hd)
      have hfac1 : (p ^ k₁ * m₁).factorization p = k₁ := by
        rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
          hp.factorization_pow, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd hpnd1, add_zero]
      have hfac2 : (p ^ k₂ * m₂).factorization p = k₂ := by
        rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
          hp.factorization_pow, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd hpnd2, add_zero]
      have hk : k₁ = k₂ := by
        have hfeq' : p ^ k₁ * m₁ = p ^ k₂ * m₂ := hfeq
        rw [← hfac1, hfeq', hfac2]
      subst hk
      have hm : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k₁) hfeq
      exact Prod.ext rfl hm
    refine ⟨dom.image f, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_image.mp hn with ⟨⟨k, m⟩, hkm, rfl⟩
      rcases Finset.mem_product.mp hkm with ⟨_, hmT⟩
      have hm1 : 1 ≤ m := (hT_prop m hmT).1
      refine ⟨Nat.mul_pos (pow_pos hp.pos k) (by omega), fun q hq hd => ?_⟩
      rcases hq.dvd_mul.mp hd with hdp | hdm
      · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdp)
        rw [hqp]
        exact Finset.mem_insert_self p S
      · exact Finset.mem_insert_of_mem ((hT_prop m hmT).2 q hq hdm)
    · rw [Finset.prod_insert hpS, hT_eq, Finset.sum_image hinj, Finset.sum_mul_sum]
      rw [← Finset.sum_product']
      apply Finset.sum_congr rfl
      rintro ⟨k, m⟩ hkm
      rcases Finset.mem_product.mp hkm with ⟨_, hmT⟩
      have hp_pos : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hm_pos : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      dsimp only [f]
      rw [Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (pow_nonneg hp_pos k) hm_pos]
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp_pos, mul_comm (k : ℝ),
        Real.rpow_mul hp_pos, Real.rpow_natCast]

private lemma prod_one_sub_prime_inv_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {s : ℝ} (hs : 0 < s) :
    ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1 + s)))⁻¹ ≤ 1 + 1 / s := by
  have hle_K : ∀ K : ℕ,
      ∏ p ∈ S, (∑ k ∈ Finset.range (K + 1), ((p : ℝ) ^ (-(1 + s))) ^ k) ≤ 1 + 1 / s := by
    intro K
    obtain ⟨T, hT_prop, hT_eq⟩ := finite_euler_prod_step hS K (s := s)
    rw [hT_eq]
    have hsub : T ⊆ Finset.Icc 1 (T.sup id) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(hT_prop n hn).1, Finset.le_sup (f := id) hn⟩
    calc
      ∑ n ∈ T, (n : ℝ) ^ (-(1 + s))
          ≤ ∑ n ∈ Finset.Icc 1 (T.sup id), (n : ℝ) ^ (-(1 + s)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ 1 + 1 / s := sum_rpow_neg_le (T.sup id) hs
  have htend : Tendsto
      (fun K : ℕ => ∏ p ∈ S, (∑ k ∈ Finset.range (K + 1), ((p : ℝ) ^ (-(1 + s))) ^ k))
      atTop (nhds (∏ p ∈ S, (1 - (p : ℝ) ^ (-(1 + s)))⁻¹)) := by
    apply tendsto_finsetProd
    intro p hp
    have hpr : p.Prime := hS p hp
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.one_lt
    have hr_nonneg : 0 ≤ (p : ℝ) ^ (-(1 + s)) := Real.rpow_nonneg (by linarith) _
    have hr_lt1 : (p : ℝ) ^ (-(1 + s)) < 1 := by
      rw [Real.rpow_neg (by linarith)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp_gt1 (by linarith))
    have hgeom := (hasSum_geometric_of_lt_one hr_nonneg hr_lt1).tendsto_sum_nat
    exact hgeom.comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto htend (Eventually.of_forall hle_K)

private lemma sum_prime_inv_le (X : ℕ) (hX : 16 ≤ X) :
    ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      3 * Real.log (Real.log (X : ℝ)) + 3 := by
  set S := (Finset.Icc 2 X).filter Nat.Prime
  have hX_gt1 : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hlogX_ge2 : (2 : ℝ) ≤ Real.log (X : ℝ) := by
    have h2 : (2 : ℝ) ^ 4 ≤ (X : ℝ) := by
      have : 16 ≤ X := hX
      exact_mod_cast this
    have hlog2 := half_lt_log_two
    have h1 : Real.log ((2 : ℝ) ^ 4) ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  set s : ℝ := 1 / Real.log (X : ℝ)
  have hs : 0 < s := by positivity
  have hstep1 : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ Real.exp 1 * (p : ℝ) ^ (-(1 + s)) := by
    intro p hp
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    have hpX : p ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
    have hlogp_le : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hp_pos (by exact_mod_cast hpX)
    have hps_le : (p : ℝ) ^ s ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hp_pos]
      apply Real.exp_le_exp.mpr
      dsimp only [s]
      rw [mul_one_div, div_le_one hlogX_pos]
      exact hlogp_le
    have hsplit : (p : ℝ) ^ s * (p : ℝ) ^ (-(1 + s)) = 1 / (p : ℝ) := by
      rw [← Real.rpow_add hp_pos, show s + -(1 + s) = -1 by ring, Real.rpow_neg_one, one_div]
    calc
      (1 : ℝ) / (p : ℝ) = (p : ℝ) ^ s * (p : ℝ) ^ (-(1 + s)) := hsplit.symm
      _ ≤ Real.exp 1 * (p : ℝ) ^ (-(1 + s)) :=
        mul_le_mul_of_nonneg_right hps_le (Real.rpow_nonneg (le_of_lt hp_pos) _)
  have hstep2 : ∑ p ∈ S, (p : ℝ) ^ (-(1 + s)) ≤ Real.log (1 + Real.log (X : ℝ)) := by
    have hterm : ∀ p ∈ S, (p : ℝ) ^ (-(1 + s)) ≤ Real.log ((1 - (p : ℝ) ^ (-(1 + s)))⁻¹) := by
      intro p hp
      have hpr : p.Prime := (Finset.mem_filter.mp hp).2
      have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.one_lt
      have hr_lt1 : (p : ℝ) ^ (-(1 + s)) < 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp_gt1 (by linarith))
      have h1 : Real.log (1 - (p : ℝ) ^ (-(1 + s))) ≤ -(p : ℝ) ^ (-(1 + s)) := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - (p : ℝ) ^ (-(1 + s)))
        linarith
      rw [Real.log_inv]
      linarith
    have hprod_pos : ∀ p ∈ S, (1 - (p : ℝ) ^ (-(1 + s)))⁻¹ ≠ 0 := by
      intro p hp
      have hpr : p.Prime := (Finset.mem_filter.mp hp).2
      have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.one_lt
      have hr_lt1 : (p : ℝ) ^ (-(1 + s)) < 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp_gt1 (by linarith))
      exact inv_ne_zero (by linarith)
    have hprod_pos' : 0 < ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1 + s)))⁻¹ := by
      apply Finset.prod_pos
      intro p hp
      have hpr : p.Prime := (Finset.mem_filter.mp hp).2
      have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.one_lt
      have hr_lt1 : (p : ℝ) ^ (-(1 + s)) < 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp_gt1 (by linarith))
      exact inv_pos.mpr (by linarith)
    calc
      ∑ p ∈ S, (p : ℝ) ^ (-(1 + s))
          ≤ ∑ p ∈ S, Real.log ((1 - (p : ℝ) ^ (-(1 + s)))⁻¹) := Finset.sum_le_sum hterm
      _ = Real.log (∏ p ∈ S, (1 - (p : ℝ) ^ (-(1 + s)))⁻¹) := (Real.log_prod hprod_pos).symm
      _ ≤ Real.log (1 + 1 / s) :=
        Real.log_le_log hprod_pos' (prod_one_sub_prime_inv_le (fun p hp => (Finset.mem_filter.mp hp).2) hs)
      _ = Real.log (1 + Real.log (X : ℝ)) := by
        dsimp only [s]
        rw [one_div_one_div]
  have hlog_bound : Real.log (1 + Real.log (X : ℝ)) ≤ Real.log (Real.log (X : ℝ)) + 1 := by
    have hle : 1 + Real.log (X : ℝ) ≤ 2 * Real.log (X : ℝ) := by linarith
    calc
      Real.log (1 + Real.log (X : ℝ)) ≤ Real.log (2 * Real.log (X : ℝ)) :=
        Real.log_le_log (by linarith) hle
      _ = Real.log 2 + Real.log (Real.log (X : ℝ)) :=
        Real.log_mul (by norm_num) (ne_of_gt hlogX_pos)
      _ ≤ 1 + Real.log (Real.log (X : ℝ)) := by
        have : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        linarith
      _ = Real.log (Real.log (X : ℝ)) + 1 := by ring
  have hll_nonneg : 0 ≤ Real.log (Real.log (X : ℝ)) + 1 := by
    have : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  calc
    ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ S, Real.exp 1 * (p : ℝ) ^ (-(1 + s)) := Finset.sum_le_sum hstep1
    _ = Real.exp 1 * ∑ p ∈ S, (p : ℝ) ^ (-(1 + s)) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp 1 * Real.log (1 + Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep2 (le_of_lt (Real.exp_pos 1))
    _ ≤ Real.exp 1 * (Real.log (Real.log (X : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_left hlog_bound (le_of_lt (Real.exp_pos 1))
    _ ≤ 3 * (Real.log (Real.log (X : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_right (le_of_lt exp_one_lt_three) hll_nonneg
    _ = 3 * Real.log (Real.log (X : ℝ)) + 3 := by ring

private lemma sum_prime_pow_ge2_le (X : ℕ) :
    ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
      ∑ j ∈ Finset.Icc 2 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) ≤ 1 := by
  have hinner : ∀ p : ℕ, 2 ≤ p →
      ∑ j ∈ Finset.Icc 2 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) ≤
        1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ) := by
    intro p hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hp1_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    have htele : ∀ k : ℕ,
        ((p : ℝ) - 1) * (∑ j ∈ Finset.Icc 2 (1 + k), (1 : ℝ) / ((p ^ j : ℕ) : ℝ)) =
          1 / (p : ℝ) - 1 / ((p ^ (1 + k) : ℕ) : ℝ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hsub : Finset.Icc 2 (1 + (k + 1)) = insert (1 + (k + 1)) (Finset.Icc 2 (1 + k)) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnotmem : 1 + (k + 1) ∉ Finset.Icc 2 (1 + k) := by simp
        rw [hsub, Finset.sum_insert hnotmem, mul_add, ih]
        have hpow : ((p ^ (1 + (k + 1)) : ℕ) : ℝ) = (p : ℝ) * ((p ^ (1 + k) : ℕ) : ℝ) := by
          rw [show 1 + (k + 1) = (1 + k) + 1 by omega, pow_succ]
          push_cast
          ring
        have hne : ((p ^ (1 + k) : ℕ) : ℝ) ≠ 0 := by positivity
        rw [hpow]
        field_simp
        ring
    by_cases hX2 : X < 2
    · simp only [Finset.Icc_eq_empty (by omega : ¬ 2 ≤ X), Finset.sum_empty]
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hp1_pos (by linarith)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ X)
      have h1 := htele k
      have hnonneg : 0 ≤ 1 / ((p ^ (1 + k) : ℕ) : ℝ) := by positivity
      have h2 : ((p : ℝ) - 1) * (∑ j ∈ Finset.Icc 2 (1 + k), (1 : ℝ) / ((p ^ j : ℕ) : ℝ)) ≤
          1 / (p : ℝ) := by linarith
      have h3 : ∑ j ∈ Finset.Icc 2 (1 + k), (1 : ℝ) / ((p ^ j : ℕ) : ℝ) ≤
          (1 / (p : ℝ)) / ((p : ℝ) - 1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
      have heq : (1 / (p : ℝ)) / ((p : ℝ) - 1) = 1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ) := by
        rw [hcast]
        have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
      linarith
  have houter : ∑ m ∈ Finset.Icc 2 X, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) ≤ 1 := by
    by_cases hX2 : X < 2
    · simp [Finset.Icc_eq_empty (by omega : ¬ 2 ≤ X)]
    · have htele : ∀ k : ℕ,
          ∑ m ∈ Finset.Icc 2 (1 + k), (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
            1 - 1 / ((1 + k : ℕ) : ℝ) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hsub : Finset.Icc 2 (1 + (k + 1)) = insert (1 + (k + 1)) (Finset.Icc 2 (1 + k)) := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnotmem : 1 + (k + 1) ∉ Finset.Icc 2 (1 + k) := by simp
          rw [hsub, Finset.sum_insert hnotmem, ih]
          have heq : 1 + (k + 1) - 1 = 1 + k := by omega
          rw [heq]
          ring
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ X)
      rw [htele k]
      have : 0 ≤ 1 / ((1 + k : ℕ) : ℝ) := by positivity
      linarith
  calc
    ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        ∑ j ∈ Finset.Icc 2 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ)
        ≤ ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) :=
          Finset.sum_le_sum (fun p hp => hinner p (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
    _ ≤ ∑ m ∈ Finset.Icc 2 X, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m hm _
          have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
          rw [sub_nonneg]
          apply one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < m - 1))
          exact_mod_cast (by omega : m - 1 ≤ m)
    _ ≤ 1 := houter

private def omegaBig (n : ℕ) : ℕ :=
  n.factorization.sum fun _ k => k

private lemma omegaBig_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ omegaBig n := by
  have hne1 : n ≠ 1 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hpos : 1 ≤ n.factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization (by omega)]
    simpa using hpdvd
  have hmem : p ∈ n.factorization.support :=
    Finsupp.mem_support_iff.mpr (by omega)
  have hle : n.factorization p ≤ omegaBig n := by
    unfold omegaBig
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  omega

private lemma omegaBig_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaBig (a * b) = omegaBig a + omegaBig b := by
  unfold omegaBig
  rw [Nat.factorization_mul ha hb]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma omegaBig_eq_prime_pow_count {n X : ℕ} (hn2 : 2 ≤ n) (hnX : n ≤ X) :
    (omegaBig n : ℝ) =
      ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        ∑ _j ∈ (Finset.Icc 1 X).filter (fun j => p ^ j ∣ n), (1 : ℝ) := by
  have hnat : omegaBig n =
      ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        ((Finset.Icc 1 X).filter (fun j => p ^ j ∣ n)).card := by
    unfold omegaBig
    rw [Finsupp.sum]
    have hsub : n.factorization.support ⊆ (Finset.Icc 2 X).filter Nat.Prime := by
      intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hp.1.two_le, le_trans (Nat.le_of_dvd (by omega) hp.2.1) hnX⟩, hp.1⟩
    rw [Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro p hp
      have hpr : p.Prime := (Finset.mem_filter.mp hp).2
      have hleX : n.factorization p ≤ X := by
        have h1 : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
        have h2 : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) h1
        have h3 : n.factorization p < 2 ^ n.factorization p := Nat.lt_two_pow_self
        have h4 : 2 ^ n.factorization p ≤ p ^ n.factorization p :=
          Nat.pow_le_pow_left hpr.two_le _
        omega
      have heq : (Finset.Icc 1 X).filter (fun j => p ^ j ∣ n) =
          Finset.Icc 1 (n.factorization p) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, hpr.pow_dvd_iff_le_factorization (by omega : n ≠ 0)]
        omega
      rw [heq, Nat.card_Icc]
      omega
    · intro p _ hpnot
      exact Finsupp.notMem_support_iff.mp hpnot
  rw [hnat]
  push_cast
  simp

private lemma sum_omegaBig_mul_w_le (X : ℕ) (hX : 16 ≤ X) :
    ∑ n ∈ Finset.Icc 2 X, (omegaBig n : ℝ) * w (n : ℝ) ≤
      (3 * Real.log (Real.log (X : ℝ)) + 5) * (Real.log (Real.log (X : ℝ)) + 2) := by
  set Pset := (Finset.Icc 2 X).filter Nat.Prime
  have h1 : ∑ n ∈ Finset.Icc 2 X, (omegaBig n : ℝ) * w (n : ℝ) =
      ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X,
        ∑ n ∈ (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n), w (n : ℝ) := by
    have hrew : ∀ n ∈ Finset.Icc 2 X,
        (omegaBig n : ℝ) * w (n : ℝ) =
          ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X, if p ^ j ∣ n then w (n : ℝ) else 0 := by
      intro n hn
      rcases Finset.mem_Icc.mp hn with ⟨hn2, hnX⟩
      rw [omegaBig_eq_prime_pow_count hn2 hnX, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hrew, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_filter]
  have hinner : ∀ p ∈ Pset, ∀ j ∈ Finset.Icc 1 X,
      ∑ n ∈ (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n), w (n : ℝ) ≤
        (if p ^ j ≤ X then w ((p ^ j : ℕ) : ℝ) else 0) +
          ((1 : ℝ) / ((p ^ j : ℕ) : ℝ)) * (∑ m ∈ Finset.Icc 2 X, w (m : ℝ)) := by
    intro p hp j hj
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpj_ge2 : 2 ≤ p ^ j := le_trans hpr.two_le (Nat.le_self_pow (by omega) p)
    have hsplit : (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n) =
        ((Finset.Icc 2 X).filter (fun n => n = p ^ j)) ∪
          ((Finset.Icc 2 X).filter (fun n => p ^ j ∣ n ∧ p ^ j < n)) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hn2, hnX⟩, hd⟩
        have hle : p ^ j ≤ n := Nat.le_of_dvd (by omega) hd
        by_cases heq : n = p ^ j
        · exact Or.inl ⟨⟨hn2, hnX⟩, heq⟩
        · exact Or.inr ⟨⟨hn2, hnX⟩, hd, by omega⟩
      · rintro (⟨hI, rfl⟩ | ⟨hI, hd, _⟩)
        · exact ⟨hI, dvd_refl _⟩
        · exact ⟨hI, hd⟩
    have hdisj : Disjoint ((Finset.Icc 2 X).filter (fun n => n = p ^ j))
        ((Finset.Icc 2 X).filter (fun n => p ^ j ∣ n ∧ p ^ j < n)) := by
      rw [Finset.disjoint_filter]
      intro n _ h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hfirst : ∑ n ∈ (Finset.Icc 2 X).filter (fun n => n = p ^ j), w (n : ℝ) ≤
        if p ^ j ≤ X then w ((p ^ j : ℕ) : ℝ) else 0 := by
      by_cases hle : p ^ j ≤ X
      · rw [if_pos hle]
        have heq : (Finset.Icc 2 X).filter (fun n => n = p ^ j) = {p ^ j} := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl; exact ⟨⟨hpj_ge2, hle⟩, rfl⟩
        rw [heq, Finset.sum_singleton]
      · rw [if_neg hle]
        have heq : (Finset.Icc 2 X).filter (fun n => n = p ^ j) = ∅ := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
          rintro ⟨⟨_, hnX⟩, rfl⟩
          exact hle hnX
        rw [heq, Finset.sum_empty]
    have hsecond : ∑ n ∈ (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n ∧ p ^ j < n), w (n : ℝ) ≤
        ((1 : ℝ) / ((p ^ j : ℕ) : ℝ)) * (∑ m ∈ Finset.Icc 2 X, w (m : ℝ)) := by
      let g : ℕ → ℕ := fun m => p ^ j * m
      have hsub : (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n ∧ p ^ j < n) ⊆
          (Finset.Icc 2 X).image g := by
        intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hI, ⟨m, rfl⟩, hlt⟩
        rcases Finset.mem_Icc.mp hI with ⟨_, hXle⟩
        have hm2 : 2 ≤ m := by
          by_contra hm
          have : m = 0 ∨ m = 1 := by omega
          rcases this with rfl | rfl <;> simp at hlt
        have hmX : m ≤ X := le_trans (Nat.le_mul_of_pos_left m (by omega)) hXle
        exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm2, hmX⟩, rfl⟩
      have hinj : Set.InjOn g ((Finset.Icc 2 X : Finset ℕ) : Set ℕ) :=
        fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left (by omega) heq
      calc
        ∑ n ∈ (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n ∧ p ^ j < n), w (n : ℝ)
            ≤ ∑ n ∈ (Finset.Icc 2 X).image g, w (n : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => by
                rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
                have hm2 := (Finset.mem_Icc.mp hm).1
                exact le_of_lt (w_pos (by exact_mod_cast (by nlinarith : 1 < p ^ j * m))))
        _ = ∑ m ∈ Finset.Icc 2 X, w ((p ^ j * m : ℕ) : ℝ) := Finset.sum_image hinj
        _ ≤ ∑ m ∈ Finset.Icc 2 X, ((1 : ℝ) / ((p ^ j : ℕ) : ℝ)) * w (m : ℝ) := by
              apply Finset.sum_le_sum
              intro m hm
              have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
              have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
              have hpj_pos : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p ^ j)
              have hlog_le : Real.log (m : ℝ) ≤ Real.log ((p ^ j * m : ℕ) : ℝ) :=
                Real.log_le_log (by linarith) (by exact_mod_cast (Nat.le_mul_of_pos_left m (by omega)))
              unfold w
              have h1 : (1 : ℝ) / ((p ^ j : ℕ) : ℝ) * (1 / ((m : ℝ) * Real.log (m : ℝ))) =
                  1 / (((p ^ j * m : ℕ) : ℝ) * Real.log (m : ℝ)) := by
                push_cast
                field_simp
              rw [h1]
              apply one_div_le_one_div_of_le (mul_pos (by positivity) (Real.log_pos hm_gt1))
              exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
        _ = ((1 : ℝ) / ((p ^ j : ℕ) : ℝ)) * (∑ m ∈ Finset.Icc 2 X, w (m : ℝ)) :=
              (Finset.mul_sum _ _ _).symm
    linarith
  have hfirst_sum :
      ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X, (if p ^ j ≤ X then w ((p ^ j : ℕ) : ℝ) else 0) ≤
        ∑ n ∈ Finset.Icc 2 X, w (n : ℝ) := by
    let Q := (Pset ×ˢ Finset.Icc 1 X).filter (fun pj => pj.1 ^ pj.2 ≤ X)
    have hrew : ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X,
        (if p ^ j ≤ X then w ((p ^ j : ℕ) : ℝ) else 0) =
        ∑ pj ∈ Q, w ((pj.1 ^ pj.2 : ℕ) : ℝ) := by
      rw [← Finset.sum_product', Finset.sum_filter]
    rw [hrew]
    let f : ℕ × ℕ → ℕ := fun pj => pj.1 ^ pj.2
    have hinj : Set.InjOn f (Q : Set (ℕ × ℕ)) := by
      rintro ⟨p₁, j₁⟩ h₁ ⟨p₂, j₂⟩ h₂ heq
      simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Pset,
        Finset.mem_Icc] at h₁ h₂
      have hp1 : p₁.Prime := h₁.1.1.2
      have hp2 : p₂.Prime := h₂.1.1.2
      have hj1 : 1 ≤ j₁ := h₁.1.2.1
      have hj2 : 1 ≤ j₂ := h₂.1.2.1
      have hpeq : p₁ = p₂ := by
        have hd : p₁ ∣ p₂ ^ j₂ := by
          have : p₁ ∣ p₁ ^ j₁ := dvd_pow_self p₁ (by omega)
          rwa [show p₁ ^ j₁ = p₂ ^ j₂ from heq] at this
        exact (Nat.prime_dvd_prime_iff_eq hp1 hp2).mp (hp1.dvd_of_dvd_pow hd)
      subst hpeq
      have hjeq : j₁ = j₂ := Nat.pow_right_injective hp1.two_le heq
      exact Prod.ext rfl hjeq
    have hsub : Q.image f ⊆ Finset.Icc 2 X := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨⟨p, j⟩, hpj, rfl⟩
      simp only [Q, Finset.mem_filter, Finset.mem_product, Pset, Finset.mem_Icc] at hpj
      exact Finset.mem_Icc.mpr ⟨le_trans hpj.1.1.2.two_le (Nat.le_self_pow (by omega) p), hpj.2⟩
    have himg : ∑ n ∈ Q.image f, w (n : ℝ) = ∑ pj ∈ Q, w ((f pj : ℕ) : ℝ) :=
      Finset.sum_image (f := fun n : ℕ => w (n : ℝ)) hinj
    change ∑ pj ∈ Q, w ((f pj : ℕ) : ℝ) ≤ _
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => le_of_lt (w_pos (by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 1 < n))))
  have hT_bound :
      ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) ≤
        3 * Real.log (Real.log (X : ℝ)) + 4 := by
    have hsplit : ∀ p ∈ Pset,
        ∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) =
          (1 : ℝ) / (p : ℝ) + ∑ j ∈ Finset.Icc 2 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ) := by
      intro p _
      have heq : Finset.Icc 1 X = insert 1 (Finset.Icc 2 X) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [heq, Finset.sum_insert (by simp), pow_one]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have h1' := sum_prime_inv_le X hX
    have h2' := sum_prime_pow_ge2_le X
    linarith
  have hS_nonneg : 0 ≤ ∑ n ∈ Finset.Icc 2 X, w (n : ℝ) :=
    Finset.sum_nonneg (fun n hn =>
      le_of_lt (w_pos (by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 1 < n))))
  have hS_bound := sum_w_Icc_le X (by omega)
  have hT1_nonneg : 0 ≤ 3 * Real.log (Real.log (X : ℝ)) + 5 := by
    have hlogX : (2 : ℝ) ≤ Real.log (X : ℝ) := by
      have h2 : (2 : ℝ) ^ 4 ≤ (X : ℝ) := by exact_mod_cast hX
      have h1' : Real.log ((2 : ℝ) ^ 4) ≤ Real.log (X : ℝ) := Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h1'
      have := half_lt_log_two
      push_cast at h1'
      linarith
    have : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  calc
    ∑ n ∈ Finset.Icc 2 X, (omegaBig n : ℝ) * w (n : ℝ)
        = ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X,
            ∑ n ∈ (Finset.Icc 2 X).filter (fun n => p ^ j ∣ n), w (n : ℝ) := h1
    _ ≤ ∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X,
          ((if p ^ j ≤ X then w ((p ^ j : ℕ) : ℝ) else 0) +
            ((1 : ℝ) / ((p ^ j : ℕ) : ℝ)) * (∑ m ∈ Finset.Icc 2 X, w (m : ℝ))) :=
          Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun j hj => hinner p hp j hj))
    _ = (∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X, if p ^ j ≤ X then w ((p ^ j : ℕ) : ℝ) else 0) +
          (∑ p ∈ Pset, ∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / ((p ^ j : ℕ) : ℝ)) *
            (∑ m ∈ Finset.Icc 2 X, w (m : ℝ)) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ ≤ (∑ n ∈ Finset.Icc 2 X, w (n : ℝ)) +
          (3 * Real.log (Real.log (X : ℝ)) + 4) * (∑ m ∈ Finset.Icc 2 X, w (m : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hT_bound hS_nonneg
          linarith
    _ = (3 * Real.log (Real.log (X : ℝ)) + 5) * (∑ m ∈ Finset.Icc 2 X, w (m : ℝ)) := by ring
    _ ≤ (3 * Real.log (Real.log (X : ℝ)) + 5) * (Real.log (Real.log (X : ℝ)) + 2) :=
          mul_le_mul_of_nonneg_left hS_bound hT1_nonneg

private lemma periodic_sum_w_ge {M : ℕ} (hM : 1 ≤ M) {Rgood : Finset ℕ}
    (hRsub : Rgood ⊆ Finset.range M) (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ X : ℕ, (N + 2 * M) ≤ X →
      ((Rgood.card : ℝ) / (M : ℝ)) * Real.log (Real.log (X : ℝ)) - C ≤
        ∑ n ∈ (Finset.Icc N X).filter (fun n => n % M ∈ Rgood), w (n : ℝ) := by
  set K0 : ℕ := N / M + 2
  have hK0_ge2 : 2 ≤ K0 := Nat.le_add_left 2 (N / M)
  have hK0M_geN : N ≤ K0 * M := by
    have := Nat.lt_div_mul_add (a := N) (b := M) (by omega)
    dsimp only [K0]
    nlinarith
  refine ⟨((Rgood.card : ℝ) / (M : ℝ)) * Real.log (Real.log ((M * (K0 + 1) : ℕ) : ℝ)),
    fun X hX => ?_⟩
  set K1 : ℕ := X / M
  have hK0_le_K1 : K0 ≤ K1 := by
    dsimp only [K0, K1]
    have h1 : N + 2 * M ≤ X := hX
    have h2 : (N / M + 2) * M ≤ X := by
      have := Nat.div_mul_le_self N M
      nlinarith
    exact (Nat.le_div_iff_mul_le (by omega)).mpr h2
  let f : ℕ × ℕ → ℕ := fun kr => kr.1 * M + kr.2
  let dom := Finset.Ico K0 K1 ×ˢ Rgood
  have hinj : Set.InjOn f (dom : Set (ℕ × ℕ)) := by
    rintro ⟨k₁, r₁⟩ h₁ ⟨k₂, r₂⟩ h₂ hfeq
    simp only [dom, Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
    have hr1 : r₁ < M := Finset.mem_range.mp (hRsub h₁.2)
    have hr2 : r₂ < M := Finset.mem_range.mp (hRsub h₂.2)
    have hmod : r₁ = r₂ := by
      have h1' : (k₁ * M + r₁) % M = r₁ := by
        rw [Nat.mul_add_mod_of_lt hr1]
      have h2' : (k₂ * M + r₂) % M = r₂ := by
        rw [Nat.mul_add_mod_of_lt hr2]
      rw [← h1', ← h2']
      exact congrArg (· % M) hfeq
    subst hmod
    dsimp only [f] at hfeq
    have hk : k₁ = k₂ := by
      have : k₁ * M = k₂ * M := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    exact Prod.ext hk rfl
  have hsub : dom.image f ⊆ (Finset.Icc N X).filter (fun n => n % M ∈ Rgood) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨⟨k, r⟩, hkr, rfl⟩
    rcases Finset.mem_product.mp hkr with ⟨hk, hr⟩
    rcases Finset.mem_Ico.mp hk with ⟨hk0, hk1⟩
    have hrlt : r < M := Finset.mem_range.mp (hRsub hr)
    have hNle : N ≤ k * M + r := by
      have : K0 * M ≤ k * M := Nat.mul_le_mul_right M hk0
      omega
    have hXge : k * M + r ≤ X := by
      have h1 : (k + 1) * M ≤ K1 * M := Nat.mul_le_mul_right M hk1
      have h2 : K1 * M ≤ X := Nat.div_mul_le_self X M
      nlinarith
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hNle, hXge⟩, ?_⟩
    dsimp only [f]
    rwa [Nat.mul_add_mod_of_lt hrlt]
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hstep1 : ∑ n ∈ dom.image f, w (n : ℝ) ≤
      ∑ n ∈ (Finset.Icc N X).filter (fun n => n % M ∈ Rgood), w (n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ =>
      le_of_lt (w_pos (by exact_mod_cast (by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1; omega : 1 < n))))
  have hstep2 : ((Rgood.card : ℝ) / (M : ℝ)) *
      (∑ m ∈ Finset.Ico (K0 + 1) (K1 + 1), 1 / ((m : ℝ) * Real.log ((M * m : ℕ) : ℝ))) ≤
      ∑ n ∈ dom.image f, w (n : ℝ) := by
    rw [Finset.sum_image hinj, Finset.sum_product]
    have hge : ∀ k ∈ Finset.Ico K0 K1,
        ((Rgood.card : ℝ) / (M : ℝ)) * (1 / (((k + 1 : ℕ) : ℝ) * Real.log ((M * (k + 1) : ℕ) : ℝ))) ≤
          ∑ r ∈ Rgood, w ((k * M + r : ℕ) : ℝ) := by
      intro k hk
      have hk0 : K0 ≤ k := (Finset.mem_Ico.mp hk).1
      have hterm : ∀ r ∈ Rgood, w ((M * (k + 1) : ℕ) : ℝ) ≤ w ((k * M + r : ℕ) : ℝ) := by
        intro r hr
        have hrlt : r < M := Finset.mem_range.mp (hRsub hr)
        apply w_anti
        · have : 2 ≤ k * M + r := by nlinarith
          exact_mod_cast (by omega : 1 < k * M + r)
        · exact_mod_cast (by nlinarith : k * M + r ≤ M * (k + 1))
      have hsum_ge : (Rgood.card : ℝ) * w ((M * (k + 1) : ℕ) : ℝ) ≤
          ∑ r ∈ Rgood, w ((k * M + r : ℕ) : ℝ) := by
        calc
          (Rgood.card : ℝ) * w ((M * (k + 1) : ℕ) : ℝ)
              = ∑ _r ∈ Rgood, w ((M * (k + 1) : ℕ) : ℝ) := by simp
          _ ≤ ∑ r ∈ Rgood, w ((k * M + r : ℕ) : ℝ) := Finset.sum_le_sum hterm
      have heq : ((Rgood.card : ℝ) / (M : ℝ)) *
          (1 / (((k + 1 : ℕ) : ℝ) * Real.log ((M * (k + 1) : ℕ) : ℝ))) =
          (Rgood.card : ℝ) * w ((M * (k + 1) : ℕ) : ℝ) := by
        unfold w
        rw [Nat.cast_mul]
        ring
      linarith
    calc
      ((Rgood.card : ℝ) / (M : ℝ)) *
          (∑ m ∈ Finset.Ico (K0 + 1) (K1 + 1), 1 / ((m : ℝ) * Real.log ((M * m : ℕ) : ℝ)))
          = ((Rgood.card : ℝ) / (M : ℝ)) *
              (∑ k ∈ Finset.Ico K0 K1,
                1 / (((k + 1 : ℕ) : ℝ) * Real.log ((M * (k + 1) : ℕ) : ℝ))) := by
            congr 1
            have hbij : Finset.Ico (K0 + 1) (K1 + 1) = (Finset.Ico K0 K1).image (· + 1) := by
              ext m
              simp only [Finset.mem_Ico, Finset.mem_image]
              constructor
              · intro hm; exact ⟨m - 1, by omega, by omega⟩
              · rintro ⟨k, hk, rfl⟩; omega
            rw [hbij, Finset.sum_image (fun _ _ _ _ h => by omega)]
      _ = ∑ k ∈ Finset.Ico K0 K1,
            ((Rgood.card : ℝ) / (M : ℝ)) *
              (1 / (((k + 1 : ℕ) : ℝ) * Real.log ((M * (k + 1) : ℕ) : ℝ))) := Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Finset.Ico K0 K1, ∑ r ∈ Rgood, w ((k * M + r : ℕ) : ℝ) := Finset.sum_le_sum hge
  have hstep3 := sum_inv_mul_log_ge (a := K0 + 1) (b := K1 + 1) (M := M)
    (by omega) (by omega) hM
  have hX_le : (X : ℝ) ≤ ((M * (K1 + 1) : ℕ) : ℝ) := by
    have : X < M * (K1 + 1) := by
      dsimp only [K1]
      have := Nat.lt_div_mul_add (a := X) (b := M) (by omega)
      nlinarith
    exact_mod_cast (le_of_lt this)
  have hll_le : Real.log (Real.log (X : ℝ)) ≤ Real.log (Real.log ((M * (K1 + 1) : ℕ) : ℝ)) := by
    have hX_gt1 : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
    exact Real.log_le_log (Real.log_pos hX_gt1) (Real.log_le_log (by linarith) hX_le)
  have hdens_nonneg : 0 ≤ (Rgood.card : ℝ) / (M : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (le_trans (sub_le_sub_right hll_le _) hstep3) hdens_nonneg
  linarith

private lemma lemma7_primitive_selection {M : ℕ} (hM : 1 ≤ M) {Rgood : Finset ℕ}
    (hRsub : Rgood ⊆ Finset.range M) (hdens : (2 / 3 : ℝ) < (Rgood.card : ℝ) / (M : ℝ))
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, P.Nonempty ∧
      (∀ n ∈ P, N ≤ n ∧ n % M ∈ Rgood) ∧
      (∀ m ∈ P, ∀ n ∈ P, m ≠ n → ¬ (m ∣ n)) ∧
      (1 / 48 : ℝ) < Wnat P := by
  obtain ⟨C, hC⟩ := periodic_sum_w_ge hM hRsub N hN
  set δ : ℝ := (Rgood.card : ℝ) / (M : ℝ)
  have htend_ll : Tendsto (fun X : ℕ => Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨X, hX_ge, hL_big⟩ :
      ∃ X : ℕ, max 16 (N + 2 * M) ≤ X ∧
        max 100 (12 * (|C| + 1)) < Real.log (Real.log (X : ℝ)) := by
    have h1 := htend_ll.eventually_gt_atTop (max 100 (12 * (|C| + 1)))
    have h2 := eventually_ge_atTop (max 16 (N + 2 * M))
    obtain ⟨X, hX1, hX2⟩ := (h1.and h2).exists
    exact ⟨X, hX2, hX1⟩
  have hX16 : 16 ≤ X := le_trans (le_max_left _ _) hX_ge
  have hXNM : N + 2 * M ≤ X := le_trans (le_max_right _ _) hX_ge
  set L : ℝ := Real.log (Real.log (X : ℝ))
  have hL100 : (100 : ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL_big
  have hLC : 12 * (|C| + 1) < L := lt_of_le_of_lt (le_max_right _ _) hL_big
  set E_fin := (Finset.Icc N X).filter (fun n => n % M ∈ Rgood)
  have hE_weight : δ * L - C ≤ ∑ n ∈ E_fin, w (n : ℝ) := hC X hXNM
  set R : ℕ := Nat.floor (14 * L)
  have hR_le : (R : ℝ) ≤ 14 * L := Nat.floor_le (by linarith)
  have hR_gt : 14 * L - 1 < (R : ℝ) := Nat.sub_one_lt_floor (14 * L)
  have hR_pos : 1 ≤ R := by
    have : (1 : ℝ) < (R : ℝ) := by linarith
    exact_mod_cast (le_of_lt this)
  have htail : ∑ n ∈ E_fin.filter (fun n => R < omegaBig n), w (n : ℝ) ≤ L / 4 := by
    have hsub : E_fin.filter (fun n => R < omegaBig n) ⊆ Finset.Icc 2 X := by
      intro n hn
      have hI := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      rcases Finset.mem_Icc.mp hI with ⟨hNn, hnX⟩
      exact Finset.mem_Icc.mpr ⟨by omega, hnX⟩
    have hmarkov : (14 * L - 1) * ∑ n ∈ E_fin.filter (fun n => R < omegaBig n), w (n : ℝ) ≤
        ∑ n ∈ Finset.Icc 2 X, (omegaBig n : ℝ) * w (n : ℝ) := by
      rw [Finset.mul_sum]
      calc
        ∑ n ∈ E_fin.filter (fun n => R < omegaBig n), (14 * L - 1) * w (n : ℝ)
            ≤ ∑ n ∈ E_fin.filter (fun n => R < omegaBig n), (omegaBig n : ℝ) * w (n : ℝ) := by
              apply Finset.sum_le_sum
              intro n hn
              have hlt : R < omegaBig n := (Finset.mem_filter.mp hn).2
              have hle : 14 * L - 1 ≤ (omegaBig n : ℝ) := by
                have : (R : ℝ) < (omegaBig n : ℝ) := by exact_mod_cast hlt
                linarith
              have hn2 : 2 ≤ n := (Finset.mem_Icc.mp (hsub hn)).1
              exact mul_le_mul_of_nonneg_right hle (le_of_lt (w_pos (by exact_mod_cast (by omega : 1 < n))))
        _ ≤ ∑ n ∈ Finset.Icc 2 X, (omegaBig n : ℝ) * w (n : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => by
                have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
                exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (w_pos (by exact_mod_cast (by omega : 1 < n)))))
    have hmom := sum_omegaBig_mul_w_le X hX16
    have hnum : (3 * L + 5) * (L + 2) ≤ (14 * L - 1) * (L / 4) := by nlinarith
    have hpos : (0 : ℝ) < 14 * L - 1 := by linarith
    nlinarith
  have hlow : (L / 3 : ℝ) < ∑ n ∈ E_fin.filter (fun n => omegaBig n ≤ R), w (n : ℝ) := by
    have hpart : ∑ n ∈ E_fin, w (n : ℝ) =
        (∑ n ∈ E_fin.filter (fun n => omegaBig n ≤ R), w (n : ℝ)) +
        (∑ n ∈ E_fin.filter (fun n => R < omegaBig n), w (n : ℝ)) := by
      have := Finset.sum_filter_add_sum_filter_not E_fin (fun n => omegaBig n ≤ R) (fun n => w (n : ℝ))
      simp only [not_le] at this
      linarith
    have hCab : C ≤ |C| := le_abs_self C
    nlinarith
  have hfiber : ∑ n ∈ E_fin.filter (fun n => omegaBig n ≤ R), w (n : ℝ) =
      ∑ r ∈ Finset.Icc 1 R, Wnat (E_fin.filter (fun n => omegaBig n = r)) := by
    unfold Wnat
    rw [← Finset.sum_biUnion]
    · congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
      constructor
      · rintro ⟨hnE, hle⟩
        have hn2 : 2 ≤ n := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnE).1).1
          omega
        exact ⟨omegaBig n, ⟨omegaBig_pos hn2, hle⟩, hnE, rfl⟩
      · rintro ⟨r, ⟨_, hrR⟩, hnE, rfl⟩
        exact ⟨hnE, hrR⟩
    · intro r₁ _ r₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro n _ h1 h2
      exact hne (h1.symm.trans h2)
  have hex : ∃ r ∈ Finset.Icc 1 R, (1 / 48 : ℝ) < Wnat (E_fin.filter (fun n => omegaBig n = r)) := by
    by_contra hall
    push Not at hall
    have hsum_le : ∑ r ∈ Finset.Icc 1 R, Wnat (E_fin.filter (fun n => omegaBig n = r)) ≤
        (R : ℝ) * (1 / 48 : ℝ) := by
      calc
        ∑ r ∈ Finset.Icc 1 R, Wnat (E_fin.filter (fun n => omegaBig n = r))
            ≤ ∑ _r ∈ Finset.Icc 1 R, (1 / 48 : ℝ) := Finset.sum_le_sum hall
        _ = ((Finset.Icc 1 R).card : ℝ) * (1 / 48 : ℝ) := by simp
        _ = (R : ℝ) * (1 / 48 : ℝ) := by rw [Nat.card_Icc]; simp
    linarith
  obtain ⟨r, hrI, hW⟩ := hex
  set P := E_fin.filter (fun n => omegaBig n = r)
  have hP_ne : P.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hW
    unfold Wnat at hW
    simp at hW
    linarith
  refine ⟨P, hP_ne, ?_, ?_, hW⟩
  · intro n hn
    have hE := (Finset.mem_filter.mp hn).1
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hE).1).1, (Finset.mem_filter.mp hE).2⟩
  · intro m hm n hn hne hd
    have hrm : omegaBig m = r := (Finset.mem_filter.mp hm).2
    have hrn : omegaBig n = r := (Finset.mem_filter.mp hn).2
    have hm2 : 2 ≤ m := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).1
      omega
    obtain ⟨k, rfl⟩ := hd
    have hk2 : 2 ≤ k := by
      by_contra hk
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · have hn2 : 2 ≤ m * 0 := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
          omega
        omega
      · exact hne (by ring)
    have hadd := omegaBig_mul (a := m) (b := k) (by omega) (by omega)
    have hkpos := omegaBig_pos hk2
    omega

/- ### Part 2: Periodic residue union bound -/

private lemma card_filter_mod_mem {M d : ℕ} (hd : 0 < d) (hdM : d ∣ M)
    {S : Finset ℕ} (hS : S ⊆ Finset.range d) :
    ((Finset.range M).filter (fun x => x % d ∈ S)).card = (M / d) * S.card := by
  let f : ℕ × ℕ → ℕ := fun qr => qr.1 * d + qr.2
  have hbij : (Finset.range M).filter (fun x => x % d ∈ S) = (Finset.range (M / d) ×ˢ S).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨hxM, hxS⟩
      refine ⟨x / d, x % d, ⟨?_, hxS⟩, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.div_mul_cancel hdM]; exact hxM)
      · dsimp only [f]; rw [mul_comm, Nat.div_add_mod]
    · rintro ⟨q, r, ⟨hq, hr⟩, rfl⟩
      have hrlt : r < d := Finset.mem_range.mp (hS hr)
      refine ⟨?_, ?_⟩
      · dsimp only [f]
        have h1 : (q + 1) * d ≤ (M / d) * d := Nat.mul_le_mul_right d hq
        rw [Nat.div_mul_cancel hdM] at h1
        nlinarith
      · dsimp only [f]
        rwa [Nat.mul_add_mod_of_lt hrlt]
  have hinj : Set.InjOn f ((Finset.range (M / d) ×ˢ S : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro ⟨q₁, r₁⟩ h₁ ⟨q₂, r₂⟩ h₂ hfeq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
    have hr1 : r₁ < d := Finset.mem_range.mp (hS h₁.2)
    have hr2 : r₂ < d := Finset.mem_range.mp (hS h₂.2)
    have hreq : r₁ = r₂ := by
      have h1' : (q₁ * d + r₁) % d = r₁ := Nat.mul_add_mod_of_lt hr1
      have h2' : (q₂ * d + r₂) % d = r₂ := Nat.mul_add_mod_of_lt hr2
      rw [← h1', ← h2']
      exact congrArg (· % d) hfeq
    subst hreq
    dsimp only [f] at hfeq
    have hqeq : q₁ = q₂ := Nat.eq_of_mul_eq_mul_right hd (by omega : q₁ * d = q₂ * d)
    exact Prod.ext hqeq rfl
  rw [hbij, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]

private lemma card_filter_mod_mem_div {M d : ℕ} (hM : 0 < M) (hd : 0 < d) (hdM : d ∣ M)
    {S : Finset ℕ} (hS : S ⊆ Finset.range d) :
    (((Finset.range M).filter (fun x => x % d ∈ S)).card : ℝ) / (M : ℝ) =
      (S.card : ℝ) / (d : ℝ) := by
  rw [card_filter_mod_mem hd hdM hS, Nat.cast_mul]
  have hMeq : (M : ℝ) = ((M / d : ℕ) : ℝ) * (d : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel hdM).symm
  have hMd_ne : ((M / d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < M / d := Nat.div_pos (Nat.le_of_dvd hM hdM) hd
    positivity
  have hd_ne : (d : ℝ) ≠ 0 := by positivity
  rw [hMeq]
  field_simp

/- ### Part 3: Rational blocks and finite admissible configurations -/

private structure Block where
  D : ℕ
  p : ℕ
  q : ℕ
  P : Finset ℕ
  hD : 48 ≤ D
  hp : p.Prime
  hp2 : 2 < p
  hq : 2 ≤ q
  hP_ne : P.Nonempty
  hP_ge2 : ∀ n ∈ P, 2 ≤ n
  hP_prim : ∀ m ∈ P, ∀ n ∈ P, m ≠ n → ¬ (m ∣ n)

private noncomputable def Block.pt (B : Block) (n : ℕ) : ℝ :=
  ((B.D * n * B.p * B.q : ℕ) : ℝ) / ((B.p * B.q - 1 : ℕ) : ℝ)

private noncomputable def Block.pts (B : Block) : Finset ℝ :=
  B.P.image B.pt

private lemma Block.pq_ge6 (B : Block) : 6 ≤ B.p * B.q := by
  have := B.hp2
  have := B.hq
  nlinarith

private lemma Block.pt_gt_Dn (B : Block) {n : ℕ} (hn : 1 ≤ n) :
    ((B.D * n : ℕ) : ℝ) < B.pt n := by
  unfold Block.pt
  have hpq : 6 ≤ B.p * B.q := B.pq_ge6
  have hden : (0 : ℝ) < ((B.p * B.q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < B.p * B.q - 1)
  rw [lt_div_iff₀ hden]
  have hnat : (B.D * n) * (B.p * B.q - 1) < B.D * n * B.p * B.q := by
    have hDn : 1 ≤ B.D * n := by have := B.hD; nlinarith
    have hlt : B.p * B.q - 1 < B.p * B.q := by omega
    have := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < B.D * n)
    linarith
  exact_mod_cast hnat

private lemma Block.pt_gt_two (B : Block) {n : ℕ} (hn : n ∈ B.P) : (2 : ℝ) < B.pt n := by
  have hn2 := B.hP_ge2 n hn
  have h1 := B.pt_gt_Dn (by omega : 1 ≤ n)
  have h2 : (2 : ℝ) ≤ ((B.D * n : ℕ) : ℝ) := by
    have := B.hD
    exact_mod_cast (by nlinarith : 2 ≤ B.D * n)
  linarith

private lemma Block.pt_injective (B : Block) : Function.Injective B.pt := by
  intro m n h
  unfold Block.pt at h
  have hpq : 6 ≤ B.p * B.q := B.pq_ge6
  have hden : ((B.p * B.q - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.p * B.q - 1 ≠ 0)
  have hnum : ((B.D * m * B.p * B.q : ℕ) : ℝ) = ((B.D * n * B.p * B.q : ℕ) : ℝ) :=
    (div_left_inj' hden).mp h
  have hnat : B.D * m * B.p * B.q = B.D * n * B.p * B.q := by exact_mod_cast hnum
  have hD : 0 < B.D := by have := B.hD; omega
  have h1 : B.D * m * B.p = B.D * n * B.p := Nat.eq_of_mul_eq_mul_right (by have := B.hq; omega) hnat
  have h2 : B.D * m = B.D * n := Nat.eq_of_mul_eq_mul_right B.hp.pos h1
  exact Nat.eq_of_mul_eq_mul_left hD h2

private noncomputable def ptsOf (bs : List Block) : Finset ℝ :=
  bs.foldr (fun B acc => B.pts ∪ acc) ∅

private lemma mem_ptsOf_iff {bs : List Block} {x : ℝ} :
    x ∈ ptsOf bs ↔ ∃ B ∈ bs, x ∈ B.pts := by
  induction bs with
  | nil => simp [ptsOf]
  | cons B bs ih =>
    simp only [ptsOf, List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    exact or_congr_right ih

private structure Admissible (bs : List Block) : Prop where
  sep : ∀ a ∈ ptsOf bs, ∀ b ∈ ptsOf bs, a ≠ b → ∀ k : ℕ, 1 ≤ k → (1 : ℝ) < |(k : ℝ) * a - b|
  nodup_p : (bs.map Block.p).Nodup
  ndvd : ∀ B₁ ∈ bs, ∀ B₂ ∈ bs, ∀ n ∈ B₁.P, ¬ (B₂.p ∣ B₁.q * B₁.D * n)
  ratio : ∀ B ∈ bs, ∀ n ∈ B.P, (4 : ℝ) * (B.p : ℝ) < B.pt n
  psum : (bs.map (fun B => (1 : ℝ) / (B.p : ℝ))).sum < 1 / 100

private lemma admissible_nil : Admissible [] := by
  refine ⟨by simp [ptsOf], by simp, by simp, by simp, by norm_num⟩

private lemma old_point_sep {B : Block} {n D ℓ : ℕ} (hn : n ∈ B.P)
    (hdiv : B.q * B.D * n ∣ D) (hndvdD : ¬ (B.p ∣ D)) (hndvdℓ : ¬ (B.p ∣ ℓ))
    (hratio : (4 : ℝ) * (B.p : ℝ) < B.pt n) (k : ℕ) :
    (4 : ℝ) < |(k : ℝ) * B.pt n - ((D * ℓ : ℕ) : ℝ)| := by
  obtain ⟨v, hv⟩ := hdiv
  have hpndv : ¬ (B.p ∣ v) := fun hd => hndvdD (hv ▸ dvd_mul_of_dvd_right hd _)
  have hpq : 6 ≤ B.p * B.q := B.pq_ge6
  have hden_pos : (0 : ℝ) < ((B.p * B.q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < B.p * B.q - 1)
  have hp_pos : (0 : ℝ) < (B.p : ℝ) := by exact_mod_cast B.hp.pos
  set z : ℤ := (k : ℤ) * (B.p : ℤ) - (v : ℤ) * ((B.p * B.q - 1 : ℕ) : ℤ) * (ℓ : ℤ)
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hd1 : (B.p : ℤ) ∣ (v : ℤ) * ((B.p * B.q - 1 : ℕ) : ℤ) * (ℓ : ℤ) := by
      have : (v : ℤ) * ((B.p * B.q - 1 : ℕ) : ℤ) * (ℓ : ℤ) = (k : ℤ) * (B.p : ℤ) := by linarith
      rw [this]
      exact dvd_mul_left _ _
    have hcast : ((B.p * B.q - 1 : ℕ) : ℤ) = (B.p : ℤ) * (B.q : ℤ) - 1 := by
      rw [Int.ofNat_sub (by omega : 1 ≤ B.p * B.q)]
      push_cast
      rfl
    have hd2 : (B.p : ℤ) ∣ (v : ℤ) * (ℓ : ℤ) := by
      have hrew : (v : ℤ) * ((B.p * B.q - 1 : ℕ) : ℤ) * (ℓ : ℤ) =
          (B.p : ℤ) * ((v : ℤ) * (B.q : ℤ) * (ℓ : ℤ)) - (v : ℤ) * (ℓ : ℤ) := by
        rw [hcast]
        ring
      rw [hrew] at hd1
      have hsub := dvd_sub (dvd_mul_right (B.p : ℤ) ((v : ℤ) * (B.q : ℤ) * (ℓ : ℤ))) hd1
      simpa using hsub
    have hd3 : B.p ∣ v * ℓ := by
      exact_mod_cast hd2
    rcases B.hp.dvd_mul.mp hd3 with hdv | hdℓ
    · exact hpndv hdv
    · exact hndvdℓ hdℓ
  have hz_ge1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz_ne
    exact_mod_cast this
  have hfactor : (k : ℝ) * B.pt n - ((D * ℓ : ℕ) : ℝ) = (B.pt n / (B.p : ℝ)) * (z : ℝ) := by
    unfold Block.pt
    have hDcast : (D : ℝ) = (B.q : ℝ) * (B.D : ℝ) * (n : ℝ) * (v : ℝ) := by
      exact_mod_cast hv
    have hzcast : (z : ℝ) = (k : ℝ) * (B.p : ℝ) - (v : ℝ) * ((B.p * B.q - 1 : ℕ) : ℝ) * (ℓ : ℝ) := by
      dsimp only [z]
      push_cast
      ring
    rw [hzcast]
    push_cast
    rw [hDcast]
    field_simp
  rw [hfactor, abs_mul]
  have hratio' : (4 : ℝ) < B.pt n / (B.p : ℝ) := (lt_div_iff₀ hp_pos).mpr hratio
  have hpos : 0 < B.pt n / (B.p : ℝ) := by linarith
  rw [abs_of_pos hpos]
  nlinarith

private def badRes (D : ℕ) (B : Block) : Finset ℕ :=
  let pq := B.p * B.q
  let K := (pq - 1) / D
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).image (fun z => (z % (pq : ℤ)).toNat)

private lemma badRes_subset (D : ℕ) (B : Block) : badRes D B ⊆ Finset.range (B.p * B.q) := by
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨z, _, rfl⟩
  have hpq : 0 < B.p * B.q := by have := B.pq_ge6; omega
  have hpqZ : (0 : ℤ) < ((B.p * B.q : ℕ) : ℤ) := by exact_mod_cast hpq
  have hnonneg : 0 ≤ z % ((B.p * B.q : ℕ) : ℤ) := Int.emod_nonneg z (ne_of_gt hpqZ)
  have hlt : z % ((B.p * B.q : ℕ) : ℤ) < ((B.p * B.q : ℕ) : ℤ) := Int.emod_lt_of_pos z hpqZ
  rw [Finset.mem_range]
  omega

private lemma badRes_card_div_le {D : ℕ} (hD : 48 ≤ D) {B : Block} (hpq2D : 2 * D ≤ B.p * B.q) :
    ((badRes D B).card : ℝ) / ((B.p * B.q : ℕ) : ℝ) ≤ 3 / (D : ℝ) := by
  set pq := B.p * B.q
  set K := (pq - 1) / D
  have hcard : (badRes D B).card ≤ 2 * K + 1 := by
    calc
      (badRes D B).card ≤ (Finset.Icc (-(K : ℤ)) (K : ℤ)).card := Finset.card_image_le
      _ = 2 * K + 1 := by
        rw [Int.card_Icc]
        omega
  have hKD : K * D ≤ pq - 1 := Nat.div_mul_le_self (pq - 1) D
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hpq_pos : (0 : ℝ) < (pq : ℝ) := by exact_mod_cast (by omega : 0 < pq)
  rw [div_le_div_iff₀ hpq_pos hD_pos]
  have hnat : (badRes D B).card * D ≤ 3 * pq := by
    calc
      (badRes D B).card * D ≤ (2 * K + 1) * D := Nat.mul_le_mul_right D hcard
      _ = 2 * (K * D) + D := by ring
      _ ≤ 2 * (pq - 1) + D := by omega
      _ ≤ 3 * pq := by omega
  exact_mod_cast hnat

private lemma new_block_sep {D ℓ : ℕ} {B : Block} (hBD : B.D = D)
    (hnotbad : ℓ % (B.p * B.q) ∉ badRes D B) (n k : ℕ) :
    (1 : ℝ) < |(k : ℝ) * B.pt n - ((D * ℓ : ℕ) : ℝ)| := by
  set pq := B.p * B.q
  have hpq : 6 ≤ pq := B.pq_ge6
  have hden_pos : (0 : ℝ) < ((pq - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < pq - 1)
  set z : ℤ := (pq : ℤ) * ((k * n : ℕ) : ℤ) - ((pq - 1 : ℕ) : ℤ) * (ℓ : ℤ)
  have hmod : z % (pq : ℤ) = ((ℓ % pq : ℕ) : ℤ) := by
    have hcast : ((pq - 1 : ℕ) : ℤ) = (pq : ℤ) - 1 := by
      rw [Int.ofNat_sub (by omega : 1 ≤ pq)]
      rfl
    have hz : z = (ℓ : ℤ) + (pq : ℤ) * (((k * n : ℕ) : ℤ) - (ℓ : ℤ)) := by
      dsimp only [z]
      rw [hcast]
      ring
    rw [hz, Int.add_mul_emod_self_left]
    exact_mod_cast rfl
  have hz_big : ((pq - 1 : ℕ) : ℝ) < (D : ℝ) * |(z : ℝ)| := by
    by_contra hle
    push Not at hle
    have hnat : D * z.natAbs ≤ pq - 1 := by
      have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [habs] at hle
      exact_mod_cast hle
    have hK : z.natAbs ≤ (pq - 1) / D :=
      (Nat.le_div_iff_mul_le (by have := B.hD; omega)).mpr (by rw [mul_comm]; exact hnat)
    have hzIcc : z ∈ Finset.Icc (-(((pq - 1) / D : ℕ) : ℤ)) (((pq - 1) / D : ℕ) : ℤ) := by
      rw [Finset.mem_Icc]
      have h1 : -(z.natAbs : ℤ) ≤ z := neg_le_of_abs_le (by rw [Int.abs_eq_natAbs])
      have h2 : z ≤ (z.natAbs : ℤ) := le_of_abs_le (by rw [Int.abs_eq_natAbs])
      omega
    have hmem : ℓ % pq ∈ badRes D B := by
      unfold badRes
      refine Finset.mem_image.mpr ⟨z, hzIcc, ?_⟩
      rw [hmod]
      exact Int.toNat_natCast (ℓ % pq)
    exact hnotbad hmem
  have hfactor : (k : ℝ) * B.pt n - ((D * ℓ : ℕ) : ℝ) =
      ((D : ℝ) * (z : ℝ)) / ((pq - 1 : ℕ) : ℝ) := by
    unfold Block.pt
    rw [hBD]
    have hzcast : (z : ℝ) = (pq : ℝ) * ((k * n : ℕ) : ℝ) - ((pq - 1 : ℕ) : ℝ) * (ℓ : ℝ) := by
      dsimp only [z]
      push_cast
      ring
    rw [hzcast]
    dsimp only [pq] at hden_pos ⊢
    push_cast
    field_simp
  rw [hfactor, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), abs_of_pos hden_pos]
  exact (one_lt_div hden_pos).mpr hz_big

private lemma lattice_upgrade {a : ℝ} {A B : ℕ} (hB : 0 < B) (ha : a = (A : ℝ) / (B : ℝ))
    {M k : ℕ} (hgt : (1 : ℝ) < |(k : ℝ) * a - (M : ℝ)|) :
    (1 : ℝ) + 1 / (B : ℝ) ≤ |(k : ℝ) * a - (M : ℝ)| := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  set z : ℤ := (k : ℤ) * (A : ℤ) - (B : ℤ) * (M : ℤ)
  have heq : (k : ℝ) * a - (M : ℝ) = (z : ℝ) / (B : ℝ) := by
    rw [ha]
    dsimp only [z]
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_pos hB_pos] at hgt ⊢
  have h1 : (B : ℝ) < |(z : ℝ)| := (one_lt_div hB_pos).mp hgt
  have h2 : (B : ℤ) < |z| := by exact_mod_cast h1
  have h3 : (B : ℤ) + 1 ≤ |z| := by omega
  have h4 : (B : ℝ) + 1 ≤ |(z : ℝ)| := by exact_mod_cast h3
  rw [show (1 : ℝ) + 1 / (B : ℝ) = ((B : ℝ) + 1) / (B : ℝ) by field_simp]
  exact div_le_div_of_nonneg_right h4 (le_of_lt hB_pos)

private lemma le_foldr_max {a : ℕ} : ∀ {L : List ℕ} {init : ℕ}, a ∈ L → a ≤ L.foldr max init
  | [], _, h => by simp at h
  | _ :: _, _, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max h') (le_max_right _ _)

private lemma init_le_foldr_max : ∀ (L : List ℕ) (init : ℕ), init ≤ L.foldr max init
  | [], _ => le_rfl
  | _ :: xs, init => le_trans (init_le_foldr_max xs init) (le_max_right _ _)

private lemma one_block_step {bs₀ added : List Block} {D : ℕ}
    (hD48 : 48 ≤ D)
    (hD_old : ∀ B ∈ bs₀, ∀ n ∈ B.P, B.q * B.D * n ∣ D)
    (hadm : Admissible (added ++ bs₀))
    (hadded_D : ∀ B ∈ added, B.D = D ∧ 2 * D ≤ B.p * B.q)
    (hndvdD : ∀ B ∈ added ++ bs₀, ¬ (B.p ∣ D))
    (hs_bound : added.length < D / 12) :
    ∃ Bnew : Block,
      Bnew.D = D ∧
      2 * D ≤ Bnew.p * Bnew.q ∧
      ¬ (Bnew.p ∣ D) ∧
      Admissible (Bnew :: (added ++ bs₀)) ∧
      Disjoint Bnew.pts (ptsOf (added ++ bs₀)) ∧
      (1 : ℝ) / (192 * (D : ℝ)) < W Bnew.pts := by
  set cur := added ++ bs₀
  have hpsum_lt : (cur.map (fun B => (1 : ℝ) / (B.p : ℝ))).sum < 1 / 100 := hadm.psum
  set rem : ℝ := 1 / 100 - (cur.map (fun B => (1 : ℝ) / (B.p : ℝ))).sum
  have hrem_pos : 0 < rem := by dsimp only [rem]; linarith
  -- Upper bound on all primes and stored integers in cur
  set maxP : ℕ := (cur.map Block.p).foldr max 0
  set maxStored : ℕ :=
    (cur.map (fun B => B.P.sup (fun n => B.q * B.D * n))).foldr max 0
  set pMin : ℕ := max (max D maxP) (max maxStored (Nat.ceil (1 / rem))) + 2
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes pMin
  have hp_gt_D : D < p := by
    have : D ≤ max D maxP := le_max_left _ _
    have : max D maxP ≤ pMin - 2 := le_max_left _ _
    omega
  have hp2 : 2 < p := by omega
  have hp_gt_all : ∀ B ∈ cur, B.p < p := by
    intro B hB
    have hle : B.p ≤ maxP := le_foldr_max (List.mem_map_of_mem hB)
    have : maxP ≤ max D maxP := le_max_right _ _
    have : max D maxP ≤ pMin - 2 := le_max_left _ _
    omega
  have hp_gt_stored : ∀ B ∈ cur, ∀ n ∈ B.P, B.q * B.D * n < p := by
    intro B hB n hn
    have hle1 : B.q * B.D * n ≤ B.P.sup (fun n => B.q * B.D * n) :=
      Finset.le_sup (f := fun n => B.q * B.D * n) hn
    have hle2 : B.P.sup (fun n => B.q * B.D * n) ≤ maxStored :=
      le_foldr_max (List.mem_map_of_mem (f := fun B => B.P.sup (fun n => B.q * B.D * n)) hB)
    have : maxStored ≤ max maxStored (Nat.ceil (1 / rem)) := le_max_left _ _
    have : max maxStored (Nat.ceil (1 / rem)) ≤ pMin - 2 := le_max_right _ _
    omega
  have hp_inv_lt : (1 : ℝ) / (p : ℝ) < rem := by
    have h1 : 1 / rem ≤ (Nat.ceil (1 / rem) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (1 / rem) < p := by
      have : Nat.ceil (1 / rem) ≤ max maxStored (Nat.ceil (1 / rem)) := le_max_right _ _
      have : max maxStored (Nat.ceil (1 / rem)) ≤ pMin - 2 := le_max_right _ _
      omega
    have h3 : (1 / rem) < (p : ℝ) := lt_of_le_of_lt h1 (by exact_mod_cast h2)
    rw [div_lt_iff₀ (by exact_mod_cast hp_prime.pos : (0 : ℝ) < (p : ℝ))]
    have h4 := (div_lt_iff₀ hrem_pos).mp h3
    linarith
  have hp_ndvd_D : ¬ (p ∣ D) := Nat.not_dvd_of_pos_of_lt (by omega) hp_gt_D
  -- Build periodic modulus M and good residue set Rgood
  set allPrimes : List ℕ := p :: cur.map Block.p
  set M : ℕ := allPrimes.prod * (added.map (fun B => B.p * B.q)).prod
  have hM_pos : 1 ≤ M := by
    have h1 : 0 < allPrimes.prod := by
      apply List.prod_pos
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hp_prime.pos
      · rcases List.mem_map.mp hx' with ⟨B, _, rfl⟩
        exact B.hp.pos
    have h2 : 0 < (added.map (fun B => B.p * B.q)).prod := by
      apply List.prod_pos
      intro x hx
      rcases List.mem_map.mp hx with ⟨B, _, rfl⟩
      have := B.pq_ge6
      omega
    exact Nat.mul_pos h1 h2
  have hp_dvd_M : ∀ p' ∈ allPrimes, p' ∣ M := fun p' hp' =>
    dvd_mul_of_dvd_left (List.dvd_prod hp') _
  have hpq_dvd_M : ∀ B ∈ added, B.p * B.q ∣ M := fun B hB =>
    dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map_of_mem hB)) _
  set Rgood : Finset ℕ := (Finset.range M).filter (fun r =>
    (∀ p' ∈ allPrimes, ¬ (p' ∣ r)) ∧
    (∀ B ∈ added, r % (B.p * B.q) ∉ badRes D B))
  have hRsub : Rgood ⊆ Finset.range M := Finset.filter_subset _ _
  -- Density lower bound on Rgood via union bound
  have hdens : (2 / 3 : ℝ) < (Rgood.card : ℝ) / (M : ℝ) := by
    have hbad_primes : ∀ L : List ℕ, (∀ p' ∈ L, 0 < p' ∧ p' ∣ M) →
        (((Finset.range M).filter (fun r => ∃ p' ∈ L, p' ∣ r)).card : ℝ) / (M : ℝ) ≤
          (L.map (fun (p' : ℕ) => (1 : ℝ) / (p' : ℝ))).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons q L ih =>
        have hq_pos : 0 < q := (hL q (List.mem_cons_self ..)).1
        have hq_dvd : q ∣ M := (hL q (List.mem_cons_self ..)).2
        have hsub_u : (Finset.range M).filter (fun r => ∃ p' ∈ q :: L, p' ∣ r) ⊆
            ((Finset.range M).filter (fun r => r % q ∈ ({0} : Finset ℕ))) ∪
              ((Finset.range M).filter (fun r => ∃ p' ∈ L, p' ∣ r)) := by
          intro r hr
          rcases Finset.mem_filter.mp hr with ⟨hrM, p', hp', hd⟩
          rcases List.mem_cons.mp hp' with rfl | hp'L
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hrM, Finset.mem_singleton.mpr (Nat.mod_eq_zero_of_dvd hd)⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrM, p', hp'L, hd⟩)
        have hcard_u :
            (((Finset.range M).filter (fun r => ∃ p' ∈ q :: L, p' ∣ r)).card : ℝ) ≤
              (((Finset.range M).filter (fun r => r % q ∈ ({0} : Finset ℕ))).card : ℝ) +
              (((Finset.range M).filter (fun r => ∃ p' ∈ L, p' ∣ r)).card : ℝ) := by
          exact_mod_cast le_trans (Finset.card_le_card hsub_u) (Finset.card_union_le _ _)
        have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
        have hdiv_u := div_le_div_of_nonneg_right hcard_u (le_of_lt hM0)
        rw [add_div] at hdiv_u
        have hfirst := card_filter_mod_mem_div hM_pos hq_pos hq_dvd
          (S := {0}) (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; exact Finset.mem_range.mpr hq_pos)
        simp only [Finset.card_singleton, Nat.cast_one] at hfirst
        have hih := ih (fun p' hp' => hL p' (List.mem_cons_of_mem q hp'))
        rw [List.map_cons, List.sum_cons]
        linarith
    have hbad_blocks : ∀ L : List Block,
        (∀ B ∈ L, B.D = D ∧ 2 * D ≤ B.p * B.q ∧ B.p * B.q ∣ M) →
        (((Finset.range M).filter (fun r => ∃ B ∈ L, r % (B.p * B.q) ∈ badRes D B)).card : ℝ) / (M : ℝ) ≤
          (L.length : ℝ) * (3 / (D : ℝ)) := by
      intro L hL
      induction L with
      | nil => simp
      | cons B L ih =>
        have hB := hL B (List.mem_cons_self ..)
        have hsub_u : (Finset.range M).filter (fun r => ∃ B' ∈ B :: L, r % (B'.p * B'.q) ∈ badRes D B') ⊆
            ((Finset.range M).filter (fun r => r % (B.p * B.q) ∈ badRes D B)) ∪
              ((Finset.range M).filter (fun r => ∃ B' ∈ L, r % (B'.p * B'.q) ∈ badRes D B')) := by
          intro r hr
          rcases Finset.mem_filter.mp hr with ⟨hrM, B', hB', hmem⟩
          rcases List.mem_cons.mp hB' with rfl | hB'L
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrM, hmem⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrM, B', hB'L, hmem⟩)
        have hcard_u :
            (((Finset.range M).filter (fun r => ∃ B' ∈ B :: L, r % (B'.p * B'.q) ∈ badRes D B')).card : ℝ) ≤
              (((Finset.range M).filter (fun r => r % (B.p * B.q) ∈ badRes D B)).card : ℝ) +
              (((Finset.range M).filter (fun r => ∃ B' ∈ L, r % (B'.p * B'.q) ∈ badRes D B')).card : ℝ) := by
          exact_mod_cast le_trans (Finset.card_le_card hsub_u) (Finset.card_union_le _ _)
        have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
        have hdiv_u := div_le_div_of_nonneg_right hcard_u (le_of_lt hM0)
        rw [add_div] at hdiv_u
        have hfirst := card_filter_mod_mem_div hM_pos (by have := B.pq_ge6; omega) hB.2.2 (badRes_subset D B)
        have hle3 := badRes_card_div_le hD48 hB.2.1
        have hih := ih (fun B' hB' => hL B' (List.mem_cons_of_mem B hB'))
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
    have hcover : Finset.range M ⊆
        Rgood ∪
          ((Finset.range M).filter (fun r => ∃ p' ∈ allPrimes, p' ∣ r)) ∪
          ((Finset.range M).filter (fun r => ∃ B ∈ added, r % (B.p * B.q) ∈ badRes D B)) := by
      intro r hr
      by_cases h1 : ∀ p' ∈ allPrimes, ¬ (p' ∣ r)
      · by_cases h2 : ∀ B ∈ added, r % (B.p * B.q) ∉ badRes D B
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, h1, h2⟩))
        · push Not at h2
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, h2⟩)
      · push Not at h1
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, h1⟩))
    have hcard_cov : (M : ℝ) ≤
        (Rgood.card : ℝ) +
        (((Finset.range M).filter (fun r => ∃ p' ∈ allPrimes, p' ∣ r)).card : ℝ) +
        (((Finset.range M).filter (fun r => ∃ B ∈ added, r % (B.p * B.q) ∈ badRes D B)).card : ℝ) := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_union_le
        (Rgood ∪ (Finset.range M).filter (fun r => ∃ p' ∈ allPrimes, p' ∣ r))
        ((Finset.range M).filter (fun r => ∃ B ∈ added, r % (B.p * B.q) ∈ badRes D B))
      have h3 := Finset.card_union_le Rgood
        ((Finset.range M).filter (fun r => ∃ p' ∈ allPrimes, p' ∣ r))
      rw [Finset.card_range] at h1
      exact_mod_cast (by omega : M ≤ Rgood.card +
        ((Finset.range M).filter (fun r => ∃ p' ∈ allPrimes, p' ∣ r)).card +
        ((Finset.range M).filter (fun r => ∃ B ∈ added, r % (B.p * B.q) ∈ badRes D B)).card)
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    have hdiv_cov := div_le_div_of_nonneg_right hcard_cov (le_of_lt hM0)
    rw [div_self (ne_of_gt hM0), add_div, add_div] at hdiv_cov
    have hbp := hbad_primes allPrimes (fun p' hp' => by
      refine ⟨?_, hp_dvd_M p' hp'⟩
      rcases List.mem_cons.mp hp' with rfl | hp'c
      · exact hp_prime.pos
      · rcases List.mem_map.mp hp'c with ⟨B, _, rfl⟩
        exact B.hp.pos)
    have hpsum_new : (allPrimes.map (fun (p' : ℕ) => (1 : ℝ) / (p' : ℝ))).sum < 1 / 100 := by
      dsimp only [allPrimes]
      rw [List.map_cons, List.sum_cons, List.map_map]
      have heq : ((fun (p' : ℕ) => (1 : ℝ) / (p' : ℝ)) ∘ Block.p) = (fun B => (1 : ℝ) / (B.p : ℝ)) := rfl
      rw [heq]
      dsimp only [rem] at hp_inv_lt
      linarith
    have hbb := hbad_blocks added (fun B hB =>
      ⟨(hadded_D B hB).1, (hadded_D B hB).2, hpq_dvd_M B hB⟩)
    have hs_div : (added.length : ℝ) * (3 / (D : ℝ)) < 1 / 4 := by
      have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
      have h1 : 12 * added.length < D := by
        have := Nat.div_mul_le_self D 12
        omega
      have h2 : 12 * (added.length : ℝ) < (D : ℝ) := by exact_mod_cast h1
      have h3 : (added.length : ℝ) * (3 / (D : ℝ)) = (3 * (added.length : ℝ)) / (D : ℝ) := by ring
      rw [h3, div_lt_iff₀ hD_pos]
      linarith
    linarith
  -- Choose threshold N and apply Lemma 7
  set maxF : ℝ := if h : (ptsOf cur).Nonempty then (ptsOf cur).max' h else 0
  have hle_maxF : ∀ a ∈ ptsOf cur, a ≤ maxF := by
    intro a ha
    have hne : (ptsOf cur).Nonempty := ⟨a, ha⟩
    dsimp only [maxF]
    rw [dif_pos hne]
    exact Finset.le_max' _ a ha
  set N : ℕ := max (2 * D) (max (4 * p) (Nat.ceil (max 0 maxF) + 2)) + 2
  obtain ⟨P, hP_ne, hP_mem, hP_prim, hWP⟩ :=
    lemma7_primitive_selection hM_pos hRsub hdens N (by omega)
  have hP_ge2 : ∀ n ∈ P, 2 ≤ n := fun n hn => by have := (hP_mem n hn).1; omega
  have hP_ge2D : ∀ n ∈ P, 2 * D ≤ n := fun n hn => by
    have := (hP_mem n hn).1
    have : 2 * D ≤ max (2 * D) (max (4 * p) (Nat.ceil (max 0 maxF) + 2)) := le_max_left _ _
    omega
  have hP_gt_4p : ∀ n ∈ P, 4 * p < D * n := fun n hn => by
    have hnN := (hP_mem n hn).1
    have h1 : 4 * p ≤ max (4 * p) (Nat.ceil (max 0 maxF) + 2) := le_max_left _ _
    have h2 : max (4 * p) (Nat.ceil (max 0 maxF) + 2) ≤ N - 2 := le_max_right _ _
    have : 4 * p < n := by omega
    nlinarith
  have hP_gt_maxF : ∀ n ∈ P, maxF + 1 < ((D * n : ℕ) : ℝ) := fun n hn => by
    have hnN := (hP_mem n hn).1
    have h1 : Nat.ceil (max 0 maxF) + 2 ≤ max (4 * p) (Nat.ceil (max 0 maxF) + 2) := le_max_right _ _
    have h2 : max (4 * p) (Nat.ceil (max 0 maxF) + 2) ≤ N - 2 := le_max_right _ _
    have h3 : max 0 maxF ≤ (Nat.ceil (max 0 maxF) : ℝ) := Nat.le_ceil _
    have h4 : maxF ≤ max 0 maxF := le_max_right _ _
    have h5 : Nat.ceil (max 0 maxF) + 2 ≤ n := by omega
    have h6 : n ≤ D * n := Nat.le_mul_of_pos_left n (by omega)
    have h7 : ((Nat.ceil (max 0 maxF) + 2 : ℕ) : ℝ) ≤ ((D * n : ℕ) : ℝ) :=
      by exact_mod_cast le_trans h5 h6
    push_cast at h7 ⊢
    linarith
  -- Choose q coprime to all primes in allPrimes and huge enough
  set U : ℕ := D * P.sup id
  set maxDen : ℕ := (cur.map (fun B => B.p * B.q - 1)).foldr max 1
  have hden_le : ∀ B ∈ cur, B.p * B.q - 1 ≤ maxDen := fun B hB =>
    le_foldr_max (List.mem_map_of_mem (f := fun B => B.p * B.q - 1) hB)
  set Pprod : ℕ := allPrimes.prod
  have hPprod_pos : 1 ≤ Pprod := by
    apply Nat.succ_le_of_lt
    apply List.prod_pos
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hp_prime.pos
    · rcases List.mem_map.mp hx' with ⟨B, _, rfl⟩
      exact B.hp.pos
  set Kq : ℕ := max (2 * D) (U * maxDen + 2) + 1
  set q : ℕ := 1 + Kq * Pprod
  have hq2 : 2 ≤ q := by
    have : 1 ≤ Kq * Pprod := Nat.mul_pos (by omega) hPprod_pos
    omega
  have hq_ndvd : ∀ p' ∈ allPrimes, ¬ (p' ∣ q) := by
    intro p' hp' hd
    have hpr : p'.Prime := by
      rcases List.mem_cons.mp hp' with rfl | hp'c
      · exact hp_prime
      · rcases List.mem_map.mp hp'c with ⟨B, _, rfl⟩
        exact B.hp
    have hd2 : p' ∣ Kq * Pprod := dvd_mul_of_dvd_right (List.dvd_prod hp') Kq
    have hd1 : p' ∣ 1 := (Nat.dvd_add_left hd2).mp hd
    exact hpr.not_dvd_one hd1
  have hpq_ge2D : 2 * D ≤ p * q := by
    have h1 : 2 * D ≤ Kq := le_trans (le_max_left _ _) (Nat.le_succ _)
    have h2 : Kq ≤ q := by
      have : Kq ≤ Kq * Pprod := Nat.le_mul_of_pos_right Kq hPprod_pos
      omega
    nlinarith
  have hU_lt_den : U * maxDen < p * q - 1 := by
    have h1 : U * maxDen + 2 ≤ Kq := le_trans (le_max_right _ _) (Nat.le_succ _)
    have h2 : Kq ≤ q := by
      have : Kq ≤ Kq * Pprod := Nat.le_mul_of_pos_right Kq hPprod_pos
      omega
    have h3 : U * maxDen + 2 ≤ p * q := by nlinarith
    omega
  have hmaxDen_pos : 1 ≤ maxDen := init_le_foldr_max _ 1
  let Bnew : Block := {
    D := D
    p := p
    q := q
    P := P
    hD := hD48
    hp := hp_prime
    hp2 := hp2
    hq := hq2
    hP_ne := hP_ne
    hP_ge2 := hP_ge2
    hP_prim := hP_prim
  }
  have hBnew_pt_close : ∀ n ∈ P,
      Bnew.pt n - ((D * n : ℕ) : ℝ) < 1 / (maxDen : ℝ) ∧
      Bnew.pt n - ((D * n : ℕ) : ℝ) < 1 := by
    intro n hn
    have hDn_le_U : D * n ≤ U := Nat.mul_le_mul_left D (Finset.le_sup (f := id) hn)
    have hden_pos : (0 : ℝ) < ((p * q - 1 : ℕ) : ℝ) := by
      have := Bnew.pq_ge6
      exact_mod_cast (by omega : 0 < p * q - 1)
    have hdiff : Bnew.pt n - ((D * n : ℕ) : ℝ) = ((D * n : ℕ) : ℝ) / ((p * q - 1 : ℕ) : ℝ) := by
      dsimp only [Block.pt, Bnew]
      have hcast : ((p * q - 1 : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by have := Bnew.pq_ge6; omega)]
        push_cast
        rfl
      push_cast
      rw [hcast]
      have hne : (p : ℝ) * (q : ℝ) - 1 ≠ 0 := by rw [← hcast]; exact ne_of_gt hden_pos
      field_simp
      ring
    rw [hdiff]
    have h1 : ((D * n : ℕ) : ℝ) / ((p * q - 1 : ℕ) : ℝ) < 1 / (maxDen : ℝ) := by
      rw [div_lt_div_iff₀ hden_pos (by exact_mod_cast hmaxDen_pos : (0 : ℝ) < (maxDen : ℝ))]
      have hnat : (D * n) * maxDen < p * q - 1 :=
        lt_of_le_of_lt (Nat.mul_le_mul_right maxDen hDn_le_U) hU_lt_den
      have : ((D * n * maxDen : ℕ) : ℝ) < ((p * q - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this ⊢
      linarith
    have h2 : (1 : ℝ) / (maxDen : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hmaxDen_pos : (0 : ℝ) < (maxDen : ℝ))]
      exact_mod_cast hmaxDen_pos
    exact ⟨h1, lt_of_lt_of_le h1 h2⟩
  -- Prove admissibility of Bnew :: cur
  have hadm_new : Admissible (Bnew :: cur) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- Separation
      intro a ha b hb hab k hk
      rw [mem_ptsOf_iff] at ha hb
      rcases ha with ⟨Ba, hBa, haPts⟩
      rcases hb with ⟨Bb, hBb, hbPts⟩
      rcases List.mem_cons.mp hBa with rfl | hBa_cur <;>
      rcases List.mem_cons.mp hBb with rfl | hBb_cur
      · -- Both in Bnew
        rcases Finset.mem_image.mp haPts with ⟨m, hm, rfl⟩
        rcases Finset.mem_image.mp hbPts with ⟨n, hn, rfl⟩
        have hmn : m ≠ n := fun h => hab (h ▸ rfl)
        have hkmn : k * m ≠ n := by
          intro heq
          by_cases hk1 : k = 1
          · subst hk1; simp at heq; exact hmn heq
          · exact hP_prim m hm n hn hmn ⟨k, by rw [mul_comm]; exact heq.symm⟩
        have hdiff_ge1 : (1 : ℝ) ≤ |((k * m : ℕ) : ℝ) - (n : ℝ)| := by
          have h1 : (1 : ℤ) ≤ |(k * m : ℤ) - (n : ℤ)| :=
            Int.one_le_abs (by intro h0; apply hkmn; omega)
          exact_mod_cast h1
        have hden_pos : (0 : ℝ) < ((p * q - 1 : ℕ) : ℝ) := by
          have := Bnew.pq_ge6
          exact_mod_cast (by omega : 0 < p * q - 1)
        have hfactor : (k : ℝ) * Bnew.pt m - Bnew.pt n =
            (((D * p * q : ℕ) : ℝ) / ((p * q - 1 : ℕ) : ℝ)) * (((k * m : ℕ) : ℝ) - (n : ℝ)) := by
          dsimp only [Block.pt, Bnew]
          push_cast
          ring
        rw [hfactor, abs_mul]
        have hcoef_gt : (1 : ℝ) < ((D * p * q : ℕ) : ℝ) / ((p * q - 1 : ℕ) : ℝ) := by
          rw [one_lt_div hden_pos]
          have : p * q - 1 < D * p * q := by
            have h6 : 6 ≤ p * q := Bnew.pq_ge6
            have hle : p * q ≤ D * (p * q) := Nat.le_mul_of_pos_left (p * q) (by omega)
            rw [← mul_assoc] at hle
            omega
          exact_mod_cast this
        rw [abs_of_pos (by linarith : 0 < ((D * p * q : ℕ) : ℝ) / ((p * q - 1 : ℕ) : ℝ))]
        nlinarith
      · -- a in Bnew, b in cur
        rcases Finset.mem_image.mp haPts with ⟨m, hm, rfl⟩
        have hb_cur : b ∈ ptsOf cur := mem_ptsOf_iff.mpr ⟨Bb, hBb_cur, hbPts⟩
        have hb_le : b ≤ maxF := hle_maxF b hb_cur
        have ha_gt : maxF + 1 < Bnew.pt m :=
          lt_trans (hP_gt_maxF m hm) (Bnew.pt_gt_Dn (n := m) (by have := hP_ge2 m hm; omega))
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have ha_pos : (0 : ℝ) < Bnew.pt m := by linarith [Bnew.pt_gt_two hm]
        have hsub : (1 : ℝ) < (k : ℝ) * Bnew.pt m - b := by nlinarith
        exact lt_of_lt_of_le hsub (le_abs_self _)
      · -- a in cur, b in Bnew
        rcases Finset.mem_image.mp haPts with ⟨m, hm, rfl⟩
        rcases Finset.mem_image.mp hbPts with ⟨n, hn, rfl⟩
        have hnR : n % M ∈ Rgood := (hP_mem n hn).2
        rcases (Finset.mem_filter.mp hnR).2 with ⟨hndvd_n, hnotbad_n⟩
        have hgt1 : (1 : ℝ) < |(k : ℝ) * Ba.pt m - ((D * n : ℕ) : ℝ)| := by
          rcases List.mem_append.mp hBa_cur with hBa_add | hBa_old
          · have hnotb : n % (Ba.p * Ba.q) ∉ badRes D Ba := by
              have := hnotbad_n Ba hBa_add
              rwa [Nat.mod_mod_of_dvd n (hpq_dvd_M Ba hBa_add)] at this
            exact new_block_sep (hadded_D Ba hBa_add).1 hnotb m k
          · have hndvd_p : ¬ (Ba.p ∣ n) := by
              have hp_in : Ba.p ∈ allPrimes :=
                List.mem_cons_of_mem p (List.mem_map_of_mem hBa_cur)
              have h1 := hndvd_n Ba.p hp_in
              intro hd
              exact h1 ((Nat.dvd_mod_iff (hp_dvd_M Ba.p hp_in)).mpr hd)
            have h4 := old_point_sep hm (hD_old Ba hBa_old m hm) (hndvdD Ba hBa_cur)
              hndvd_p (hadm.ratio Ba hBa_cur m hm) k
            linarith
        have hlat := lattice_upgrade (a := Ba.pt m) (A := Ba.D * m * Ba.p * Ba.q)
          (B := Ba.p * Ba.q - 1) (by have := Ba.pq_ge6; omega) rfl (M := D * n) (k := k) hgt1
        have hden_le' : ((Ba.p * Ba.q - 1 : ℕ) : ℝ) ≤ (maxDen : ℝ) :=
          by exact_mod_cast hden_le Ba hBa_cur
        have hinv_ge : 1 / (maxDen : ℝ) ≤ 1 / ((Ba.p * Ba.q - 1 : ℕ) : ℝ) :=
          one_div_le_one_div_of_le (by have := Ba.pq_ge6; exact_mod_cast (by omega : 0 < Ba.p * Ba.q - 1)) hden_le'
        have hclose := (hBnew_pt_close n hn).1
        have hpos_diff : 0 < Bnew.pt n - ((D * n : ℕ) : ℝ) := by
          have hgt := Bnew.pt_gt_Dn (n := n) (by have := hP_ge2 n hn; omega)
          dsimp only [Bnew] at hgt
          linarith
        have htri : |(k : ℝ) * Ba.pt m - ((D * n : ℕ) : ℝ)| -
            |Bnew.pt n - ((D * n : ℕ) : ℝ)| ≤ |(k : ℝ) * Ba.pt m - Bnew.pt n| := by
          have := abs_sub_abs_le_abs_sub ((k : ℝ) * Ba.pt m - ((D * n : ℕ) : ℝ))
            (Bnew.pt n - ((D * n : ℕ) : ℝ))
          have heq : ((k : ℝ) * Ba.pt m - ((D * n : ℕ) : ℝ)) -
              (Bnew.pt n - ((D * n : ℕ) : ℝ)) = (k : ℝ) * Ba.pt m - Bnew.pt n := by ring
          rw [heq] at this
          exact this
        rw [abs_of_pos hpos_diff] at htri
        linarith
      · -- Both in cur
        exact hadm.sep a (mem_ptsOf_iff.mpr ⟨Ba, hBa_cur, haPts⟩)
          b (mem_ptsOf_iff.mpr ⟨Bb, hBb_cur, hbPts⟩) hab k hk
    · -- nodup_p
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hadm.nodup_p⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨B, hB, hpB⟩
      have := hp_gt_all B hB
      dsimp only [Bnew] at hpB
      omega
    · -- ndvd
      intro B₁ hB₁ B₂ hB₂ n hn
      rcases List.mem_cons.mp hB₁ with rfl | hB₁_cur <;>
      rcases List.mem_cons.mp hB₂ with rfl | hB₂_cur
      · -- B₁ = Bnew, B₂ = Bnew
        have h1 : ¬ (p ∣ q) := hq_ndvd p (List.mem_cons_self ..)
        have h2 : ¬ (p ∣ D) := hp_ndvd_D
        have h3 : ¬ (p ∣ n) := by
          have hnR := (hP_mem n hn).2
          have hnd := (Finset.mem_filter.mp hnR).2.1 p (List.mem_cons_self ..)
          intro hd
          exact hnd ((Nat.dvd_mod_iff (hp_dvd_M p (List.mem_cons_self ..))).mpr hd)
        intro hd
        rcases hp_prime.dvd_mul.mp hd with hd1 | hdn
        · rcases hp_prime.dvd_mul.mp hd1 with hdq | hdD
          · exact h1 hdq
          · exact h2 hdD
        · exact h3 hdn
      · -- B₁ = Bnew, B₂ in cur
        have hp2_mem : B₂.p ∈ allPrimes :=
          List.mem_cons_of_mem p (List.mem_map_of_mem hB₂_cur)
        have h1 : ¬ (B₂.p ∣ q) := hq_ndvd B₂.p hp2_mem
        have h2 : ¬ (B₂.p ∣ D) := hndvdD B₂ hB₂_cur
        have h3 : ¬ (B₂.p ∣ n) := by
          have hnR := (hP_mem n hn).2
          have hnd := (Finset.mem_filter.mp hnR).2.1 B₂.p hp2_mem
          intro hd
          exact hnd ((Nat.dvd_mod_iff (hp_dvd_M B₂.p hp2_mem)).mpr hd)
        intro hd
        rcases B₂.hp.dvd_mul.mp hd with hd1 | hdn
        · rcases B₂.hp.dvd_mul.mp hd1 with hdq | hdD
          · exact h1 hdq
          · exact h2 hdD
        · exact h3 hdn
      · -- B₁ in cur, B₂ = Bnew
        have hlt := hp_gt_stored B₁ hB₁_cur n hn
        have hpos : 0 < B₁.q * B₁.D * n := by
          have := B₁.hq
          have := B₁.hD
          have := B₁.hP_ge2 n hn
          positivity
        exact Nat.not_dvd_of_pos_of_lt hpos hlt
      · -- Both in cur
        exact hadm.ndvd B₁ hB₁_cur B₂ hB₂_cur n hn
    · -- ratio
      intro B hB n hn
      rcases List.mem_cons.mp hB with rfl | hB_cur
      · have h1 : (4 : ℝ) * (p : ℝ) < ((D * n : ℕ) : ℝ) := by
          have := hP_gt_4p n hn
          exact_mod_cast this
        have h2 := Bnew.pt_gt_Dn (n := n) (by have := hP_ge2 n hn; omega)
        dsimp only [Bnew] at h2 ⊢
        linarith
      · exact hadm.ratio B hB_cur n hn
    · -- psum
      rw [List.map_cons, List.sum_cons]
      dsimp only [Bnew, rem] at hp_inv_lt ⊢
      linarith
  have hdisj : Disjoint Bnew.pts (ptsOf cur) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨n, hn, rfl⟩
    have h1 := hle_maxF _ hx2
    have h2 := lt_trans (hP_gt_maxF n hn) (Bnew.pt_gt_Dn (n := n) (by have := hP_ge2 n hn; omega))
    linarith
  have hW_new : (1 : ℝ) / (192 * (D : ℝ)) < W Bnew.pts := by
    unfold W Block.pts
    rw [Finset.sum_image (fun x _ y _ h => Bnew.pt_injective h)]
    have hterm : ∀ n ∈ P, w (n : ℝ) / (4 * (D : ℝ)) ≤ w (Bnew.pt n) := by
      intro n hn
      have hn2 := hP_ge2 n hn
      have hn2D := hP_ge2D n hn
      have hclose := (hBnew_pt_close n hn).2
      have hDn_pos : (0 : ℝ) < ((D * n : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : 0 < D * n)
      have ha_lt_2Dn : Bnew.pt n < 2 * ((D * n : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((D * n : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : 1 ≤ D * n)
        linarith
      have h2Dn_le_n2 : 2 * ((D * n : ℕ) : ℝ) ≤ ((n : ℝ) ^ 2) := by
        have : 2 * (D * n) ≤ n * n := by nlinarith
        have h' : ((2 * (D * n) : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        rw [Nat.cast_mul, sq]
        linarith
      have ha_pos : 0 < Bnew.pt n := by linarith [Bnew.pt_gt_two hn]
      have ha_gt1 : 1 < Bnew.pt n := by linarith [Bnew.pt_gt_two hn]
      have hlog_le : Real.log (Bnew.pt n) ≤ 2 * Real.log (n : ℝ) := by
        calc
          Real.log (Bnew.pt n) ≤ Real.log ((n : ℝ) ^ 2) :=
            Real.log_le_log ha_pos (le_trans (le_of_lt ha_lt_2Dn) h2Dn_le_n2)
          _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
      have hprod : Bnew.pt n * Real.log (Bnew.pt n) ≤ 4 * (D : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
        have hlog_pos : 0 < Real.log (Bnew.pt n) := Real.log_pos ha_gt1
        have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have h1 : Bnew.pt n * Real.log (Bnew.pt n) ≤ (2 * ((D * n : ℕ) : ℝ)) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul (le_of_lt ha_lt_2Dn) hlog_le (le_of_lt hlog_pos) (by positivity)
        push_cast at h1
        linarith
      unfold w
      have hrew : 1 / ((n : ℝ) * Real.log (n : ℝ)) / (4 * (D : ℝ)) =
          1 / (4 * (D : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) := by ring
      rw [hrew]
      exact one_div_le_one_div_of_le (mul_pos ha_pos (Real.log_pos ha_gt1)) hprod
    have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    calc
      (1 : ℝ) / (192 * (D : ℝ)) = (1 / 48 : ℝ) / (4 * (D : ℝ)) := by ring
      _ < Wnat P / (4 * (D : ℝ)) := div_lt_div_of_pos_right hWP (by positivity)
      _ = ∑ n ∈ P, w (n : ℝ) / (4 * (D : ℝ)) := by unfold Wnat; rw [Finset.sum_div]
      _ ≤ ∑ n ∈ P, w (Bnew.pt n) := Finset.sum_le_sum hterm
  exact ⟨Bnew, rfl, hpq_ge2D, hp_ndvd_D, hadm_new, hdisj, hW_new⟩

private lemma prime_dvd_list_prod {p : ℕ} (hp : p.Prime) :
    ∀ {L : List ℕ}, p ∣ L.prod → ∃ x ∈ L, p ∣ x
  | [], hd => absurd hd hp.not_dvd_one
  | x :: xs, hd => by
    rw [List.prod_cons] at hd
    rcases hp.dvd_mul.mp hd with hdx | hdxs
    · exact ⟨x, List.mem_cons_self .., hdx⟩
    · rcases prime_dvd_list_prod hp hdxs with ⟨y, hy, hdy⟩
      exact ⟨y, List.mem_cons_of_mem x hy, hdy⟩

private lemma lemma8_finite_extension {bs₀ : List Block} (hadm : Admissible bs₀) :
    ∃ bs' : List Block, Admissible bs' ∧
      ptsOf bs₀ ⊆ ptsOf bs' ∧
      (1 / 4608 : ℝ) < W (ptsOf bs' \ ptsOf bs₀) := by
  set D : ℕ := 64 * (bs₀.map (fun B => ∏ n ∈ B.P, (B.q * B.D * n))).prod
  have hD_pos : 1 ≤ (bs₀.map (fun B => ∏ n ∈ B.P, (B.q * B.D * n))).prod := by
    apply Nat.succ_le_of_lt
    apply List.prod_pos
    intro x hx
    rcases List.mem_map.mp hx with ⟨B, _, rfl⟩
    apply Finset.prod_pos
    intro n hn
    have := B.hq
    have := B.hD
    have := B.hP_ge2 n hn
    positivity
  have hD64 : 64 ≤ D := by dsimp only [D]; nlinarith
  have hD48 : 48 ≤ D := by omega
  have hD_old : ∀ B ∈ bs₀, ∀ n ∈ B.P, B.q * B.D * n ∣ D := by
    intro B hB n hn
    have h1 : B.q * B.D * n ∣ ∏ m ∈ B.P, (B.q * B.D * m) := Finset.dvd_prod_of_mem _ hn
    have h2 : (∏ m ∈ B.P, (B.q * B.D * m)) ∣
        (bs₀.map (fun B => ∏ m ∈ B.P, (B.q * B.D * m))).prod :=
      List.dvd_prod (List.mem_map_of_mem hB)
    exact dvd_mul_of_dvd_right (dvd_trans h1 h2) 64
  have hndvdD₀ : ∀ B ∈ bs₀, ¬ (B.p ∣ D) := by
    intro B hB hd
    rcases B.hp.dvd_mul.mp hd with hd64 | hdprod
    · have hd2 : B.p ∣ 2 := B.hp.dvd_of_dvd_pow (show B.p ∣ 2 ^ 6 by exact hd64)
      have := Nat.le_of_dvd (by norm_num) hd2
      have := B.hp2
      omega
    · have hlist : ∃ x ∈ bs₀.map (fun B' => ∏ n ∈ B'.P, (B'.q * B'.D * n)), B.p ∣ x :=
        prime_dvd_list_prod B.hp hdprod
      rcases hlist with ⟨_, hx, hdx⟩
      rcases List.mem_map.mp hx with ⟨B', hB', rfl⟩
      obtain ⟨n, hn, hdn⟩ := (B.hp.prime.dvd_finsetProd_iff (fun n => B'.q * B'.D * n)).mp hdx
      exact hadm.ndvd B' hB' B hB n hn hdn
  set J : ℕ := D / 12
  have hiter : ∀ s : ℕ, s ≤ J →
      ∃ added : List Block,
        added.length = s ∧
        Admissible (added ++ bs₀) ∧
        (∀ B ∈ added, B.D = D ∧ 2 * D ≤ B.p * B.q) ∧
        (∀ B ∈ added ++ bs₀, ¬ (B.p ∣ D)) ∧
        (s : ℝ) / (192 * (D : ℝ)) ≤ W (ptsOf (added ++ bs₀) \ ptsOf bs₀) := by
    intro s hs
    induction s with
    | zero =>
      refine ⟨[], rfl, hadm, by simp, hndvdD₀, ?_⟩
      simp [W]
    | succ s ih =>
      obtain ⟨added, hlen, hadm_s, haddD, hndvd_s, hW_s⟩ := ih (by omega)
      have hs_lt : added.length < D / 12 := by omega
      obtain ⟨Bnew, hBD, hBpq, hBnd, hadm_new, hdisj, hW_new⟩ :=
        one_block_step hD48 hD_old hadm_s haddD hndvd_s hs_lt
      refine ⟨Bnew :: added, by simp [hlen], hadm_new, ?_, ?_, ?_⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB'
        · exact ⟨hBD, hBpq⟩
        · exact haddD B hB'
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB'
        · exact hBnd
        · exact hndvd_s B hB'
      · have hpts_eq : ptsOf ((Bnew :: added) ++ bs₀) \ ptsOf bs₀ =
            Bnew.pts ∪ (ptsOf (added ++ bs₀) \ ptsOf bs₀) := by
          ext x
          simp only [List.cons_append, ptsOf, List.foldr_cons, Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hx1 | hx2, hxnot⟩
            · exact Or.inl hx1
            · exact Or.inr ⟨hx2, hxnot⟩
          · rintro (hx1 | ⟨hx2, hxnot⟩)
            · refine ⟨Or.inl hx1, fun hx0 => ?_⟩
              change x ∈ ptsOf bs₀ at hx0
              have hx_cur : x ∈ ptsOf (added ++ bs₀) := by
                rw [mem_ptsOf_iff] at hx0 ⊢
                rcases hx0 with ⟨B, hB, hxB⟩
                exact ⟨B, List.mem_append_right added hB, hxB⟩
              exact Finset.disjoint_left.mp hdisj hx1 hx_cur
            · exact ⟨Or.inr hx2, hxnot⟩
        have hdisj' : Disjoint Bnew.pts (ptsOf (added ++ bs₀) \ ptsOf bs₀) :=
          Disjoint.mono_right Finset.sdiff_subset hdisj
        rw [hpts_eq]
        unfold W
        rw [Finset.sum_union hdisj']
        have hsum_cast : ((s + 1 : ℕ) : ℝ) / (192 * (D : ℝ)) =
            1 / (192 * (D : ℝ)) + (s : ℝ) / (192 * (D : ℝ)) := by
          push_cast
          ring
        rw [hsum_cast]
        unfold W at hW_new hW_s
        linarith
  obtain ⟨added, _, hadm_J, _, _, hW_J⟩ := hiter J le_rfl
  have hsub : ptsOf bs₀ ⊆ ptsOf (added ++ bs₀) := by
    intro x hx
    rw [mem_ptsOf_iff] at hx ⊢
    rcases hx with ⟨B, hB, hxB⟩
    exact ⟨B, List.mem_append_right added hB, hxB⟩
  have hJ_gt : (1 / 4608 : ℝ) < (J : ℝ) / (192 * (D : ℝ)) := by
    have hD_pos' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    have hnat : D < 24 * J := by
      dsimp only [J]
      have := Nat.lt_div_mul_add (a := D) (b := 12) (by norm_num)
      omega
    have hreal : (D : ℝ) < 24 * (J : ℝ) := by exact_mod_cast hnat
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4608) (by positivity : (0 : ℝ) < 192 * (D : ℝ))]
    linarith
  exact ⟨added ++ bs₀, hadm_J, hsub, lt_of_lt_of_le hJ_gt hW_J⟩

/- ### Part 4: Infinite union and refutation -/

private noncomputable def chain : ℕ → { bs : List Block // Admissible bs }
  | 0 => ⟨[], admissible_nil⟩
  | n + 1 =>
    let prev := chain n
    let h := lemma8_finite_extension prev.2
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩

private lemma chain_sub (n : ℕ) : ptsOf (chain n).1 ⊆ ptsOf (chain (n + 1)).1 :=
  (Classical.choose_spec (lemma8_finite_extension (chain n).2)).2.1

private lemma chain_mono {m n : ℕ} (hmn : m ≤ n) :
    ptsOf (chain m).1 ⊆ ptsOf (chain n).1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact subset_trans (ih (Nat.le_add_right m k)) (chain_sub (m + k))

private lemma chain_weight (n : ℕ) : (n : ℝ) / 4608 ≤ W (ptsOf (chain n).1) := by
  induction n with
  | zero => simp [chain, ptsOf, W]
  | succ n ih =>
    have hspec := Classical.choose_spec (lemma8_finite_extension (chain n).2)
    have hsub : ptsOf (chain n).1 ⊆ ptsOf (chain (n + 1)).1 := hspec.2.1
    have hgain : (1 / 4608 : ℝ) < W (ptsOf (chain (n + 1)).1 \ ptsOf (chain n).1) := hspec.2.2
    have hsplit : ptsOf (chain (n + 1)).1 =
        (ptsOf (chain (n + 1)).1 \ ptsOf (chain n).1) ∪ ptsOf (chain n).1 :=
      (Finset.sdiff_union_of_subset hsub).symm
    have hdisj : Disjoint (ptsOf (chain (n + 1)).1 \ ptsOf (chain n).1) (ptsOf (chain n).1) :=
      Finset.sdiff_disjoint
    unfold W at ih hgain ⊢
    rw [hsplit, Finset.sum_union hdisj]
    push_cast
    linarith

private noncomputable def counterexampleA : Set ℝ :=
  ⋃ n : ℕ, (ptsOf (chain n).1 : Set ℝ)

private lemma counterexampleA_wellSeparated : Erdos143.WellSeparatedSet counterexampleA := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- A ⊆ Ioi 1
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
    rw [Finset.mem_coe, mem_ptsOf_iff] at hxn
    rcases hxn with ⟨B, _, hxB⟩
    rcases Finset.mem_image.mp hxB with ⟨m, hm, rfl⟩
    have := B.pt_gt_two hm
    exact Set.mem_Ioi.mpr (by linarith)
  · -- A.Infinite
    intro hfin
    obtain ⟨S, hS⟩ := hfin.exists_finset_coe
    have hle : ∀ n : ℕ, W (ptsOf (chain n).1) ≤ W S := by
      intro n
      have hsub : ptsOf (chain n).1 ⊆ S := by
        intro x hx
        have : x ∈ counterexampleA := Set.mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr hx⟩
        rwa [← hS, Finset.mem_coe] at this
      unfold W
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => ?_)
      have hxA : x ∈ counterexampleA := by rwa [← hS, Finset.mem_coe]
      rcases Set.mem_iUnion.mp hxA with ⟨m, hxm⟩
      rw [Finset.mem_coe, mem_ptsOf_iff] at hxm
      rcases hxm with ⟨B, _, hxB⟩
      rcases Finset.mem_image.mp hxB with ⟨r, hr, rfl⟩
      exact le_of_lt (w_pos (by linarith [B.pt_gt_two hr]))
    set N : ℕ := Nat.ceil (4608 * max 0 (W S)) + 1
    have h1 := chain_weight N
    have h2 := hle N
    have h3 : 4608 * max 0 (W S) ≤ (Nat.ceil (4608 * max 0 (W S)) : ℝ) := Nat.le_ceil _
    have h4 : W S ≤ max 0 (W S) := le_max_right _ _
    have h5 : ((Nat.ceil (4608 * max 0 (W S)) : ℝ) + 1) / 4608 ≤ W S := by
      have : (N : ℝ) = (Nat.ceil (4608 * max 0 (W S)) : ℝ) + 1 := by
        dsimp only [N]; push_cast; ring
      linarith
    linarith
  · -- A.Countable
    exact Set.countable_iUnion (fun n => (ptsOf (chain n).1).countable_toSet)
  · -- Separation
    intro x hx y hy hxy k hk
    rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
    rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
    set r := max m n
    have hxr : x ∈ ptsOf (chain r).1 := chain_mono (le_max_left m n) (Finset.mem_coe.mp hxm)
    have hyr : y ∈ ptsOf (chain r).1 := chain_mono (le_max_right m n) (Finset.mem_coe.mp hyn)
    exact le_of_lt ((chain r).2.sep x hxr y hyr hxy k hk)

private lemma counterexampleA_not_summable :
    ¬ Summable (fun x : counterexampleA => 1 / ((x : ℝ) * Real.log (x : ℝ))) := by
  intro hsum
  set T : ℝ := ∑' x : counterexampleA, 1 / ((x : ℝ) * Real.log (x : ℝ))
  have hnonneg : ∀ x : counterexampleA, 0 ≤ 1 / ((x : ℝ) * Real.log (x : ℝ)) := by
    intro ⟨x, hx⟩
    exact le_of_lt (w_pos (counterexampleA_wellSeparated.1 hx))
  set N : ℕ := Nat.ceil (4608 * max 0 T) + 1
  let emb : ptsOf (chain N).1 → counterexampleA := fun x =>
    ⟨x.1, Set.mem_iUnion.mpr ⟨N, Finset.mem_coe.mpr x.2⟩⟩
  have hemb_inj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : counterexampleA → ℝ) h)
  let S : Finset counterexampleA := (ptsOf (chain N).1).attach.image emb
  have hsum_eq : ∑ x ∈ S, (1 / ((x : ℝ) * Real.log (x : ℝ))) = W (ptsOf (chain N).1) := by
    rw [Finset.sum_image (fun a _ b _ h => hemb_inj h)]
    unfold W w
    exact Finset.sum_attach (ptsOf (chain N).1) (fun x => 1 / (x * Real.log x))
  have hle_T : W (ptsOf (chain N).1) ≤ T := by
    rw [← hsum_eq]
    exact hsum.sum_le_tsum S (fun x _ => hnonneg x)
  have h1 := chain_weight N
  have h3 : 4608 * max 0 T ≤ (Nat.ceil (4608 * max 0 T) : ℝ) := Nat.le_ceil _
  have h4 : T ≤ max 0 T := le_max_right _ _
  have h5 : (N : ℝ) = (Nat.ceil (4608 * max 0 T) : ℝ) + 1 := by
    dsimp only [N]; push_cast; ring
  linarith

end OMA.Erdos143Disproof

theorem OMA.disproof : ¬ (type_of% @Erdos143.erdos_143.parts.ii) := by
  intro h
  exact OMA.Erdos143Disproof.counterexampleA_not_summable
    (h OMA.Erdos143Disproof.counterexampleA OMA.Erdos143Disproof.counterexampleA_wellSeparated)
