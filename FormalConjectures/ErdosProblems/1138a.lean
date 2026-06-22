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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.ErdosProblems.«1138»

/-!
# Erdős Problem 1138 — disproof

A negative answer to [Erdős Problem 1138](https://www.erdosproblems.com/1138): the uniform
prime-gap asymptotic `A(C)` cannot hold simultaneously for two nearby constants (Theorem 1.2),
hence cannot hold for every `C > 1` (Corollary 3.1). The argument constructs counterexample
points from strict record prime gaps.

This reuses the definitions of `Erdos1138` (`sup_primeGap`, `snd_gt_half_fst`,
`primeCount_Ioc_mul_const`); `AsymptoticA C` is the per-`C` clause of `Erdos1138.erdos_1138`.

*References:*
- [erdosproblems.com/1138](https://www.erdosproblems.com/1138)
- *An Elementary Obstruction to a Uniform Prime-Gap Asymptotic*, by *Hrishi Sunder, Sourish
  Kumrawat and Kireet Cheri* (2026).
-/

open Nat Set Filter Asymptotics Erdos1138

set_option maxHeartbeats 400000

namespace Erdos1138a

noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable def realPi (t : ℝ) : ℕ := Nat.primeCounting ⌊t⌋₊
def IsStrictRecordGap (n : ℕ) : Prop := ∀ m : ℕ, m < n → primeGap m < primeGap n

def AsymptoticA (C : ℝ) : Prop :=
  primeCount_Ioc_mul_const C ~[snd_gt_half_fst] (fun (x, y) ↦ (C * (sup_primeGap x) / Real.log y))

@[category API, AMS 11]
lemma primes_infinite : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime

@[category API, AMS 11]
lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite primes_infinite n

@[category API, AMS 11]
lemma nthPrime_strictMono : StrictMono nthPrime := Nat.nth_strictMono primes_infinite

@[category API, AMS 11]
lemma nthPrime_ge_two (n : ℕ) : 2 ≤ nthPrime n := Nat.Prime.two_le (nthPrime_prime n)

@[category API, AMS 11]
lemma primeGap_pos (n : ℕ) : 0 < primeGap n :=
  Nat.sub_pos_of_lt (nthPrime_strictMono n.lt_succ_self)

@[category API, AMS 11]
lemma nthPrime_succ_eq (n : ℕ) : nthPrime (n + 1) = nthPrime n + primeGap n :=
  Eq.symm (Nat.add_sub_of_le (nthPrime_strictMono.monotone (Nat.le_succ _)))

@[category API, AMS 11]
lemma not_prime_between_consecutive (n : ℕ) (k : ℕ)
    (hlo : nthPrime n < k) (hhi : k < nthPrime (n + 1)) : ¬Nat.Prime k := by
  have h_prime_nth : ∀ m, Nat.nth Nat.Prime n < m → m < Nat.nth Nat.Prime (n + 1) →
      ¬Nat.Prime m := by
    intro m hm₁ hm₂
    contrapose! hm₂
    rw [Nat.nth_eq_sInf]
    exact Nat.sInf_le ⟨hm₂, fun j hj => lt_of_le_of_lt
      (Nat.nth_monotone Nat.infinite_setOf_prime (by omega)) hm₁⟩
  exact h_prime_nth k hlo hhi

@[category API, AMS 11]
lemma primeCounting'_eq_succ_of_between {n : ℕ} {m : ℕ}
    (hlo : nthPrime n < m) (hhi : m ≤ nthPrime (n + 1)) :
    Nat.primeCounting' m = n + 1 := by
  apply le_antisymm
  · contrapose! hhi
    exact Nat.nth_lt_of_lt_count hhi
  · rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
    refine le_trans ?_ (Finset.card_mono <| show Finset.image (fun k => Nat.nth Nat.Prime k)
      (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range m) from ?_)
    · rw [Finset.card_image_of_injective _ fun a b h =>
        Nat.nth_injective Nat.infinite_setOf_prime h]
      simp
    · refine Finset.image_subset_iff.mpr fun k hk => Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr <| lt_of_le_of_lt
          (Nat.nth_monotone Nat.infinite_setOf_prime <| Finset.mem_range_succ_iff.mp hk) hlo,
         nthPrime_prime k⟩

@[category API, AMS 11]
lemma realPi_eq_of_in_gap {n : ℕ} {s t : ℝ}
    (hlos : (nthPrime n : ℝ) ≤ s) (hhis : s < (nthPrime (n + 1) : ℝ))
    (hlot : (nthPrime n : ℝ) ≤ t) (hhit : t < (nthPrime (n + 1) : ℝ)) :
    realPi s = realPi t := by
  have h_primeCounting_eq : ∀ k : ℕ, nthPrime n ≤ k → k < nthPrime (n + 1) →
      Nat.primeCounting k = Nat.primeCounting (nthPrime n) := by
    intro k hk₁ hk₂
    simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx_lt, hx_prime⟩
      refine ⟨?_, hx_prime⟩
      by_contra h
      push_neg at h
      exact not_prime_between_consecutive n x (by omega) (by omega) hx_prime
    · rintro ⟨hx_lt, hx_prime⟩
      exact ⟨by omega, hx_prime⟩
  unfold realPi
  have hs : (nthPrime n) ≤ ⌊s⌋₊ := Nat.le_floor hlos
  have ht : (nthPrime n) ≤ ⌊t⌋₊ := Nat.le_floor hlot
  have hs' : ⌊s⌋₊ < nthPrime (n + 1) := by
    have hsnn : (0 : ℝ) ≤ s := le_trans (Nat.cast_nonneg _) hlos
    have := (Nat.floor_lt hsnn).2 hhis
    exact_mod_cast this
  have ht' : ⌊t⌋₊ < nthPrime (n + 1) := by
    have htnn : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg _) hlot
    have := (Nat.floor_lt htnn).2 hhit
    exact_mod_cast this
  rw [h_primeCounting_eq _ hs hs', h_primeCounting_eq _ ht ht']

@[category API, AMS 11]
lemma finset_sup_range_record {n : ℕ} (hrec : IsStrictRecordGap n) :
    Finset.sup (Finset.range (n + 1)) primeGap = primeGap n :=
  le_antisymm
    (Finset.sup_le fun x hx => if h : x = n then h.symm ▸ le_rfl
      else le_of_lt (hrec x (Nat.lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hx) h)))
    (Finset.le_sup (f := primeGap) (Finset.mem_range.mpr (Nat.lt_succ_self n)))

@[category API, AMS 11]
lemma sup_primeGap_eq_at_record {n : ℕ} (hrec : IsStrictRecordGap n)
    {x : ℝ} (hlo : (nthPrime n : ℝ) < x) (hhi : x < (nthPrime (n + 1) : ℝ)) :
    sup_primeGap x = primeGap n := by
  rw [sup_primeGap]
  rw [primeCounting'_eq_succ_of_between (n := n) (m := ⌈x⌉₊)]
  · exact finset_sup_range_record hrec
  · exact Nat.lt_ceil.mpr hlo
  · exact Nat.ceil_le.mpr hhi.le

@[category API, AMS 11]
lemma primeGap_unbounded (M : ℕ) : ∃ n : ℕ, M ≤ primeGap n := by
  -- The set of primes ≤ (M+1)! + 1 is a nonempty finite set; take its max `p`.
  set S : Finset ℕ := Finset.filter Nat.Prime (Finset.Iic ((M + 1)! + 1)) with hS
  have h2mem : (2 : ℕ) ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨by linarith [Nat.self_le_factorial (M + 1)], Nat.prime_two⟩
  have hSne : S.Nonempty := ⟨2, h2mem⟩
  set p := S.max' hSne with hp_def
  have hp_mem : p ∈ S := Finset.max'_mem S hSne
  have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp_mem).2
  have hp_le : p ≤ (M + 1)! + 1 := Finset.mem_Iic.mp (Finset.mem_filter.mp hp_mem).1
  have hp_max : ∀ q, Nat.Prime q → q ≤ (M + 1)! + 1 → q ≤ p := by
    intro q hq hq'
    refine Finset.le_max' S q ?_
    rw [hS, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨hq', hq⟩
  obtain ⟨n, hn⟩ : ∃ n, nthPrime n = p := ⟨Nat.count Nat.Prime p, Nat.nth_count hp_prime⟩
  -- The next prime after p is at least (M+1)! + (M+2), since (M+1)!+2 … (M+1)!+(M+1) are composite.
  have h_next_prime : ∀ q, Nat.Prime q → q > p → q ≥ (M + 1)! + (M + 2) := by
    intro q hq hq_gt_p
    by_contra h_contra
    push_neg at h_contra
    -- Any prime > p must exceed (M+1)!+1, since p is the largest prime ≤ (M+1)!+1.
    have hqlo : (M + 1)! + 1 < q := by
      by_contra hle
      push_neg at hle
      exact absurd (hp_max q hq hle) (by omega)
    obtain ⟨k, hk2, hkM, hqk⟩ : ∃ k, 2 ≤ k ∧ k ≤ M + 1 ∧ q = (M + 1)! + k :=
      ⟨q - (M + 1)!, by omega⟩
    have hdvd : k ∣ q :=
      hqk ▸ Nat.dvd_add (Nat.dvd_factorial (by omega) (by omega)) (dvd_refl k)
    have hfac_pos : 0 < (M + 1)! := Nat.factorial_pos _
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq k hdvd) with h | h
    · omega
    · -- k = q = (M+1)! + k forces (M+1)! = 0, impossible
      omega
  have h_gap : nthPrime (n + 1) ≥ (M + 1)! + (M + 2) := by
    apply h_next_prime
    · exact nthPrime_prime _
    · have := nthPrime_strictMono (Nat.lt_succ_self n)
      rw [hn] at this
      exact this
  refine ⟨n, ?_⟩
  have hgap : primeGap n = nthPrime (n + 1) - nthPrime n := rfl
  omega

@[category API, AMS 11]
lemma exists_record_gap_ge (N : ℕ) : ∃ n ≥ N, IsStrictRecordGap n := by
  -- Let `M` be the largest gap among indices `< N`.
  set M : ℕ := (Finset.range N).sup primeGap with hM
  -- Gaps are unbounded, so there is some index with gap > M; take the least such index.
  have hExists : ∃ n, M < primeGap n := by
    obtain ⟨m, hm⟩ := primeGap_unbounded (M + 1)
    exact ⟨m, by omega⟩
  classical
  set n := Nat.find hExists with hn_def
  have hn_spec : M < primeGap n := Nat.find_spec hExists
  have hn_min : ∀ k, k < n → ¬(M < primeGap k) := fun k hk => Nat.find_min hExists hk
  -- Any index `< N` has gap ≤ M, hence n ≥ N.
  have h_sup_le : ∀ m, m < N → primeGap m ≤ M := fun m hm =>
    hM ▸ Finset.le_sup (f := primeGap) (Finset.mem_range.mpr hm)
  have hnN : N ≤ n := by
    by_contra h
    push_neg at h
    exact absurd hn_spec (not_lt.mpr (h_sup_le n h))
  refine ⟨n, hnN, ?_⟩
  intro m hm
  -- Either m < N (gap ≤ M < primeGap n) or N ≤ m < n (minimality gives gap ≤ M).
  rcases lt_or_ge m N with hmN | hmN
  · exact lt_of_le_of_lt (h_sup_le m hmN) hn_spec
  · have := hn_min m hm
    push_neg at this
    exact lt_of_le_of_lt this hn_spec

@[category API, AMS 11]
lemma record_gap_arbitrarily_large (B : ℕ) :
    ∃ n, IsStrictRecordGap n ∧ 0 < n ∧ B ≤ nthPrime n := by
  -- nthPrime is increasing with nthPrime m ≥ m for every m.
  have h_n_le : ∀ m, m ≤ nthPrime m := by
    intro m
    induction m with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (nthPrime_strictMono (Nat.lt_succ_self k)))
  obtain ⟨n, hn_ge, hn_rec⟩ := exists_record_gap_ge (max B 1)
  refine ⟨n, hn_rec, lt_of_lt_of_le (by omega) hn_ge, ?_⟩
  have hnB : B ≤ n := le_trans (le_max_left _ _) hn_ge
  exact le_trans hnB (h_n_le n)

@[category API, AMS 11]
private lemma rho_lt_bound {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hlt : C₁ < C₂) :
    let ε := (C₂ - C₁) / (2 * (C₂ + C₁))
    C₁ / C₂ < (1 - ε) / (1 + ε) := by
  rw [div_lt_div_iff₀]
  · nlinarith [mul_div_cancel₀ (C₂ - C₁) (by linarith : (2 * (C₂ + C₁)) ≠ 0)]
  · grind
  · rw [add_div', lt_div_iff₀] <;> linarith

@[category API, AMS 11]
private lemma ratio_bound {a b ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (ha : 1 - ε < a) (hb : b < 1 + ε) (hb_pos : 0 < b) :
    (1 - ε) / (1 + ε) < a / b := by
  rw [div_lt_div_iff₀] <;> nlinarith

/-- The arithmetic core of the disproof. Given the two ε-estimates (rephrased in terms of
the common count `N`, the gap `D`, and the logarithms `Ly = log y < Lz = log z`), the
inequality `C₁/C₂ < (1-ε)/(1+ε)` is contradicted. -/
@[category API, AMS 11]
private lemma final_contradiction {C₁ C₂ ε N D Ly Lz : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hε : 0 < ε) (hε1 : ε < 1) (hD : 0 < D)
    (hLy : 0 < Ly) (hLz : 0 < Lz) (hLyz : Ly < Lz)
    (hbnd₂ : |N * Ly / (C₂ * D) - 1| < ε) (hbnd₁ : |N * Lz / (C₁ * D) - 1| < ε)
    (hρ : C₁ / C₂ < (1 - ε) / (1 + ε)) : False := by
  rw [abs_lt] at hbnd₁ hbnd₂
  set a := N * Ly / (C₂ * D) with ha_def
  set b := N * Lz / (C₁ * D) with hb_def
  have ha_lo : 1 - ε < a := by linarith [hbnd₂.1]
  have hb_hi : b < 1 + ε := by linarith [hbnd₁.2]
  have hN_pos : 0 < N := by
    by_contra hNle
    push_neg at hNle
    have hale : a ≤ 0 := by
      rw [ha_def]
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg hNle hLy.le
      · positivity
    linarith [ha_lo, hε1]
  have hb_pos : 0 < b := by rw [hb_def]; positivity
  have hratio := ratio_bound hε hε1 ha_lo hb_hi hb_pos
  have hDne : D ≠ 0 := ne_of_gt hD
  have hC₁ne : C₁ ≠ 0 := ne_of_gt hC₁
  have hC₂ne : C₂ ≠ 0 := ne_of_gt hC₂
  have hNne : N ≠ 0 := ne_of_gt hN_pos
  have hLzne : Lz ≠ 0 := ne_of_gt hLz
  have hab_eq : a / b = (C₁ * Ly) / (C₂ * Lz) := by
    rw [ha_def, hb_def]
    field_simp
  rw [hab_eq] at hratio
  have hab_lt : (C₁ * Ly) / (C₂ * Lz) < C₁ / C₂ := by
    rw [div_lt_div_iff₀ (by positivity) hC₂]
    nlinarith [mul_lt_mul_of_pos_left hLyz (mul_pos hC₁ hC₂)]
  linarith [hρ, hratio, hab_lt]

@[category API, AMS 11]
private lemma construct_z_lt_x {P D η : ℝ} (hD : 0 < D) (hη' : η < 1/2) :
    P + (1/2 + η) * D < P + ((3 + 2 * η) / 4) * D := by
  nlinarith

@[category API, AMS 11]
private lemma construct_x_lt_Q {P D η : ℝ} (hD : 0 < D) (hη' : η < 1/2) :
    P + ((3 + 2 * η) / 4) * D < P + D := by
  nlinarith

/-- All the inequalities placing `x, y, z` inside `(P, P + D)` and ensuring the filter side
conditions `x/2 < y < x` and `x/2 < z < x`. Bundled so the (nonlinear) arithmetic is checked
in its own declaration. -/
@[category API, AMS 11]
private lemma placement_bounds {P D η : ℝ} (hP : 0 < P) (hD : 0 < D)
    (hη_pos : 0 < η) (hη' : η < 1 / 2) :
    P < P + ((3 + 2 * η) / 4) * D ∧
    P + ((3 + 2 * η) / 4) * D < P + D ∧
    P ≤ P + (1 / 2) * D ∧
    P + (1 / 2) * D < P + D ∧
    P ≤ P + (1 / 2 + η) * D ∧
    P + (1 / 2 + η) * D < P + D ∧
    P + (1 / 2 + η) * D < P + ((3 + 2 * η) / 4) * D ∧
    P + (1 / 2) * D < P + ((3 + 2 * η) / 4) * D ∧
    P + (1 / 2) * D < P + (1 / 2 + η) * D ∧
    (P + ((3 + 2 * η) / 4) * D) / 2 < P + (1 / 2) * D ∧
    (P + ((3 + 2 * η) / 4) * D) / 2 < P + (1 / 2 + η) * D := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

@[category API, AMS 11]
lemma primeGap_zero : primeGap 0 = 1 := by
  show (0 + 1).nth Nat.Prime - (0 : ℕ).nth Nat.Prime = 1
  rw [Nat.nth_prime_zero_eq_two]
  simp only [zero_add]
  rw [Nat.nth_prime_one_eq_three]

@[category API, AMS 11]
lemma one_le_sup_primeGap {x : ℝ} (hx : 3 ≤ x) : 1 ≤ sup_primeGap x := by
  rw [sup_primeGap]
  have hceil : 3 ≤ ⌈x⌉₊ := by
    have : (3 : ℝ) ≤ ⌈x⌉₊ := le_trans hx (Nat.le_ceil x)
    exact_mod_cast this
  have h1 : 1 ≤ Nat.primeCounting' ⌈x⌉₊ := by
    have h3 : Nat.primeCounting' 3 = 1 := by decide
    calc 1 = Nat.primeCounting' 3 := h3.symm
      _ ≤ Nat.primeCounting' ⌈x⌉₊ := Nat.monotone_primeCounting' hceil
  calc (1 : ℕ) = primeGap 0 := primeGap_zero.symm
    _ ≤ (Finset.range (Nat.primeCounting' ⌈x⌉₊)).sup primeGap :=
        Finset.le_sup (f := primeGap) (Finset.mem_range.mpr h1)

@[category API, AMS 11]
lemma asymptoticA_eps {C : ℝ} (hC : 0 < C) (hA : AsymptoticA C) :
    ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X, ∀ y : ℝ, x / 2 < y → y < x →
      |((realPi (y + C * (sup_primeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
        Real.log y / (C * (sup_primeGap x : ℝ)) - 1| < ε := by
  set f := primeCount_Ioc_mul_const C with hf
  set g : ℝ × ℝ → ℝ := fun p ↦ C * (sup_primeGap p.1) / Real.log p.2 with hg
  -- Step 1: `g` is eventually nonzero on the filter.
  have hg_ne : ∀ᶠ p in snd_gt_half_fst, g p ≠ 0 := by
    rw [snd_gt_half_fst, Filter.eventually_inf_principal, Filter.eventually_comap,
        Filter.eventually_atTop]
    refine ⟨4, fun b hb a ha hmem => ?_⟩
    subst ha
    rw [Set.mem_setOf_eq, Set.mem_Ioo] at hmem
    obtain ⟨hy_lo, hy_hi⟩ := hmem
    have hx3 : (3 : ℝ) ≤ a.1 := by linarith
    have hsup : 1 ≤ sup_primeGap a.1 := one_le_sup_primeGap hx3
    have hsup_pos : (0 : ℝ) < sup_primeGap a.1 := by exact_mod_cast hsup
    have hy_pos : 1 < a.2 := by linarith
    have hlog_pos : 0 < Real.log a.2 := Real.log_pos hy_pos
    have : (0 : ℝ) < g a := by
      rw [hg]; positivity
    exact ne_of_gt this
  -- Step 2: convert the asymptotic equivalence to convergence of the ratio to 1.
  have htend : Filter.Tendsto (f / g) snd_gt_half_fst (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hg_ne).mp hA
  intro ε hε
  -- Step 3: ε-closeness of the ratio to 1, eventually.
  have heps : ∀ᶠ p in snd_gt_half_fst, dist ((f / g) p) 1 < ε :=
    Metric.tendsto_nhds.mp htend ε hε
  -- Step 4: unpack the filter to extract a threshold `X`.
  rw [snd_gt_half_fst, Filter.eventually_inf_principal, Filter.eventually_comap,
      Filter.eventually_atTop] at heps
  obtain ⟨X, hX⟩ := heps
  refine ⟨max X 4, fun x hx y hy_lo hy_hi => ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have key := hX x hxX (x, y) rfl ⟨hy_lo, hy_hi⟩
  -- Translate `dist ((f/g) (x,y)) 1 < ε` into the goal's absolute-value form.
  rw [Real.dist_eq] at key
  have hf_eq : f (x, y) = (realPi (y + C * (sup_primeGap x : ℝ)) : ℝ) - (realPi y : ℝ) := by
    simp only [hf, primeCount_Ioc_mul_const, realPi]
  have hg_eq : g (x, y) = C * (sup_primeGap x : ℝ) / Real.log y := rfl
  have hfg : (f / g) (x, y) =
      ((realPi (y + C * (sup_primeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
        Real.log y / (C * (sup_primeGap x : ℝ)) := by
    have hx3 : (3 : ℝ) ≤ x := by linarith
    have hsup : 1 ≤ sup_primeGap x := one_le_sup_primeGap hx3
    have hsup_pos : (0 : ℝ) < sup_primeGap x := by exact_mod_cast hsup
    have hy_pos : 1 < y := by linarith
    have hlog_pos : 0 < Real.log y := Real.log_pos hy_pos
    rw [Pi.div_apply, hf_eq, hg_eq, div_div_eq_mul_div]
  rw [hfg] at key
  exact key

/--
**Erdős Problem 1138 (disproof).** For `1 < C₁ < C₂` with `C₂ - C₁ < 1/2`, the asymptotic
`π(y + Cd) - π(y) ∼ Cd / log y` cannot hold simultaneously for both `C₁` and `C₂`.
-/
@[category research solved, AMS 11]
theorem erdos1138_theorem (C₁ C₂ : ℝ) (hC₁_pos : 1 < C₁) (hlt : C₁ < C₂)
    (hη : C₂ - C₁ < 1 / 2) : ¬(AsymptoticA C₁ ∧ AsymptoticA C₂) := by
  rintro ⟨hA₁, hA₂⟩
  have hC₁ : (0 : ℝ) < C₁ := by linarith
  have hC₂ : (0 : ℝ) < C₂ := by linarith
  -- Choose the gap parameter `ε`.
  set ε := (C₂ - C₁) / (2 * (C₂ + C₁)) with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; exact div_pos (by linarith) (by linarith)
  have hε_lt1 : ε < 1 := by
    rw [hε_def, div_lt_one (by linarith)]; linarith
  have hε_lt : C₁ / C₂ < (1 - ε) / (1 + ε) := rho_lt_bound hC₁ hlt
  -- Translate each asymptotic into an ε-estimate beyond some threshold.
  obtain ⟨X₂, hX₂⟩ := asymptoticA_eps hC₂ hA₂ ε hε_pos
  obtain ⟨X₁, hX₁⟩ := asymptoticA_eps hC₁ hA₁ ε hε_pos
  -- Pick a strict record gap whose prime `P` is large enough.
  obtain ⟨n, hn_rec, hn_pos, hn_B⟩ :=
    record_gap_arbitrarily_large (max (Nat.ceil (max X₁ X₂)) 3)
  set η := C₂ - C₁ with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; linarith
  have hη_lt : η < 1 / 2 := hη
  set P := (nthPrime n : ℝ) with hP_def
  set Q := (nthPrime (n + 1) : ℝ) with hQ_def
  set D := (primeGap n : ℝ) with hD_def
  set x := P + ((3 + 2 * η) / 4) * D with hx_def
  set y := P + (1 / 2) * D with hy_def
  set z := P + (1 / 2 + η) * D with hz_def
  have hD_pos : (0 : ℝ) < D := by rw [hD_def]; exact_mod_cast primeGap_pos n
  have hP_two : (2 : ℝ) ≤ P := by rw [hP_def]; exact_mod_cast nthPrime_ge_two n
  have hQ_eq : Q = P + D := by
    rw [hQ_def, hP_def, hD_def]
    have := nthPrime_succ_eq n
    rw [this]; push_cast; ring
  have hP_pos : (0 : ℝ) < P := by linarith [hP_two]
  -- All placement bounds, computed once in `placement_bounds`.
  obtain ⟨hP_lt_x, hx_lt_PD, hP_le_y, hy_lt_PD, hP_le_z, hz_lt_PD, hz_lt_x, hy_lt_x,
      hy_lt_z, hxy_lo, hxz_lo⟩ := placement_bounds hP_pos hD_pos hη_pos hη_lt
  rw [← hx_def] at hP_lt_x hx_lt_PD
  rw [← hy_def] at hP_le_y hy_lt_PD hy_lt_x hy_lt_z hxy_lo
  rw [← hz_def] at hP_le_z hz_lt_PD hz_lt_x hy_lt_z hxz_lo
  have hx_lt_Q : x < Q := by rw [hQ_eq]; exact hx_lt_PD
  have hy_lt_Q : y < Q := by rw [hQ_eq]; exact hy_lt_PD
  have hz_lt_Q : z < Q := by rw [hQ_eq]; exact hz_lt_PD
  -- `x` is large enough to exceed the asymptotic thresholds.
  have hX_le_P : (max X₁ X₂ : ℝ) ≤ P := by
    have h1 : (max (Nat.ceil (max X₁ X₂)) 3 : ℝ) ≤ P := by rw [hP_def]; exact_mod_cast hn_B
    have h2 : (Nat.ceil (max X₁ X₂) : ℝ) ≤ P :=
      le_trans (by exact_mod_cast le_max_left (Nat.ceil (max X₁ X₂)) 3) h1
    exact le_trans (Nat.le_ceil _) h2
  have hX₁_le_x : X₁ ≤ x := by
    have : X₁ ≤ P := le_trans (le_max_left _ _) hX_le_P
    linarith [hP_lt_x]
  have hX₂_le_x : X₂ ≤ x := by
    have : X₂ ≤ P := le_trans (le_max_right _ _) hX_le_P
    linarith [hP_lt_x]
  -- `sup_primeGap x = D` since `x ∈ (P, Q)` at a record index.
  have hsup_x : (sup_primeGap x : ℝ) = D := by
    rw [hD_def]
    exact_mod_cast sup_primeGap_eq_at_record hn_rec hP_lt_x hx_lt_Q
  -- `realPi y = realPi z` since both `y, z ∈ [P, Q)`.
  have hreal_yz : realPi y = realPi z :=
    realPi_eq_of_in_gap hP_le_y hy_lt_Q hP_le_z hz_lt_Q
  -- The shifted arguments coincide: `y + C₂·D = z + C₁·D`.
  have hshift : y + C₂ * D = z + C₁ * D := by rw [hy_def, hz_def, hη_def]; ring
  -- Set `N` = the common interval count.
  set N : ℝ := (realPi (y + C₂ * D) : ℝ) - (realPi y : ℝ) with hN_def
  -- ε-bound from `C₂` at `(x, y)`.
  have hbound₂ := hX₂ x hX₂_le_x y hxy_lo hy_lt_x
  rw [hsup_x] at hbound₂
  -- ε-bound from `C₁` at `(x, z)`.
  have hbound₁ := hX₁ x hX₁_le_x z hxz_lo hz_lt_x
  rw [hsup_x] at hbound₁
  -- Rewrite `hbound₁` so it speaks about the same `N`.
  have hN_eq₁ : (realPi (z + C₁ * D) : ℝ) - (realPi z : ℝ) = N := by
    rw [hN_def, ← hshift, hreal_yz]
  rw [hN_eq₁] at hbound₁
  rw [show (realPi (y + C₂ * D) : ℝ) - (realPi y : ℝ) = N from hN_def.symm] at hbound₂
  -- Positivity of the logarithms and `log y < log z`.
  have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith [hP_two])
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith [hP_two])
  have hlogyz : Real.log y < Real.log z :=
    Real.log_lt_log (by linarith [hP_two]) hy_lt_z
  -- Hand off to the pure-arithmetic core.
  exact final_contradiction hC₁ hC₂ hε_pos hε_lt1 hD_pos
    hlogy_pos hlogz_pos hlogyz hbound₂ hbound₁ hε_lt

/--
**Erdős Problem 1138 (disproof, corollary).** The asymptotic `π(y + Cd) - π(y) ∼ Cd / log y`
cannot hold for every `C > 1`: e.g. `C = 2` and `C = 9/4` already give a contradiction.
-/
@[category research solved, AMS 11]
theorem erdos1138_corollary :
    ¬(∀ C > 1, primeCount_Ioc_mul_const C ~[snd_gt_half_fst]
    (fun (x, y) ↦ (C * (sup_primeGap x) / Real.log y))) := by
  intro h
  exact erdos1138_theorem 2 (9/4) (by norm_num) (by norm_num) (by norm_num)
    ⟨h 2 (by norm_num), h (9/4) (by norm_num)⟩

end Erdos1138a
