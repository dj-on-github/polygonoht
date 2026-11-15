import PolygonLean.Boundary

/-!
# Integer comparator constants

Formalizes Sections 7–9 of the follow-up paper:

* the integer comparators of Eqs. (6)–(9) with the stated rounding directions
  are **sound**: an `(count1, count11)` pair that passes them has asymptotic
  min-entropy rate at least `H` (§7.3, "one-sided error");
* every entry of Table 3 (`n = 2304`, `k = 12`) and the `P₂` constants of §9,
  checked exactly from `p¹⁰ = 2^{-10H}`;
* the `H = 0.5` special case, the spot check at `count1 = 1152`, `A₁ + B₁ = 8191`,
  and the bit widths of the datapaths;
* the multiplier-based exact arc test of §9 is sound.
-/

open Real

namespace Polygon

noncomputable section

/-! ### Soundness of the integer comparators -/

/-- The exact test (AB, BC, DC, `y ≥ 0` and the ellipse itself) is sound. -/
theorem exact_sound {p x y : ℝ} (hp1 : p < 1) (hAB : y ≤ lAB p x)
    (hBC : y ≤ lBC p x) (hDC : lCD x ≤ y) (hy : 0 ≤ y)
    (harc : (x - y) ^ 2 ≤ p ^ 2 * (x * (1 - x))) : Feasible x y ∧ InRegion p x y := by
  unfold lAB lBC lCD at *
  have hx0 : 0 < x := by by_contra h; push Not at h; nlinarith
  have hx1 : x < 1 := by nlinarith
  exact ⟨⟨hx0, hx1, hy, by nlinarith, hDC⟩, hAB, hBC, harc⟩

section scaling
variable {N : ℕ} (hN : 0 < N)
include hN

lemma scale_AB {p : ℝ} {S c1 c11 : ℝ} (hS : 0 < S) (hc1 : 0 ≤ c1) {A1 A0 : ℝ}
    (hA1 : A1 ≤ (2 - p) * S) (hA0 : (1 - p) * S * N ≤ A0) (t : S * c11 ≤ A1 * c1 - A0) :
    c11 / N ≤ lAB p (c1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold lAB
  rw [div_le_iff₀ hNr]
  have : S * c11 ≤ S * ((2 - p) * c1 - (1 - p) * N) := by nlinarith
  have := le_of_mul_le_mul_left this hS
  calc c11 ≤ (2 - p) * c1 - (1 - p) * N := this
    _ = ((2 - p) * (c1 / N) - (1 - p)) * N := by field_simp

lemma scale_BC {p : ℝ} {S c1 c11 B1 : ℝ} (hS : 0 < S) (hc1 : 0 ≤ c1)
    (hB1 : B1 ≤ p * S) (t : S * c11 ≤ B1 * c1) : c11 / N ≤ lBC p (c1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold lBC
  rw [div_le_iff₀ hNr, mul_assoc, div_mul_cancel₀ _ hNr.ne']
  have : S * c11 ≤ S * (p * c1) := by nlinarith
  exact le_of_mul_le_mul_left this hS

lemma scale_DC {c1 c11 : ℝ} (t : 2 * c1 - N ≤ c11) : lCD (c1 / N) ≤ c11 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold lCD
  rw [le_div_iff₀ hNr, sub_mul, mul_assoc, div_mul_cancel₀ _ hNr.ne']; linarith

lemma scale_ED {c c1 c11 C0 : ℝ} (hC0 : C0 ≤ c * N) (t : c1 - C0 ≤ c11) :
    c1 / N - c ≤ c11 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr, sub_mul, div_mul_cancel₀ _ hNr.ne']; linarith

lemma scale_arc {p : ℝ} {S c1 c11 P2 : ℝ} (hS : 0 < S) (hc1 : 0 ≤ c1) (hc1N : c1 ≤ N)
    (hP2 : P2 ≤ p ^ 2 * S) (t : S * (c1 - c11) ^ 2 ≤ P2 * c1 * (N - c1)) :
    (c1 / N - c11 / N) ^ 2 ≤ p ^ 2 * (c1 / N * (1 - c1 / N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ c1 * (N - c1) := mul_nonneg hc1 (by linarith)
  have h1 : S * (c1 - c11) ^ 2 ≤ S * (p ^ 2 * (c1 * (N - c1))) := by
    calc S * (c1 - c11) ^ 2 ≤ P2 * c1 * (N - c1) := t
      _ = P2 * (c1 * (N - c1)) := by ring
      _ ≤ p ^ 2 * S * (c1 * (N - c1)) := mul_le_mul_of_nonneg_right hP2 hq
      _ = S * (p ^ 2 * (c1 * (N - c1))) := by ring
  have h2 := le_of_mul_le_mul_left h1 hS
  have e1 : (c1 / N - c11 / N) ^ 2 = (c1 - c11) ^ 2 / N ^ 2 := by field_simp
  have e2 : p ^ 2 * (c1 / N * (1 - c1 / N)) = p ^ 2 * (c1 * (N - c1)) / N ^ 2 := by field_simp
  rw [e1, e2]; exact div_le_div_of_nonneg_right h2 (by positivity)

end scaling

/-- **Integer five-edge test is sound** (Eqs. (6)–(9) with `C₀ ≤ c5·N`): rounding
`A₁, B₁, C₀` down and `A₀` up only shrinks the accept region, so a block that
passes has `H∞ ≥ H`. -/
theorem int5_sound {H : ℝ} (hH : 0 < H) {N k : ℕ} (hN : 0 < N) {A1 A0 B1 C0 : ℤ}
    (hA1 : (A1 : ℝ) ≤ (2 - pOf H) * 2 ^ k) (hA0 : (1 - pOf H) * 2 ^ k * N ≤ A0)
    (hB1 : (B1 : ℝ) ≤ pOf H * 2 ^ k) (hC0 : (C0 : ℝ) ≤ c5 (pOf H) * N) {c1 c11 : ℕ}
    (tAB : 2 ^ k * (c11 : ℤ) ≤ A1 * c1 - A0) (tBC : 2 ^ k * (c11 : ℤ) ≤ B1 * c1)
    (tDC : 2 * (c1 : ℤ) - N ≤ c11) (tED : (c1 : ℤ) - C0 ≤ c11) :
    H ≤ Hinf ((c1 : ℝ) / N) ((c11 : ℝ) / N) := by
  have hS : (0 : ℝ) < 2 ^ k := by positivity
  have hc1 : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have tAB' : (2 : ℝ) ^ k * c11 ≤ A1 * c1 - A0 := by exact_mod_cast tAB
  have tBC' : (2 : ℝ) ^ k * c11 ≤ B1 * c1 := by exact_mod_cast tBC
  have tDC' : 2 * (c1 : ℝ) - N ≤ c11 := by exact_mod_cast tDC
  have tED' : (c1 : ℝ) - C0 ≤ c11 := by exact_mod_cast tED
  exact linear5_entropy hH (scale_AB hN hS hc1 hA1 hA0 tAB') (scale_BC hN hS hc1 hB1 tBC')
    (scale_DC hN tDC') (scale_ED hN hC0 tED') (by positivity)

/-- **Integer triangle test is sound** for `H ≥ log₂ φ` (Eqs. (6), (7), (9) with
`C₀ ≤ c3·N`; the DC test is not needed). -/
theorem int3_sound {H : ℝ} (hH : logb 2 goldenRatio ≤ H) {N k : ℕ} (hN : 0 < N)
    {A1 A0 B1 C0 : ℤ}
    (hA1 : (A1 : ℝ) ≤ (2 - pOf H) * 2 ^ k) (hA0 : (1 - pOf H) * 2 ^ k * N ≤ A0)
    (hB1 : (B1 : ℝ) ≤ pOf H * 2 ^ k) (hC0 : (C0 : ℝ) ≤ c3 (pOf H) * N) {c1 c11 : ℕ}
    (tAB : 2 ^ k * (c11 : ℤ) ≤ A1 * c1 - A0) (tBC : 2 ^ k * (c11 : ℤ) ≤ B1 * c1)
    (tED : (c1 : ℤ) - C0 ≤ c11) :
    H ≤ Hinf ((c1 : ℝ) / N) ((c11 : ℝ) / N) := by
  have hS : (0 : ℝ) < 2 ^ k := by positivity
  have hc1 : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have tAB' : (2 : ℝ) ^ k * c11 ≤ A1 * c1 - A0 := by exact_mod_cast tAB
  have tBC' : (2 : ℝ) ^ k * c11 ≤ B1 * c1 := by exact_mod_cast tBC
  have tED' : (c1 : ℝ) - C0 ≤ c11 := by exact_mod_cast tED
  exact linear3_entropy hH (scale_AB hN hS hc1 hA1 hA0 tAB') (scale_BC hN hS hc1 hB1 tBC')
    (scale_ED hN hC0 tED')

/-- **§9: the multiplier-based arc test is sound.** With `P₂ ≤ p²2ᵏ`, a block
passing AB, BC, DC and `2ᵏ(count1 - count11)² ≤ P₂·count1·(N - count1)` has
`H∞ ≥ H`. -/
theorem intArc_sound {H : ℝ} (hH : 0 < H) {N k : ℕ} (hN : 0 < N) {A1 A0 B1 P2 : ℤ}
    (hA1 : (A1 : ℝ) ≤ (2 - pOf H) * 2 ^ k) (hA0 : (1 - pOf H) * 2 ^ k * N ≤ A0)
    (hB1 : (B1 : ℝ) ≤ pOf H * 2 ^ k) (hP2 : (P2 : ℝ) ≤ pOf H ^ 2 * 2 ^ k) {c1 c11 : ℕ}
    (hc1N : c1 ≤ N)
    (tAB : 2 ^ k * (c11 : ℤ) ≤ A1 * c1 - A0) (tBC : 2 ^ k * (c11 : ℤ) ≤ B1 * c1)
    (tDC : 2 * (c1 : ℤ) - N ≤ c11)
    (tArc : 2 ^ k * ((c1 : ℤ) - c11) ^ 2 ≤ P2 * c1 * (N - c1)) :
    H ≤ Hinf ((c1 : ℝ) / N) ((c11 : ℝ) / N) := by
  have hp1 : pOf H < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hS : (0 : ℝ) < 2 ^ k := by positivity
  have hc1 : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have tAB' : (2 : ℝ) ^ k * c11 ≤ A1 * c1 - A0 := by exact_mod_cast tAB
  have tBC' : (2 : ℝ) ^ k * c11 ≤ B1 * c1 := by exact_mod_cast tBC
  have tDC' : 2 * (c1 : ℝ) - N ≤ c11 := by exact_mod_cast tDC
  have tArc' : (2 : ℝ) ^ k * ((c1 : ℝ) - c11) ^ 2 ≤ P2 * c1 * (N - c1) := by exact_mod_cast tArc
  have hc1N' : (c1 : ℝ) ≤ N := by exact_mod_cast hc1N
  obtain ⟨hf, hr⟩ := exact_sound hp1 (scale_AB hN hS hc1 hA1 hA0 tAB')
    (scale_BC hN hS hc1 hB1 tBC') (scale_DC hN tDC') (by positivity)
    (scale_arc hN hS hc1 hc1N' hP2 tArc')
  exact (Hinf_ge_iff hf H).mpr hr

/-! ### Exact values of `p = 2^{-k/10}` -/

/-- `p` at `H = k/10`. -/
def pK (k : ℕ) : ℝ := pOf ((k : ℝ) / 10)

lemma pK_pos (k : ℕ) : 0 < pK k := pOf_pos _

/-- `p¹⁰ = 2^{-k}`. -/
lemma pK_pow10 (k : ℕ) : pK k ^ 10 = 1 / 2 ^ k := by
  rw [pK, pOf, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [show -((k : ℝ) / 10) * ((10 : ℕ) : ℝ) = -(k : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- Rational bounds on `p` from `lo¹⁰ < 2^{-k} < hi¹⁰`. -/
lemma pK_bounds (k : ℕ) {lo hi : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ hi) (hlo : lo ^ 10 < 1 / 2 ^ k)
    (hhi : 1 / 2 ^ k < hi ^ 10) : lo < pK k ∧ pK k < hi := by
  have hp := pK_pos k
  rw [← pK_pow10] at hlo hhi
  exact ⟨(pow_lt_pow_iff_left₀ h0 hp.le (by norm_num)).mp hlo,
    (pow_lt_pow_iff_left₀ hp.le (h0.trans h1) (by norm_num)).mp hhi⟩

lemma pHalf_sq : pOf (1 / 2) ^ 2 = 1 / 2 := by
  rw [pOf, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg_one]

lemma pK5_sq : pK 5 ^ 2 = 1 / 2 := by
  rw [pK, show ((5 : ℕ) : ℝ) / 10 = 1 / 2 by norm_num]; exact pHalf_sq

lemma c5_strictMono {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : c5 a < c5 b := by
  unfold c5
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_lt_pow_left₀ hab ha two_ne_zero]

lemma c5_bounds {lo hi p : ℝ} (hl : lo < p) (hh : p < hi) (h0 : 0 ≤ lo) (_h1 : hi ≤ 1) :
    c5 lo ≤ c5 p ∧ c5 p ≤ c5 hi :=
  ⟨(c5_strictMono h0 hl).le, (c5_strictMono (h0.trans hl.le) hh).le⟩

lemma c3_bounds {lo hi p : ℝ} (hl : lo < p) (hh : p < hi) (h0 : 1 / 2 ≤ lo) (h1 : hi ≤ 1) :
    lo ^ 2 * (1 - hi) / Δ hi ≤ c3 p ∧ c3 p ≤ hi ^ 2 * (1 - lo) / Δ lo := by
  have hΔ : ∀ a b : ℝ, 1 / 2 ≤ a → a ≤ b → Δ a ≤ Δ b := by
    intro a b ha hab; unfold Δ; nlinarith
  have pos : ∀ a : ℝ, 0 < Δ a := fun a => by unfold Δ; nlinarith [sq_nonneg (a - 1 / 2)]
  unfold c3
  constructor
  · apply div_le_div₀ (by nlinarith) _ (pos _) (hΔ _ _ (by linarith) hh.le)
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) hl.le 2) (by linarith) (by linarith)
      (by positivity)
  · apply div_le_div₀ (by nlinarith) _ (pos _) (hΔ _ _ h0 hl.le)
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) hh.le 2) (by linarith) (by linarith)
      (by positivity)

/-! ### Table 3 and the §9 `P₂` constants (`n = 2304`, `N = 2303`, `k = 12`)

Each row is checked against the exact value of `p`. Row `H = 0.6` gives
`P₂ = ⌊p²·4096⌋ = 1782`; the paper prints 1783, which is rounded up. -/

/-- Row `H = 0.1` of Table 3 (and the `P₂` constant of §9). -/
theorem row1 :
    ⌊(2 - pK 1) * 4096⌋ = 4370 ∧ ⌈(1 - pK 1) * 4096 * 2303⌉ = 631706 ∧ ⌊pK 1 * 4096⌋ = 3821 ∧
    ⌊c5 (pK 1) * 2303⌋ = 1071 ∧ ⌊pK 1 ^ 2 * 4096⌋ = 3565 := by
  obtain ⟨hl, hh⟩ := pK_bounds 1 (lo := 0.933032991536807) (hi := 0.933032991536808)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c5_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.933032991536807 : ℝ) ^ 2 < pK 1 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 1 ^ 2 < (0.933032991536808 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.2` of Table 3 (and the `P₂` constant of §9). -/
theorem row2 :
    ⌊(2 - pK 2) * 4096⌋ = 4626 ∧ ⌈(1 - pK 2) * 4096 * 2303⌉ = 1221108 ∧ ⌊pK 2 * 4096⌋ = 3565 ∧
    ⌊c5 (pK 2) * 2303⌋ = 992 ∧ ⌊pK 2 ^ 2 * 4096⌋ = 3104 := by
  obtain ⟨hl, hh⟩ := pK_bounds 2 (lo := 0.870550563296124) (hi := 0.870550563296125)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c5_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.870550563296124 : ℝ) ^ 2 < pK 2 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 2 ^ 2 < (0.870550563296125 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.3` of Table 3 (and the `P₂` constant of §9). -/
theorem row3 :
    ⌊(2 - pK 3) * 4096⌋ = 4865 ∧ ⌈(1 - pK 3) * 4096 * 2303⌉ = 1771040 ∧ ⌊pK 3 * 4096⌋ = 3326 ∧
    ⌊c5 (pK 3) * 2303⌋ = 915 ∧ ⌊pK 3 ^ 2 * 4096⌋ = 2702 := by
  obtain ⟨hl, hh⟩ := pK_bounds 3 (lo := 0.812252396356235) (hi := 0.812252396356236)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c5_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.812252396356235 : ℝ) ^ 2 < pK 3 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 3 ^ 2 < (0.812252396356236 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.4` of Table 3 (and the `P₂` constant of §9). -/
theorem row4 :
    ⌊(2 - pK 4) * 4096⌋ = 5087 ∧ ⌈(1 - pK 4) * 4096 * 2303⌉ = 2284145 ∧ ⌊pK 4 * 4096⌋ = 3104 ∧
    ⌊c5 (pK 4) * 2303⌋ = 840 ∧ ⌊pK 4 ^ 2 * 4096⌋ = 2352 := by
  obtain ⟨hl, hh⟩ := pK_bounds 4 (lo := 0.757858283255199) (hi := 0.757858283255200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c5_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.757858283255199 : ℝ) ^ 2 < pK 4 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 4 ^ 2 < (0.757858283255200 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.5` of Table 3 (and the `P₂` constant of §9). -/
theorem row5 :
    ⌊(2 - pK 5) * 4096⌋ = 5295 ∧ ⌈(1 - pK 5) * 4096 * 2303⌉ = 2762888 ∧ ⌊pK 5 * 4096⌋ = 2896 ∧
    ⌊c5 (pK 5) * 2303⌋ = 767 ∧ ⌊pK 5 ^ 2 * 4096⌋ = 2048 := by
  obtain ⟨hl, hh⟩ := pK_bounds 5 (lo := 0.707106781186547) (hi := 0.707106781186548)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c5_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [pK5_sq]; norm_num

/-- Row `H = 0.6` of Table 3 (and the `P₂` constant of §9). -/
theorem row6 :
    ⌊(2 - pK 6) * 4096⌋ = 5489 ∧ ⌈(1 - pK 6) * 4096 * 2303⌉ = 3209571 ∧ ⌊pK 6 * 4096⌋ = 2702 ∧
    ⌊c5 (pK 6) * 2303⌋ = 698 ∧ ⌊pK 6 ^ 2 * 4096⌋ = 1782 := by
  obtain ⟨hl, hh⟩ := pK_bounds 6 (lo := 0.659753955386447) (hi := 0.659753955386448)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c5_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.659753955386447 : ℝ) ^ 2 < pK 6 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 6 ^ 2 < (0.659753955386448 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.7` of Table 3 (and the `P₂` constant of §9). -/
theorem row7 :
    ⌊(2 - pK 7) * 4096⌋ = 5670 ∧ ⌈(1 - pK 7) * 4096 * 2303⌉ = 3626342 ∧ ⌊pK 7 * 4096⌋ = 2521 ∧
    ⌊c3 (pK 7) * 2303⌋ = 636 ∧ ⌊pK 7 ^ 2 * 4096⌋ = 1552 := by
  obtain ⟨hl, hh⟩ := pK_bounds 7 (lo := 0.615572206672458) (hi := 0.615572206672459)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 7
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c3_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.615572206672458 : ℝ) ^ 2 < pK 7 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 7 ^ 2 < (0.615572206672459 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.8` of Table 3 (and the `P₂` constant of §9). -/
theorem row8 :
    ⌊(2 - pK 8) * 4096⌋ = 5839 ∧ ⌈(1 - pK 8) * 4096 * 2303⌉ = 4015202 ∧ ⌊pK 8 * 4096⌋ = 2352 ∧
    ⌊c3 (pK 8) * 2303⌋ = 632 ∧ ⌊pK 8 ^ 2 * 4096⌋ = 1351 := by
  obtain ⟨hl, hh⟩ := pK_bounds 8 (lo := 0.574349177498517) (hi := 0.574349177498518)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 8
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c3_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.574349177498517 : ℝ) ^ 2 < pK 8 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 8 ^ 2 < (0.574349177498518 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- Row `H = 0.9` of Table 3 (and the `P₂` constant of §9). -/
theorem row9 :
    ⌊(2 - pK 9) * 4096⌋ = 5997 ∧ ⌈(1 - pK 9) * 4096 * 2303⌉ = 4378022 ∧ ⌊pK 9 * 4096⌋ = 2194 ∧
    ⌊c3 (pK 9) * 2303⌋ = 610 ∧ ⌊pK 9 ^ 2 * 4096⌋ = 1176 := by
  obtain ⟨hl, hh⟩ := pK_bounds 9 (lo := 0.535886731268146) (hi := 0.535886731268147)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := pK_pos 9
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast
    obtain ⟨c1, c2⟩ := c3_bounds hl hh (by norm_num) (by norm_num)
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right c1 (by norm_num)); norm_num [c5, c3, Δ]
    · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right c2 (by norm_num)) ?_; norm_num [c5, c3, Δ]
  · rw [Int.floor_eq_iff]; push_cast
    have h1 : (0.535886731268146 : ℝ) ^ 2 < pK 9 ^ 2 :=
      pow_lt_pow_left₀ hl (by norm_num) two_ne_zero
    have h2 : pK 9 ^ 2 < (0.535886731268147 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hh hp.le two_ne_zero
    constructor <;> nlinarith

/-- The paper's `P₂ = 1783` at `H = 0.6` is one too large: rounding it up enlarges
the accept region, the non-conservative direction. -/
theorem P2_row6_paper_value_too_large : ⌊pK 6 ^ 2 * 4096⌋ ≠ 1783 := by
  rw [row6.2.2.2.2]; norm_num

/-- `A₁ + B₁ = 8191 = 2S - 1` in every row (caption of Table 3). -/
theorem A1_add_B1 : (4370 + 3821 : ℤ) = 8191 ∧ 4626 + 3565 = 8191 ∧ 4865 + 3326 = 8191 ∧
    5087 + 3104 = 8191 ∧ 5295 + 2896 = 8191 ∧ 5489 + 2702 = 8191 ∧ 5670 + 2521 = 8191 ∧
    5839 + 2352 = 8191 ∧ 5997 + 2194 = 8191 := by norm_num

/-- The general reason: if `pS` is not an integer, `⌊(2-p)S⌋ + ⌊pS⌋ = 2S - 1`. -/
theorem floor_add_floor (S : ℤ) (p : ℝ) (h : ∀ z : ℤ, p * S ≠ z) :
    ⌊(2 - p) * S⌋ + ⌊p * S⌋ = 2 * S - 1 := by
  have hf : (⌊p * S⌋ : ℝ) < p * S := lt_of_le_of_ne (Int.floor_le _) (h _).symm
  have hc : ⌈p * S⌉ = ⌊p * S⌋ + 1 := by
    rw [Int.ceil_eq_iff]; push_cast; exact ⟨by linarith, (Int.lt_floor_add_one _).le⟩
  rw [show (2 - p) * (S : ℝ) = ((2 * S : ℤ) : ℝ) + -(p * S) by push_cast; ring,
    Int.floor_intCast_add, Int.floor_neg, hc]; ring

/-! ### Regimes of the nine rows -/

lemma goldenRatio_inv : goldenRatio⁻¹ = (√5 - 1) / 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [goldenRatio, inv_div, div_eq_div_iff (by positivity) (by norm_num)]; nlinarith

/-- `H = 0.6` is in the five-edge regime and `H = 0.7` in the triangle regime,
so `0.6 < H* = log₂ φ < 0.7`. -/
theorem Hstar_between : (6 : ℝ) / 10 < logb 2 goldenRatio ∧ logb 2 goldenRatio < 7 / 10 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s1 : (2.236 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  obtain ⟨l6, -⟩ := pK_bounds 6 (lo := 0.659753955386447) (hi := 0.659753955386448)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h7⟩ := pK_bounds 7 (lo := 0.615572206672458) (hi := 0.615572206672459)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · have : goldenRatio⁻¹ ≤ pK 6 := by rw [goldenRatio_inv]; linarith
    rcases ((regime_iff _).mp this).lt_or_eq with h | h
    · push_cast at h ⊢; linarith
    · exfalso
      have : pK 6 = goldenRatio⁻¹ := by
        rw [pK, pOf, show ((6 : ℕ) : ℝ) / 10 = logb 2 goldenRatio by exact_mod_cast h,
          Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
          (by unfold goldenRatio; positivity)]
      rw [this, goldenRatio_inv] at l6; linarith
  · by_contra h; push Not at h
    have := (regime_iff ((7 : ℕ) / 10 : ℝ)).mpr (by push_cast; linarith)
    rw [goldenRatio_inv] at this
    have : pK 7 ≥ (√5 - 1) / 2 := this
    linarith

/-! ### The nine rows give sound tests -/

/-- Row `H = 0.4` (the example of the SPACE 2024 paper), as an instance:
a 2304-bit block passing the integer test with Table 3's constants has
min-entropy rate at least 0.4. -/
theorem row4_sound {c1 c11 : ℕ}
    (tAB : 4096 * (c11 : ℤ) ≤ 5087 * c1 - 2284145) (tBC : 4096 * (c11 : ℤ) ≤ 3104 * c1)
    (tDC : 2 * (c1 : ℤ) - 2303 ≤ c11) (tED : (c1 : ℤ) - 840 ≤ c11) :
    (4 : ℝ) / 10 ≤ Hinf ((c1 : ℝ) / 2303) ((c11 : ℝ) / 2303) := by
  obtain ⟨hA1, hA0, hB1, hC0, -⟩ := row4
  have e12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
  have eN : ((2303 : ℕ) : ℝ) = 2303 := by norm_num
  have := int5_sound (H := ((4 : ℕ) : ℝ) / 10) (N := 2303) (k := 12) (A1 := 5087)
    (A0 := 2284145) (B1 := 3104) (C0 := 840) (by norm_num) (by norm_num)
    (by have := Int.floor_le ((2 - pK 4) * 4096); rw [hA1] at this; rw [e12]; exact this)
    (by have := Int.le_ceil ((1 - pK 4) * 4096 * 2303); rw [hA0] at this; rw [e12, eN]
        exact this)
    (by have := Int.floor_le (pK 4 * 4096); rw [hB1] at this; rw [e12]; exact this)
    (by have := Int.floor_le (c5 (pK 4) * 2303); rw [hC0] at this; rw [eN]; exact this)
    (by norm_num; exact tAB) (by norm_num; exact tBC) (by push_cast; exact tDC) tED
  push_cast at this ⊢; exact this

/-! ### The `H = 0.5` special case (§7.2) -/

/-- At `H = 0.5`, `c = 1/3`, `D = (2/3, 1/3)`, `P₂ = 2048` exactly and
`C₀ = ⌊2303/3⌋ = 767`. -/
theorem half_case : c5 (pOf (1 / 2)) = 1 / 3 ∧ xD (pOf (1 / 2)) = 2 / 3 ∧
    lCD (xD (pOf (1 / 2))) = 1 / 3 ∧ pOf (1 / 2) ^ 2 * 4096 = 2048 ∧
    ⌊c5 (pOf (1 / 2)) * 2303⌋ = 767 := by
  unfold c5 xD lCD
  rw [pHalf_sq]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [Int.floor_eq_iff]; norm_num

/-- At `H = 0.5` the integer arc test is *exactly* the arc constraint:
`2(count1 - count11)² ≤ count1(N - count1)`. -/
theorem half_arc_exact {N : ℕ} (hN : 0 < N) (c1 c11 : ℕ) :
    2 * ((c1 : ℝ) - c11) ^ 2 ≤ c1 * (N - c1) ↔
      ((c1 : ℝ) / N - c11 / N) ^ 2 ≤ pOf (1 / 2) ^ 2 * (c1 / N * (1 - c1 / N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [pHalf_sq]
  have e1 : ((c1 : ℝ) / N - c11 / N) ^ 2 = (c1 - c11) ^ 2 / N ^ 2 := by field_simp
  have e2 : (1 / 2 : ℝ) * (c1 / N * (1 - c1 / N)) = c1 * (N - c1) / (2 * N ^ 2) := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith [pow_pos hNr 2]

/-! ### Spot check and bit widths (§8) -/

/-- At `count1 = 1152`, `H = 0.9` the integer accept window is
`542 ≤ count11 ≤ 617`. -/
theorem spot_check (c11 : ℤ) :
    (4096 * c11 ≤ 5997 * 1152 - 4378022 ∧ 4096 * c11 ≤ 2194 * 1152 ∧ 1152 - 610 ≤ c11) ↔
      542 ≤ c11 ∧ c11 ≤ 617 := by omega

/-- A 25-bit two's-complement comparison covers every row: for counts up to
`N = 2303`, both sides of AB and BC lie in `[-2²⁴, 2²⁴)`. -/
theorem bitwidth_25 (A1 A0 B1 c1 c11 : ℤ) (hA1 : 0 ≤ A1 ∧ A1 ≤ 5997)
    (hA0 : 0 ≤ A0 ∧ A0 ≤ 4378022) (hB1 : 0 ≤ B1 ∧ B1 ≤ 3821)
    (h1 : 0 ≤ c1 ∧ c1 ≤ 2303) (h11 : 0 ≤ c11 ∧ c11 ≤ 2303) :
    (-2 ^ 24 ≤ 4096 * c11 ∧ 4096 * c11 < 2 ^ 24) ∧
    (-2 ^ 24 ≤ A1 * c1 - A0 ∧ A1 * c1 - A0 < 2 ^ 24) ∧
    (-2 ^ 24 ≤ B1 * c1 ∧ B1 * c1 < 2 ^ 24) := by
  refine ⟨⟨by omega, by omega⟩, ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- The bitwidth column of Table 3 is one bit short for a signed comparison:
in every row `-A₀ < -2^(BW-1)`, the most negative `BW`-bit two's-complement
value, while `A₀ ≤ 2^BW`. The generator listing (`ceil(log2(A0)) + 1`) gives the
correct widths 21, 22, 22, 23, 23, 23, 23, 23, 24. -/
theorem bitwidth_column :
    (2 ^ 19 < (631706 : ℕ) ∧ 631706 ≤ 2 ^ 20) ∧ (2 ^ 20 < (1221108 : ℕ) ∧ 1221108 ≤ 2 ^ 21) ∧
    (2 ^ 20 < (1771040 : ℕ) ∧ 1771040 ≤ 2 ^ 21) ∧ (2 ^ 21 < (2284145 : ℕ) ∧ 2284145 ≤ 2 ^ 22) ∧
    (2 ^ 21 < (2762888 : ℕ) ∧ 2762888 ≤ 2 ^ 22) ∧ (2 ^ 21 < (3209571 : ℕ) ∧ 3209571 ≤ 2 ^ 22) ∧
    (2 ^ 21 < (3626342 : ℕ) ∧ 3626342 ≤ 2 ^ 22) ∧ (2 ^ 21 < (4015202 : ℕ) ∧ 4015202 ≤ 2 ^ 22) ∧
    (2 ^ 22 < (4378022 : ℕ) ∧ 4378022 ≤ 2 ^ 23) := by norm_num

/-- §9 bit widths: `2¹²(count1 - count11)²` fits in 35 bits, and
`P₂ · count1 · (N - count1)` in 33 bits for every `P₂ ≤ 4096`. -/
theorem arc_bitwidth (c1 c11 P2 : ℤ) (h1 : 0 ≤ c1 ∧ c1 ≤ 2303) (h11 : 0 ≤ c11 ∧ c11 ≤ 2303)
    (hP : 0 ≤ P2 ∧ P2 ≤ 4096) :
    4096 * (c1 - c11) ^ 2 < 2 ^ 35 ∧ P2 * c1 * (2303 - c1) < 2 ^ 33 := by
  have hq : c1 * (2303 - c1) ≤ 1325952 := by nlinarith [sq_nonneg (2 * c1 - 2303)]
  have hq0 : 0 ≤ c1 * (2303 - c1) := mul_nonneg h1.1 (by linarith)
  constructor
  · have : (c1 - c11) ^ 2 ≤ 2303 ^ 2 := by nlinarith
    nlinarith
  · calc P2 * c1 * (2303 - c1) = P2 * (c1 * (2303 - c1)) := by ring
      _ ≤ 4096 * 1325952 := mul_le_mul hP.2 hq hq0 (by norm_num)
      _ < 2 ^ 33 := by norm_num

end
end Polygon
