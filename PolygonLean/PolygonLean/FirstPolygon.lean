import PolygonLean.Integer

/-!
# The graphically extracted polygon of the SPACE 2024 paper

Formalizes Sections 12–13 of the SPACE 2024 paper: the `H = 0.4` polygon read
from the contour plot (Table 5), its four line equations, their integer forms
for `n = 2304`, the shift-add realisation and the 17-bit datapath. It then
compares this polygon with the exact region of the follow-up paper.
-/

open Real

namespace Polygon

namespace First

noncomputable section

/-- Table 5: the corners read from the plot. -/
def A : ℝ × ℝ := (0.2, 0)
def B : ℝ × ℝ := (0.5, 0.4)
def C : ℝ × ℝ := (0.8, 0.6)
def D : ℝ × ℝ := (0.6, 0.2)
def E : ℝ × ℝ := (0.4, 0)

/-- The four edges of §12. -/
def AB (x : ℝ) : ℝ := 4 / 3 * x - 4 / 15
def BC (x : ℝ) : ℝ := 2 / 3 * x + 1 / 15
def DC (x : ℝ) : ℝ := 2 * x - 1
def ED (x : ℝ) : ℝ := x - 0.4

/-- Each edge passes through its two corners. -/
theorem edges_through_corners :
    AB A.1 = A.2 ∧ AB B.1 = B.2 ∧ BC B.1 = B.2 ∧ BC C.1 = C.2 ∧
    DC D.1 = D.2 ∧ DC C.1 = C.2 ∧ ED E.1 = E.2 ∧ ED D.1 = D.2 := by
  simp only [AB, BC, DC, ED, A, B, C, D, E]; norm_num

/-- The polygon test of §12, in normalized coordinates. -/
def accepts (x y : ℝ) : Prop := y < AB x ∧ y < BC x ∧ DC x < y ∧ ED x < y

/-- Multiplying up to integer coefficients: `15y < 20x - 4`, `15y < 10x + 1`,
`y > 2x - 1`, `5y > 5x - 2`. -/
theorem accepts_iff_int (x y : ℝ) :
    accepts x y ↔
      15 * y < 20 * x - 4 ∧ 15 * y < 10 * x + 1 ∧ 2 * x - 1 < y ∧ 5 * x - 2 < 5 * y := by
  simp only [accepts, AB, BC, DC, ED]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨?_, ?_, h3, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨?_, ?_, h3, ?_⟩ <;> linarith

/-- The count form for a block of `n` bits (`N = n - 1`). -/
def acceptsCounts (N c1 c11 : ℤ) : Prop :=
  15 * c11 < 20 * c1 - 4 * N ∧ 15 * c11 < 10 * c1 + N ∧ 2 * c1 - N < c11 ∧ 5 * c1 - 2 * N < 5 * c11

theorem acceptsCounts_iff {N : ℕ} (hN : 0 < N) (c1 c11 : ℕ) :
    acceptsCounts N c1 c11 ↔ accepts ((c1 : ℝ) / N) ((c11 : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ a b : ℝ, a / N < b / N ↔ a < b := fun a b => div_lt_div_iff_of_pos_right hNr
  rw [accepts_iff_int, acceptsCounts]
  have e1 : 15 * ((c11 : ℝ) / N) = (15 * c11) / N := by ring
  have e2 : 20 * ((c1 : ℝ) / N) - 4 = (20 * c1 - 4 * N) / N := by field_simp
  have e3 : 10 * ((c1 : ℝ) / N) + 1 = (10 * c1 + N) / N := by field_simp
  have e4 : 2 * ((c1 : ℝ) / N) - 1 = (2 * c1 - N) / N := by field_simp
  have e5 : 5 * ((c1 : ℝ) / N) - 2 = (5 * c1 - 2 * N) / N := by field_simp
  have e6 : 5 * ((c11 : ℝ) / N) = (5 * c11) / N := by ring
  rw [e1, e2, e3, e4, e5, e6, key, key, key, key]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- For `n = 2304`: `4(n-1) = 9212`, `2(n-1) = 4606`. -/
theorem constants_2304 (c1 c11 : ℤ) :
    acceptsCounts 2303 c1 c11 ↔ 15 * c11 < 20 * c1 - 9212 ∧ 15 * c11 < 10 * c1 + 2303 ∧
      2 * c1 - 2303 < c11 ∧ 5 * c1 - 4606 < 5 * c11 := by
  simp only [acceptsCounts]; constructor <;> intro h <;> omega

/-- §12: the multiplications are shifts and adds. -/
theorem shift_add (X : ℕ) :
    2 * X = X <<< 1 ∧ 5 * X = (X <<< 2) + X ∧ 10 * X = (X <<< 3) + (X <<< 1) ∧
    15 * X = (X <<< 4) - X ∧ 20 * X = (X <<< 4) + (X <<< 2) := by
  simp only [Nat.shiftLeft_eq]; omega

/-- §13: with counts up to 2303 every intermediate value lies in `[-2¹⁶, 2¹⁶)`,
so 17-bit two's-complement arithmetic suffices. -/
theorem fits_17_bits (c1 c11 : ℤ) (h1 : 0 ≤ c1 ∧ c1 ≤ 2303) (h11 : 0 ≤ c11 ∧ c11 ≤ 2303) :
    (∀ v ∈ [15 * c11, 20 * c1 - 9212, 10 * c1 + 2303, 2 * c1 - 2303, 5 * c1 - 4606, 5 * c11],
      -2 ^ 16 ≤ v ∧ v < 2 ^ 16) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl | rfl | rfl | rfl) <;> constructor <;> omega

/-! ### Comparison with the exact region

The plotted polygon sits slightly outside the exact `H = 0.4` region (for
example the plotted apex `B = (0.5, 0.4)` lies above the exact apex
`(0.5, p/2) ≈ (0.5, 0.3789)`). So the graphical test accepts some data whose
min-entropy rate is below 0.4. -/

lemma p4_lt : pK 4 < 0.78 := by
  have := (pK_bounds 4 (lo := 0.757858283255199) (hi := 0.757858283255200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  linarith

/-- The point `(x, y) = (0.5, 0.39)` passes the SPACE 2024 polygon test but has
min-entropy rate below 0.4 (`P₁₁ = 0.78 > 2^{-0.4}`). -/
theorem not_conservative :
    accepts 0.5 0.39 ∧ Hinf 0.5 0.39 < 0.4 := by
  refine ⟨by simp only [accepts, AB, BC, DC, ED]; norm_num, ?_⟩
  have hf : Feasible 0.5 0.39 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  by_contra h
  push Not at h
  have h' : ((4 : ℕ) : ℝ) / 10 ≤ Hinf 0.5 0.39 := by norm_num; linarith
  have := ((Hinf_ge_iff hf _).mp h').2.1
  have hp := p4_lt
  simp only [pK] at hp
  linarith

/-- The same at the count level for `n = 2304`: `count1 = 1152`, `count11 = 898`
passes the integer polygon test of §12, but `P₁₁ = 898/1152 ≈ 0.7795 > 2^{-0.4}`,
so the min-entropy rate is below 0.4. -/
theorem not_conservative_counts :
    acceptsCounts 2303 1152 898 ∧ Hinf ((1152 : ℝ) / 2303) ((898 : ℝ) / 2303) < 0.4 := by
  refine ⟨by simp only [acceptsCounts]; norm_num, ?_⟩
  have hf : Feasible ((1152 : ℝ) / 2303) ((898 : ℝ) / 2303) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  by_contra h
  push Not at h
  have h' : ((4 : ℕ) : ℝ) / 10 ≤ Hinf ((1152 : ℝ) / 2303) ((898 : ℝ) / 2303) := by
    norm_num; linarith
  have := ((Hinf_ge_iff hf _).mp h').2.1
  have hp := (pK_bounds 4 (lo := 0.757858283255199) (hi := 0.757858283255200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  simp only [pK] at hp this
  linarith

end
end First
end Polygon
