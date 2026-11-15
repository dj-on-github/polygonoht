import PolygonLean.Counts

/-!
# The exact polygon-test boundary

Formalizes Sections 3–7 of *An Exact Analytic Derivation of the Polygon Test
Boundary for Online Min-Entropy Testing of Binary Data*:

* the min-entropy rate in count coordinates and its agreement with the Markov
  model (Eq. (2));
* the region `R_H = {H∞ ≥ H}` as an intersection of constraints (§4);
* the curved edge is the lower branch of an ellipse, and is convex (Prop. 1);
* all corners, their uniqueness, and the discarded roots (§5.1);
* the regime condition `p ≥ 1/φ ⇔ H ≤ log₂ φ` (§5);
* the slope-1 chord, its intercepts, and that it lies above the arc (§6);
* soundness of the linear tests in both regimes: passing the tests implies
  `H∞ ≥ H`.
-/

open Real Set

namespace Polygon

noncomputable section

/-! ### The min-entropy rate in count coordinates -/

/-- Eq. (2): the asymptotic min-entropy rate as a function of `x = pc1`,
`y = pc11`. -/
def Hinf (x y : ℝ) : ℝ :=
  -logb 2 (max (max (y / x) ((1 - 2 * x + y) / (1 - x))) ((x - y) / √(x * (1 - x))))

/-- In the model's coordinates `x = μ`, `y = μP₁₁`, Eq. (2) is exactly the
asymptotic rate `-log₂ max(P₁₁, P₀₀, √(P₀₁P₁₀))` of `Markov.minEntropy_tendsto`. -/
theorem Hinf_model (M : Markov) : Hinf M.xc M.yc = M.entropyRate := by
  obtain ⟨h11, -, -, h00⟩ := M.inverse_map
  have halt : (M.xc - M.yc) / √(M.xc * (1 - M.xc)) = √(M.p01 * M.p10) := by
    have hs : M.xc - M.yc = M.mu * M.p10 := by simp only [Markov.xc, Markov.yc, Markov.p11]; ring
    have hx : 0 < M.xc * (1 - M.xc) := mul_pos M.mu_pos (sub_pos.mpr M.mu_lt_one)
    have hq : 0 ≤ (M.xc - M.yc) / √(M.xc * (1 - M.xc)) := by
      rw [hs]; exact div_nonneg (mul_nonneg M.mu_pos.le M.p10_pos.le) (Real.sqrt_nonneg _)
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (mul_nonneg M.p01_pos.le M.p10_pos.le) hq,
      div_mul_div_comm, Real.mul_self_sqrt hx.le, hs]
    simp only [Markov.xc, Markov.mu]
    have := M.sum_pos.ne'
    rw [eq_div_iff (by rw [← Markov.mu]; exact hx.ne')]
    field_simp; ring
  rw [Hinf, ← h11, ← h00, halt]; rfl

/-! ### The region -/

/-- The parameter-feasible part of the count plane: `0 < x < 1`,
`P₁₁ ≥ 0` (`y ≥ 0`), `P₁₀ ≥ 0` (`y ≤ x`) and `P₀₁ ≤ 1` (`y ≥ 2x - 1`). -/
structure Feasible (x y : ℝ) : Prop where
  x_pos : 0 < x
  x_lt_one : x < 1
  y_nonneg : 0 ≤ y
  y_le_x : y ≤ x
  cd : 2 * x - 1 ≤ y

/-- The three entropy constraints of §4 for a threshold `p = 2^{-H}`:
`P₀₀ ≤ p` (AB), `P₁₁ ≤ p` (BC) and `√(P₀₁P₁₀) ≤ p` (the ellipse). -/
def InRegion (p x y : ℝ) : Prop :=
  y ≤ (2 - p) * x - (1 - p) ∧ y ≤ p * x ∧ (x - y) ^ 2 ≤ p ^ 2 * (x * (1 - x))

/-- `p = 2^{-H}`. -/
def pOf (H : ℝ) : ℝ := (2 : ℝ) ^ (-H)

lemma pOf_pos (H : ℝ) : 0 < pOf H := Real.rpow_pos_of_pos (by norm_num) _

/-- **§4.** On the feasible set, `H∞(x, y) ≥ H` exactly when the three entropy
constraints hold. -/
theorem Hinf_ge_iff {x y : ℝ} (hf : Feasible x y) (H : ℝ) :
    H ≤ Hinf x y ↔ InRegion (pOf H) x y := by
  obtain ⟨hx0, hx1, hy0, hyx, -⟩ := hf
  have h1x : 0 < 1 - x := by linarith
  have hs : 0 < √(x * (1 - x)) := Real.sqrt_pos.mpr (mul_pos hx0 h1x)
  have hp := pOf_pos H
  set m := max (max (y / x) ((1 - 2 * x + y) / (1 - x))) ((x - y) / √(x * (1 - x)))
  have hm : 0 < m := by
    rcases hyx.lt_or_eq with h | h
    · exact lt_of_lt_of_le (div_pos (by linarith) hs) (le_max_right _ _)
    · refine lt_of_lt_of_le ?_ (le_trans (le_max_left _ _) (le_max_left _ _))
      rw [h, div_self hx0.ne']; norm_num
  rw [Hinf, le_neg, Real.logb_le_iff_le_rpow (by norm_num) hm, ← pOf]
  simp only [m, max_le_iff, InRegion]
  rw [div_le_iff₀ hx0, div_le_iff₀ h1x, div_le_iff₀ hs]
  have e : (x - y ≤ pOf H * √(x * (1 - x))) ↔ (x - y) ^ 2 ≤ pOf H ^ 2 * (x * (1 - x)) := by
    rw [← pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (mul_pos hx0 h1x).le]
  rw [e]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-- The region shrinks as `p` decreases (§7.3, "monotonically stricter"): on
`0 ≤ x ≤ 1`, every constraint for `p'` implies the one for any `p ≥ p' > 0`. -/
theorem InRegion.mono {p p' x y : ℝ} (h : InRegion p' x y) (hp' : 0 ≤ p') (hpp : p' ≤ p)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : InRegion p x y := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by nlinarith, by nlinarith, le_trans h3 ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp' hpp 2) (mul_nonneg hx0 (by linarith))

/-- The regions are nested (Fig. 5): raising the threshold `H` shrinks the region. -/
theorem region_nested {H H' x y : ℝ} (hH : H ≤ H') (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (h : InRegion (pOf H') x y) : InRegion (pOf H) x y :=
  h.mono (pOf_pos _).le (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) hx0 hx1

/-- The `0 ↔ 1` complement symmetry `(x, y) ↦ (1 - x, 1 - 2x + y)` swaps the
AB and BC constraints and fixes the ellipse. -/
theorem InRegion.complement {p x y : ℝ} :
    InRegion p x y ↔ InRegion p (1 - x) (1 - 2 * x + y) := by
  simp only [InRegion]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, ?_⟩
    calc (1 - x - (1 - 2 * x + y)) ^ 2 = (x - y) ^ 2 := by ring
      _ ≤ p ^ 2 * (x * (1 - x)) := h3
      _ = p ^ 2 * ((1 - x) * (1 - (1 - x))) := by ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, ?_⟩
    calc (x - y) ^ 2 = (1 - x - (1 - 2 * x + y)) ^ 2 := by ring
      _ ≤ p ^ 2 * ((1 - x) * (1 - (1 - x))) := h3
      _ = p ^ 2 * (x * (1 - x)) := by ring

/-! ### Proposition 1: the curved edge is an ellipse arc -/

/-- The ellipse constraint expands to the conic
`(1+p²)x² - 2xy + y² - p²x ≤ 0`. -/
theorem ellipse_expand (p x y : ℝ) :
    (x - y) ^ 2 - p ^ 2 * (x * (1 - x)) = (1 + p ^ 2) * x ^ 2 - 2 * x * y + y ^ 2 - p ^ 2 * x := by
  ring

/-- Its discriminant `B² - 4AC = 4 - 4(1+p²) = -4p²` is negative: an ellipse. -/
theorem ellipse_discriminant {p : ℝ} (hp : p ≠ 0) :
    (-2 : ℝ) ^ 2 - 4 * (1 + p ^ 2) * 1 = -4 * p ^ 2 ∧ (-2 : ℝ) ^ 2 - 4 * (1 + p ^ 2) * 1 < 0 := by
  constructor
  · ring
  · have := pow_pos (abs_pos.mpr hp) 2
    rw [sq_abs] at this; nlinarith

/-- Eq. (3): the lower branch of the ellipse. -/
def yArc (p x : ℝ) : ℝ := x - p * √(x * (1 - x))

/-- Below the diagonal `y ≤ x`, the ellipse constraint is `y ≥ y_arc(x)`. -/
theorem ellipse_iff_arc {p x y : ℝ} (hp : 0 ≤ p) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyx : y ≤ x) :
    (x - y) ^ 2 ≤ p ^ 2 * (x * (1 - x)) ↔ yArc p x ≤ y := by
  have hq : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have e : (x - y ≤ p * √(x * (1 - x))) ↔ (x - y) ^ 2 ≤ p ^ 2 * (x * (1 - x)) := by
    rw [← pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt hq]
  rw [yArc, ← e]
  constructor <;> intro h <;> linarith

/-- `x(1 - x)` is concave. -/
lemma concaveOn_quad : ConcaveOn ℝ univ (fun x : ℝ => x * (1 - x)) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul]
  have : t = 1 - s := by linarith
  subst this
  nlinarith [mul_nonneg hs ht, sq_nonneg (a - b)]

/-- `√(x(1 - x))` is concave on `[0, 1]`. -/
lemma concaveOn_sqrt_quad : ConcaveOn ℝ (Icc 0 1) (fun x : ℝ => √(x * (1 - x))) := by
  refine ⟨convex_Icc 0 1, fun a ha b hb s t hs ht hst => ?_⟩
  have qa : a * (1 - a) ∈ Ici (0 : ℝ) := mul_nonneg ha.1 (by linarith [ha.2])
  have qb : b * (1 - b) ∈ Ici (0 : ℝ) := mul_nonneg hb.1 (by linarith [hb.2])
  have h1 := concaveOn_quad.2 (mem_univ a) (mem_univ b) hs ht hst
  have h2 := Real.strictConcaveOn_sqrt.concaveOn.2 qa qb hs ht hst
  simp only [smul_eq_mul] at h1 h2 ⊢
  exact h2.trans (Real.sqrt_le_sqrt h1)

/-- **Proposition 1.** The arc `y = x - p√(x(1-x))` is convex on `[0, 1]`. -/
theorem yArc_convex {p : ℝ} (hp : 0 ≤ p) : ConvexOn ℝ (Icc 0 1) (yArc p) := by
  have h1 : ConvexOn ℝ (Icc 0 1) (fun x : ℝ => x) := convexOn_id (convex_Icc 0 1)
  have h2 : ConcaveOn ℝ (Icc 0 1) (fun x : ℝ => p * √(x * (1 - x))) := by
    simpa [smul_eq_mul] using concaveOn_sqrt_quad.smul hp
  exact h1.sub h2

/-! ### §5.1 Corners

Throughout, `0 < p < 1`. -/

/-- The boundary lines. -/
def lAB (p x : ℝ) : ℝ := (2 - p) * x - (1 - p)
def lBC (p x : ℝ) : ℝ := p * x
def lCD (x : ℝ) : ℝ := 2 * x - 1

/-- `Δ = (1-p)² + p²`. -/
def Δ (p : ℝ) : ℝ := (1 - p) ^ 2 + p ^ 2

def xA (p : ℝ) : ℝ := (1 - p) / (2 - p)
def xC (p : ℝ) : ℝ := 1 / (2 - p)
def xD (p : ℝ) : ℝ := 1 / (1 + p ^ 2)
def xE (p : ℝ) : ℝ := p ^ 2 / (1 + p ^ 2)
def xA' (p : ℝ) : ℝ := (1 - p) ^ 2 / Δ p
def xC' (p : ℝ) : ℝ := p ^ 2 / Δ p

section corners
-- Every result in this section is stated under the paper's standing assumption `0 < p < 1`.
set_option linter.unusedSectionVars false
variable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

lemma two_sub_pos : 0 < 2 - p := by linarith
lemma Δ_pos : 0 < Δ p := by unfold Δ; positivity

/-- Corner `A = ((1-p)/(2-p), 0)` on AB ∩ {y = 0}. -/
theorem cornerA : lAB p (xA p) = 0 := by
  have := two_sub_pos hp0 hp1
  unfold lAB xA; field_simp; ring

/-- Corner `B = (1/2, p/2)` on AB ∩ BC, and it is the only intersection. -/
theorem cornerB : lAB p (1 / 2) = p / 2 ∧ lBC p (1 / 2) = p / 2 := by
  unfold lAB lBC; constructor <;> ring

theorem cornerB_unique {x : ℝ} (h : lAB p x = lBC p x) : x = 1 / 2 := by
  unfold lAB lBC at h
  have : 2 * (1 - p) * x = 1 - p := by linarith
  have h1 : (1 - p) ≠ 0 := by linarith
  field_simp; nlinarith [mul_left_cancel₀ h1 (show (1 - p) * (2 * x) = (1 - p) * 1 by linarith)]

/-- Corner `C = (1/(2-p), p/(2-p))` on BC ∩ CD. -/
theorem cornerC : lBC p (xC p) = p / (2 - p) ∧ lCD (xC p) = p / (2 - p) := by
  have := two_sub_pos hp0 hp1
  unfold lBC lCD xC; constructor <;> field_simp; ring

lemma sqrt_E : √(xE p * (1 - xE p)) = p / (1 + p ^ 2) := by
  rw [show xE p * (1 - xE p) = (p / (1 + p ^ 2)) ^ 2 by unfold xE; field_simp; ring]
  exact Real.sqrt_sq (by positivity)

lemma sqrt_D : √(xD p * (1 - xD p)) = p / (1 + p ^ 2) := by
  rw [show xD p * (1 - xD p) = (p / (1 + p ^ 2)) ^ 2 by unfold xD; field_simp; ring]
  exact Real.sqrt_sq (by positivity)

lemma sqrt_A' : √(xA' p * (1 - xA' p)) = p * (1 - p) / Δ p := by
  have := Δ_pos hp0 hp1
  rw [show xA' p * (1 - xA' p) = (p * (1 - p) / Δ p) ^ 2 by unfold xA' Δ at *; field_simp; ring]
  exact Real.sqrt_sq (div_nonneg (mul_nonneg hp0.le (by linarith)) this.le)

lemma sqrt_C' : √(xC' p * (1 - xC' p)) = p * (1 - p) / Δ p := by
  have := Δ_pos hp0 hp1
  rw [show xC' p * (1 - xC' p) = (p * (1 - p) / Δ p) ^ 2 by unfold xC' Δ at *; field_simp; ring]
  exact Real.sqrt_sq (div_nonneg (mul_nonneg hp0.le (by linarith)) this.le)

/-- Corner `E = (p²/(1+p²), 0)`: the arc meets the axis. -/
theorem cornerE : yArc p (xE p) = 0 := by
  rw [yArc, sqrt_E hp0 hp1]; unfold xE; field_simp; ring

/-- Corner `D = (1/(1+p²), (1-p²)/(1+p²))`: the arc meets CD. -/
theorem cornerD : yArc p (xD p) = lCD (xD p) ∧ lCD (xD p) = (1 - p ^ 2) / (1 + p ^ 2) := by
  rw [yArc, sqrt_D hp0 hp1]; unfold xD lCD; constructor <;> field_simp <;> ring

/-- Corner `C' = (p²/Δ, p³/Δ)`: the arc meets BC. -/
theorem cornerC' : yArc p (xC' p) = lBC p (xC' p) ∧ lBC p (xC' p) = p ^ 3 / Δ p := by
  have := Δ_pos hp0 hp1
  rw [yArc, sqrt_C' hp0 hp1]; unfold xC' lBC Δ at *; constructor <;> (field_simp; try ring)

/-- Corner `A' = ((1-p)²/Δ, (1-p)(1-p-p²)/Δ)`: the arc meets AB. -/
theorem cornerA' : yArc p (xA' p) = lAB p (xA' p) ∧
    lAB p (xA' p) = (1 - p) * (1 - p - p ^ 2) / Δ p := by
  have := Δ_pos hp0 hp1
  rw [yArc, sqrt_A' hp0 hp1]; unfold xA' lAB Δ at *; constructor <;> (field_simp; try ring)

/-! Each line–arc corner is the only root apart from the discarded one at
`x = 0` or `x = 1`. -/

theorem cornerE_unique {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (h : yArc p x = 0) : x = xE p := by
  have hq : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
  have h1 : x = p * √(x * (1 - x)) := by unfold yArc at h; linarith
  have h2 : x ^ 2 = p ^ 2 * (x * (1 - x)) := by
    calc x ^ 2 = (p * √(x * (1 - x))) ^ 2 := by rw [← h1]
      _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
  have h3 : x * ((1 + p ^ 2) * x - p ^ 2) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · unfold xE; field_simp; linarith

theorem cornerD_unique {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (h : yArc p x = lCD x) : x = xD p := by
  have hq : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have h1 : 1 - x = p * √(x * (1 - x)) := by unfold yArc lCD at h; linarith
  have h2 : (1 - x) ^ 2 = p ^ 2 * (x * (1 - x)) := by
    calc (1 - x) ^ 2 = (p * √(x * (1 - x))) ^ 2 := by rw [← h1]
      _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
  have h3 : (1 - x) * (1 - (1 + p ^ 2) * x) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · unfold xD; field_simp; linarith

theorem cornerC'_unique {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (h : yArc p x = lBC p x) :
    x = xC' p := by
  have := Δ_pos hp0 hp1
  have hq : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
  have h1 : (1 - p) * x = p * √(x * (1 - x)) := by unfold yArc lBC at h; linarith
  have h2 : ((1 - p) * x) ^ 2 = p ^ 2 * (x * (1 - x)) := by
    calc ((1 - p) * x) ^ 2 = (p * √(x * (1 - x))) ^ 2 := by rw [← h1]
      _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
  have h3 : x * (Δ p * x - p ^ 2) = 0 := by unfold Δ; linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · unfold xC'; field_simp; linarith

theorem cornerA'_unique {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (h : yArc p x = lAB p x) :
    x = xA' p := by
  have := Δ_pos hp0 hp1
  have hq : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have h1 : (1 - p) * (1 - x) = p * √(x * (1 - x)) := by unfold yArc lAB at h; linarith
  have h2 : ((1 - p) * (1 - x)) ^ 2 = p ^ 2 * (x * (1 - x)) := by
    calc ((1 - p) * (1 - x)) ^ 2 = (p * √(x * (1 - x))) ^ 2 := by rw [← h1]
      _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
  have h3 : (1 - x) * (Δ p * x - (1 - p) ^ 2) = 0 := by unfold Δ; linear_combination -h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · unfold xA'; field_simp; linarith

/-! The discarded roots are not corners: next to them the arc is infeasible. -/

/-- On `0 < x < x_E` the arc lies below the axis. -/
theorem arc_neg_of_lt_xE {x : ℝ} (hx0 : 0 < x) (hx : x < xE p) : yArc p x < 0 := by
  have hx1 : x < 1 := lt_trans hx (by unfold xE; rw [div_lt_one (by positivity)]; linarith)
  have hq : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hlt : x * (1 + p ^ 2) < p ^ 2 := by unfold xE at hx; rwa [lt_div_iff₀ (by positivity)] at hx
  unfold yArc
  have : x < p * √(x * (1 - x)) := by
    rw [← pow_lt_pow_iff_left₀ hx0.le (by positivity) two_ne_zero, mul_pow, Real.sq_sqrt hq.le]
    nlinarith
  linarith

/-- On `x_D < x < 1` the arc lies below the line `y = 2x - 1`. -/
theorem arc_lt_lCD_of_xD_lt {x : ℝ} (hx : xD p < x) (hx1 : x < 1) : yArc p x < lCD x := by
  have hx0 : 0 < x := lt_trans (by unfold xD; positivity) hx
  have hq : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hlt : 1 < x * (1 + p ^ 2) := by unfold xD at hx; rwa [div_lt_iff₀ (by positivity)] at hx
  unfold yArc lCD
  have : 1 - x < p * √(x * (1 - x)) := by
    rw [← pow_lt_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt hq.le]
    nlinarith
  linarith

/-- The pairs of corners are symmetric about `x = 1/2`. -/
theorem corner_symmetry : xA p + xC p = 1 ∧ xE p + xD p = 1 ∧ xA' p + xC' p = 1 := by
  have := two_sub_pos hp0 hp1
  have := Δ_pos hp0 hp1
  refine ⟨?_, ?_, ?_⟩
  · unfold xA xC; field_simp; ring
  · unfold xE xD; field_simp; ring
  · unfold xA' xC'; field_simp; unfold Δ; ring

/-! ### The regime condition -/

/-- On the axis the region is `x_A ≤ x ≤ x_E`; it is nonempty exactly when
`1 - p - p² ≤ 0`. -/
theorem xA_le_xE_iff : xA p ≤ xE p ↔ 1 - p - p ^ 2 ≤ 0 := by
  have := two_sub_pos hp0 hp1
  unfold xA xE
  rw [div_le_div_iff₀ this (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The CD edge exists under the same condition. -/
theorem xD_le_xC_iff : xD p ≤ xC p ↔ 1 - p - p ^ 2 ≤ 0 := by
  obtain ⟨h1, h2, -⟩ := corner_symmetry hp0 hp1
  rw [← xA_le_xE_iff hp0 hp1]; constructor <;> intro h <;> linarith

/-- The height of `A'` is positive exactly in the triangle regime. -/
theorem yA'_pos_iff : 0 < lAB p (xA' p) ↔ 0 < 1 - p - p ^ 2 := by
  rw [(cornerA' hp0 hp1).2]
  have := Δ_pos hp0 hp1
  constructor
  · intro h
    have := (div_pos_iff_of_pos_right this).mp h
    exact pos_of_mul_pos_right this (by linarith)
  · intro h; exact div_pos (mul_pos (by linarith) h) this

/-- At the transition `p² = 1 - p` the corners `A`, `E`, `A'` coincide
(and so, by symmetry, do `C`, `D`, `C'`). -/
theorem transition_coincide (h : p ^ 2 = 1 - p) :
    xA p = xE p ∧ xA' p = xE p ∧ lAB p (xA' p) = 0 := by
  have := two_sub_pos hp0 hp1
  have := Δ_pos hp0 hp1
  refine ⟨?_, ?_, ?_⟩
  · unfold xA xE; rw [div_eq_div_iff (by linarith) (by positivity)]; nlinarith
  · unfold xA' xE; rw [div_eq_div_iff this.ne' (by positivity)]; unfold Δ; nlinarith
  · rw [(cornerA' hp0 hp1).2]; rw [show 1 - p - p ^ 2 = 0 by linarith]; simp

/-- Apex `B` satisfies the arc constraint iff `p ≥ 1/2`, i.e. for all `H ≤ 1`. -/
theorem apexB_in_iff : (1 / 2 - p / 2) ^ 2 ≤ p ^ 2 * (1 / 2 * (1 - 1 / 2)) ↔ 1 / 2 ≤ p := by
  constructor <;> intro h <;> nlinarith

/-! ### Cross-check in Markov parameters

Each corner is the image of a pair of active Markov constraints under
`x = P₀₁/(P₀₁+P₁₀)`, `y = x(1 - P₁₀)`. -/

/-- The count coordinates of transition probabilities `(a, b) = (P₀₁, P₁₀)`. -/
def toXY (a b : ℝ) : ℝ × ℝ := (a / (a + b), a / (a + b) * (1 - b))

theorem markov_corners :
    toXY (1 - p) 1 = (xA p, 0) ∧
    toXY (1 - p) (1 - p) = (1 / 2, p / 2) ∧
    toXY 1 (1 - p) = (xC p, p / (2 - p)) ∧
    toXY 1 (p ^ 2) = (xD p, (1 - p ^ 2) / (1 + p ^ 2)) ∧
    toXY (p ^ 2) 1 = (xE p, 0) ∧
    toXY (1 - p) (p ^ 2 / (1 - p)) = (xA' p, (1 - p) * (1 - p - p ^ 2) / Δ p) ∧
    toXY (p ^ 2 / (1 - p)) (1 - p) = (xC' p, p ^ 3 / Δ p) := by
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : (2 - p) ≠ 0 := by linarith
  have hd := (Δ_pos hp0 hp1).ne'
  have hd' : (1 - p) ^ 2 + p ^ 2 ≠ 0 := hd
  have h3 : 1 - p + 1 ≠ 0 := by linarith
  have h4 : 1 - p + (1 - p) ≠ 0 := by linarith
  have h5 : 1 + (1 - p) ≠ 0 := by linarith
  have h6 : 1 + p ^ 2 ≠ 0 := by positivity
  have h7 : p ^ 2 + 1 ≠ 0 := by positivity
  have h8 : 1 - p + p ^ 2 / (1 - p) = Δ p / (1 - p) := by unfold Δ; field_simp; try ring
  have h9 : p ^ 2 / (1 - p) + (1 - p) = Δ p / (1 - p) := by unfold Δ; field_simp; try ring
  simp only [toXY, xA, xC, xD, xE, xA', xC', Prod.mk.injEq, h8, h9]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    ((try field_simp); try ring)
  all_goals trivial

/-- At `A'` the remaining parameter `P₁₀ = p²/(1-p)` is a probability exactly when
`p² + p - 1 ≤ 0`: the regime boundary again. -/
theorem A'_feasible_iff : p ^ 2 / (1 - p) ≤ 1 ↔ p ^ 2 + p - 1 ≤ 0 := by
  rw [div_le_one (by linarith)]; constructor <;> intro h <;> linarith

end corners

/-! ### The golden-ratio threshold -/

/-- `p² + p - 1 ≥ 0 ⇔ p ≥ 1/φ` for `p > 0`. -/
theorem quad_nonneg_iff {p : ℝ} (hp : 0 < p) : 0 ≤ p ^ 2 + p - 1 ↔ goldenRatio⁻¹ ≤ p := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 2 < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hinv : goldenRatio⁻¹ = (√5 - 1) / 2 := by
    rw [goldenRatio, inv_div, div_eq_div_iff (by positivity) (by norm_num)]; nlinarith
  rw [hinv]
  have e : p ^ 2 + p - 1 = (p - (√5 - 1) / 2) * (p + (√5 + 1) / 2) := by nlinarith
  rw [e]
  have : 0 < p + (√5 + 1) / 2 := by positivity
  constructor
  · intro h; by_contra h'; push Not at h'; nlinarith
  · intro h; exact mul_nonneg (by linarith) this.le

/-- **The regime threshold.** `p = 2^{-H} ≥ 1/φ ⇔ H ≤ H* = log₂ φ`. -/
theorem regime_iff (H : ℝ) : goldenRatio⁻¹ ≤ pOf H ↔ H ≤ logb 2 goldenRatio := by
  have hφ : 0 < goldenRatio := by unfold goldenRatio; positivity
  rw [pOf, ← Real.logb_le_iff_le_rpow (by norm_num) (inv_pos.mpr hφ), Real.logb_inv]
  constructor <;> intro h <;> linarith

/-! ### §6 The slope-1 chord -/

/-- Chord intercept in the five-edge regime. -/
def c5 (p : ℝ) : ℝ := p ^ 2 / (1 + p ^ 2)
/-- Chord intercept in the triangle regime. -/
def c3 (p : ℝ) : ℝ := p ^ 2 * (1 - p) / Δ p

section chord
set_option linter.unusedSectionVars false
variable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

/-- The chord `ED` has slope exactly 1 and intercept `c5`. -/
theorem chord5 : xE p - 0 = c5 p ∧ xD p - lCD (xD p) = c5 p ∧
    xD p - xE p = lCD (xD p) - 0 := by
  unfold xE xD lCD c5; refine ⟨by ring, ?_, ?_⟩ <;> field_simp <;> ring

/-- The chord `A'C'` has slope exactly 1 and intercept `c3`. -/
theorem chord3 : xA' p - lAB p (xA' p) = c3 p ∧ xC' p - lBC p (xC' p) = c3 p ∧
    xC' p - xA' p = lBC p (xC' p) - lAB p (xA' p) := by
  have := Δ_pos hp0 hp1
  unfold xA' xC' lAB lBC c3; refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> unfold Δ <;> ring

omit hp0 hp1 in
lemma sqrt_mono_between {a x : ℝ} (hax : a ≤ x) (hx : x ≤ 1 - a) :
    √(a * (1 - a)) ≤ √(x * (1 - x)) :=
  Real.sqrt_le_sqrt (by nlinarith)

/-- **The chord lies above the arc** on `[x_E, x_D]`, so `y ≥ x - c5` implies the
arc constraint there. -/
theorem chord5_above {x : ℝ} (h1 : xE p ≤ x) (h2 : x ≤ xD p) : yArc p x ≤ x - c5 p := by
  have hs := corner_symmetry hp0 hp1
  have hE : 0 ≤ xE p := by unfold xE; positivity
  have := sqrt_mono_between h1 (by linarith [hs.2.1])
  rw [sqrt_E hp0 hp1] at this
  unfold yArc c5
  have : p * (p / (1 + p ^ 2)) ≤ p * √(x * (1 - x)) := mul_le_mul_of_nonneg_left this hp0.le
  rw [show p ^ 2 / (1 + p ^ 2) = p * (p / (1 + p ^ 2)) by ring]; linarith

/-- The chord lies above the arc on `[x_A', x_C']`. -/
theorem chord3_above {x : ℝ} (h1 : xA' p ≤ x) (h2 : x ≤ xC' p) : yArc p x ≤ x - c3 p := by
  have hs := corner_symmetry hp0 hp1
  have hd := Δ_pos hp0 hp1
  have hA : 0 ≤ xA' p := by unfold xA'; positivity
  have := sqrt_mono_between h1 (by linarith [hs.2.2])
  rw [sqrt_A' hp0 hp1] at this
  unfold yArc c3
  have : p * (p * (1 - p) / Δ p) ≤ p * √(x * (1 - x)) := mul_le_mul_of_nonneg_left this hp0.le
  rw [show p ^ 2 * (1 - p) / Δ p = p * (p * (1 - p) / Δ p) by ring]; linarith

/-- The vertical gap between chord and arc is largest at `x = 1/2`, where it is
`p/2 - c`. (An earlier draft printed `c(H) - (1-p)/2`; the gap is
`(1/2 - c) - (1-p)/2 = p/2 - c`, which is the quoted `≈ 0.014` at `H = 0.4`.) -/
theorem chord_gap_max (c x : ℝ) :
    (x - c) - yArc p x ≤ p / 2 - c ∧ (1 / 2 - c) - yArc p (1 / 2) = p / 2 - c := by
  constructor
  · unfold yArc
    have : √(x * (1 - x)) ≤ 1 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith [sq_nonneg (x - 1 / 2)]
    nlinarith
  · unfold yArc
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring

/-- §7.1: in the five-edge regime the chord meets `y = 0` at `x_E` and the CD
line at `x_D`, so the linear tests reproduce every corner exactly. -/
theorem chord5_perfect_fit : xE p - c5 p = 0 ∧ xD p - c5 p = lCD (xD p) := by
  obtain ⟨h1, h2, -⟩ := chord5 hp0 hp1
  constructor <;> linarith

/-- In the triangle regime the triangle chord is no stricter than the five-edge
one (`c5 ≤ c3`), so using `c3` does not lose any of the region. -/
theorem c5_le_c3 (h : p ^ 2 + p - 1 ≤ 0) : c5 p ≤ c3 p := by
  have := Δ_pos hp0 hp1
  unfold c5 c3
  rw [div_le_div_iff₀ (by positivity) this]
  have := mul_nonneg (pow_nonneg hp0.le 3) (by linarith : 0 ≤ 1 - p - p ^ 2)
  unfold Δ; nlinarith

/-! ### Soundness of the linear tests -/

/-- **Five-edge linear test is sound.** If `(x, y)` passes AB, BC, DC, the chord
`y ≥ x - c5` and `y ≥ 0`, then it is feasible and in the exact region, so
`H∞(x, y) ≥ H`. This holds for every `0 < p < 1`. -/
theorem linear5_sound {x y : ℝ} (hAB : y ≤ lAB p x) (hBC : y ≤ lBC p x) (hDC : lCD x ≤ y)
    (hED : x - c5 p ≤ y) (hy : 0 ≤ y) : Feasible x y ∧ InRegion p x y := by
  have h2p := two_sub_pos hp0 hp1
  unfold lAB lBC lCD at *
  have hx0 : 0 < x := by
    by_contra h; push Not at h; nlinarith
  have hx1 : x < 1 := by nlinarith
  have hyx : y ≤ x := by nlinarith
  refine ⟨⟨hx0, hx1, hy, hyx, hDC⟩, hAB, hBC, ?_⟩
  rw [ellipse_iff_arc hp0.le hx0.le hx1.le hyx]
  rcases lt_or_ge x (xE p) with h | h
  · exact (arc_neg_of_lt_xE hp0 hp1 hx0 h).le.trans hy
  rcases le_or_gt x (xD p) with h' | h'
  · exact (chord5_above hp0 hp1 h h').trans hED
  · exact (arc_lt_lCD_of_xD_lt hp0 hp1 h' hx1).le.trans hDC

/-- **Triangle linear test is sound.** In the triangle regime `p² + p - 1 ≤ 0`,
passing AB, BC and the chord `y ≥ x - c3` already implies feasibility and the
exact region; the DC and `y ≥ 0` tests are implied. -/
theorem linear3_sound (hreg : p ^ 2 + p - 1 ≤ 0) {x y : ℝ} (hAB : y ≤ lAB p x)
    (hBC : y ≤ lBC p x) (hED : x - c3 p ≤ y) : Feasible x y ∧ InRegion p x y := by
  have hd := Δ_pos hp0 hp1
  have h1p : 0 < 1 - p := by linarith
  -- the chord confines x to [x_A', x_C']
  have hc3 : c3 p = p ^ 2 * (1 - p) / Δ p := rfl
  have hxA : xA' p ≤ x := by
    have : (1 - p) * x ≥ (1 - p) - c3 p := by unfold lAB at hAB; linarith
    unfold xA'
    rw [div_le_iff₀ hd]
    rw [hc3] at this
    have e : (1 - p) * (x * Δ p) ≥ (1 - p) * (1 - p) ^ 2 := by
      have := mul_le_mul_of_nonneg_right this hd.le
      rw [sub_mul, div_mul_cancel₀ _ hd.ne'] at this
      unfold Δ at this ⊢; nlinarith
    exact le_of_mul_le_mul_left (by linarith) h1p
  have hxC : x ≤ xC' p := by
    have : (1 - p) * x ≤ c3 p := by unfold lBC at hBC; linarith
    unfold xC'
    rw [le_div_iff₀ hd]
    rw [hc3, le_div_iff₀ hd] at this
    exact le_of_mul_le_mul_left (by nlinarith) h1p
  have hs := corner_symmetry hp0 hp1
  have hA0 : 0 < xA' p := by unfold xA'; positivity
  have hx0 : 0 < x := lt_of_lt_of_le hA0 hxA
  have hx1 : x < 1 := lt_of_le_of_lt hxC (by linarith [hs.2.2])
  have hyx : y ≤ x := by unfold lBC at hBC; nlinarith
  -- y ≥ 0: the lowest point is A', whose height is ≥ 0 in this regime
  have hy0 : 0 ≤ y := by
    have h3 := (chord3 hp0 hp1).1
    have h4 : 0 ≤ lAB p (xA' p) := by
      rw [(cornerA' hp0 hp1).2]; exact div_nonneg (mul_nonneg h1p.le (by linarith)) hd.le
    linarith
  -- y ≥ 2x - 1: x ≤ x_C' ≤ 1 - c3
  have hDC : 2 * x - 1 ≤ y := by
    have : xC' p ≤ 1 - c3 p := by
      unfold xC'
      rw [hc3, div_le_iff₀ hd, sub_mul, div_mul_cancel₀ _ hd.ne']
      unfold Δ; nlinarith
    linarith
  refine ⟨⟨hx0, hx1, hy0, hyx, hDC⟩, hAB, hBC, ?_⟩
  rw [ellipse_iff_arc hp0.le hx0.le hx1.le hyx]
  exact (chord3_above hp0 hp1 hxA hxC).trans hED

end chord

/-- **End-to-end (five-edge).** For any threshold `0 < H`, the five linear tests
imply `H∞(x, y) ≥ H`. -/
theorem linear5_entropy {H x y : ℝ} (hH : 0 < H) (hAB : y ≤ lAB (pOf H) x)
    (hBC : y ≤ lBC (pOf H) x) (hDC : lCD x ≤ y) (hED : x - c5 (pOf H) ≤ y) (hy : 0 ≤ y) :
    H ≤ Hinf x y := by
  have hp1 : pOf H < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hf, hr⟩ := linear5_sound (pOf_pos H) hp1 hAB hBC hDC hED hy
  exact (Hinf_ge_iff hf H).mpr hr

/-- **End-to-end (triangle).** For `H ≥ log₂ φ`, the three linear tests imply
`H∞(x, y) ≥ H`. -/
theorem linear3_entropy {H x y : ℝ} (hH : logb 2 goldenRatio ≤ H) (hAB : y ≤ lAB (pOf H) x)
    (hBC : y ≤ lBC (pOf H) x) (hED : x - c3 (pOf H) ≤ y) : H ≤ Hinf x y := by
  have hφ : 0 < logb 2 goldenRatio := by
    apply Real.logb_pos (by norm_num)
    unfold goldenRatio
    have : 1 < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have hp0 := pOf_pos H
  have hp1 : pOf H < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hreg : pOf H ^ 2 + pOf H - 1 ≤ 0 := by
    rcases hH.lt_or_eq with h | h
    · have : ¬ goldenRatio⁻¹ ≤ pOf H := fun h' => absurd ((regime_iff H).mp h') (not_le.mpr h)
      have := (quad_nonneg_iff hp0).not.mpr this
      linarith [not_le.mp this]
    · have h1 : goldenRatio⁻¹ ≤ pOf H := (regime_iff H).mpr h.ge
      have h2 : pOf H ≤ goldenRatio⁻¹ := by
        rw [pOf, ← h]
        have hg : 0 < goldenRatio := by unfold goldenRatio; positivity
        rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hg]
      have := le_antisymm h2 h1
      have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have hinv : goldenRatio⁻¹ = (√5 - 1) / 2 := by
        rw [goldenRatio, inv_div, div_eq_div_iff (by positivity) (by norm_num)]; nlinarith
      rw [this, hinv]; nlinarith
  obtain ⟨hf, hr⟩ := linear3_sound hp0 hp1 hreg hAB hBC hED
  exact (Hinf_ge_iff hf H).mpr hr

end
end Polygon
