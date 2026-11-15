import PolygonLean.Markov

/-!
# Bit-pair counts

Formalizes Section 11 of the SPACE 2024 paper ("The SCC Equation Gives Another
Way to Count") and Section 2 of the follow-up paper ("Count Coordinates and the
Inverse Map").

For an `n`-bit block `l` there are `N = n - 1` bit-pair positions.
* `count1`  = number of 1s in the first `n - 1` bits,
* `cnt a b` = number of positions `i` with `(lᵢ, lᵢ₊₁) = (a, b)`.
-/

namespace Polygon

noncomputable section

/-- The `n - 1` overlapping bit pairs of a block. -/
def pairs (l : List Bool) : List (Bool × Bool) := l.zip l.tail

/-- Number of `(a, b)` bit pairs. `cnt true true` is `count11`. -/
def cnt (a b : Bool) (l : List Bool) : ℕ := (pairs l).count (a, b)

/-- Number of 1s in the first `n - 1` bits. -/
def count1 (l : List Bool) : ℕ := l.dropLast.count true
/-- Number of 0s in the first `n - 1` bits. -/
def count0 (l : List Bool) : ℕ := l.dropLast.count false

@[simp] lemma pairs_cons_cons (a b : Bool) (t : List Bool) :
    pairs (a :: b :: t) = (a, b) :: pairs (b :: t) := rfl

@[simp] lemma length_pairs (l : List Bool) : (pairs l).length = l.length - 1 := by
  simp [pairs]

lemma count_four (ps : List (Bool × Bool)) :
    ps.count (false, false) + ps.count (false, true) + ps.count (true, false) +
      ps.count (true, true) = ps.length := by
  induction ps with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    cases a <;> cases b <;> simp <;> omega

/-- `n - 1 = count00 + count01 + count10 + count11`. -/
theorem cnt_sum (l : List Bool) :
    cnt false false l + cnt false true l + cnt true false l + cnt true true l = l.length - 1 := by
  rw [← length_pairs]; exact count_four _

/-- Every 1 in the first `n - 1` bits starts a `10` or a `11` pair:
`count1 = count10 + count11`. -/
theorem count1_eq : ∀ l : List Bool, count1 l = cnt true false l + cnt true true l
  | [] => rfl
  | [_] => by simp [count1, cnt, pairs]
  | a :: b :: t => by
    have ih := count1_eq (b :: t)
    simp only [count1, cnt, pairs_cons_cons, List.dropLast_cons_cons, List.count_cons,
      beq_iff_eq, Prod.mk.injEq] at ih ⊢
    cases a <;> cases b <;> simp_all <;> omega

/-- Likewise `count0 = count00 + count01`. -/
theorem count0_eq : ∀ l : List Bool, count0 l = cnt false false l + cnt false true l
  | [] => rfl
  | [_] => by simp [count0, cnt, pairs]
  | a :: b :: t => by
    have ih := count0_eq (b :: t)
    simp only [count0, cnt, pairs_cons_cons, List.dropLast_cons_cons, List.count_cons,
      beq_iff_eq, Prod.mk.injEq] at ih ⊢
    cases a <;> cases b <;> simp_all <;> omega

/-- `count0 + count1 = N`. -/
theorem count0_add_count1 (l : List Bool) : count0 l + count1 l = l.length - 1 := by
  rw [count0_eq, count1_eq, ← cnt_sum]; ring

private def ind (b : Bool) : ℤ := if b then 1 else 0

/-- `count01 - count10 = last bit - first bit`. -/
theorem cnt01_sub_cnt10 : ∀ (a : Bool) (t : List Bool),
    (cnt false true (a :: t) : ℤ) - cnt true false (a :: t) =
      ind ((a :: t).getLast (by simp)) - ind a
  | a, [] => by simp [cnt, pairs]
  | a, b :: t => by
    have ih := cnt01_sub_cnt10 b t
    simp only [cnt, pairs_cons_cons, List.count_cons, beq_iff_eq, Prod.mk.injEq] at ih ⊢
    rw [List.getLast_cons (by simp)]
    cases a <;> cases b <;> simp_all [ind] <;> omega

/-- In non-cyclic data `count01` and `count10` differ by at most one. -/
theorem cnt01_cnt10_close (l : List Bool) :
    |(cnt false true l : ℤ) - cnt true false l| ≤ 1 := by
  match l with
  | [] => simp [cnt, pairs]
  | a :: t =>
    rw [cnt01_sub_cnt10]
    generalize (a :: t).getLast (by simp) = z
    cases a <;> cases z <;> simp [ind]

/-! ### SCC from counts (SPACE 2024, §11.1) -/

/-- The bits as real numbers `xᵢ ∈ {0, 1}`. -/
def toReal (b : Bool) : ℝ := if b then 1 else 0

/-- Knuth's serial correlation coefficient (Eq. (20)), made non-cyclic: over the
`N` bit pairs, with `Sxy = Σ xᵢxᵢ₊₁`, `Sx = Σ xᵢ`, `Sxx = Σ xᵢ²` taken over the
first `N` bits. -/
def knuthSCC (l : List Bool) : ℝ :=
  let N : ℝ := (l.length - 1 : ℕ)
  let Sxy := ((pairs l).map fun p => toReal p.1 * toReal p.2).sum
  let Sx := (l.dropLast.map toReal).sum
  let Sxx := (l.dropLast.map fun b => toReal b ^ 2).sum
  (N * Sxy - Sx ^ 2) / (N * Sxx - Sx ^ 2)

lemma sum_toReal (l : List Bool) : (l.map toReal).sum = l.count true := by
  induction l with
  | nil => simp
  | cons b t ih => cases b <;> simp [toReal, ih, add_comm]

lemma sum_toReal_sq (l : List Bool) : (l.map fun b => toReal b ^ 2).sum = l.count true := by
  rw [← sum_toReal]; congr 1; apply List.map_congr_left; intro b _; cases b <;> simp [toReal]

lemma sum_pair_prod (l : List Bool) :
    ((pairs l).map fun p => toReal p.1 * toReal p.2).sum = cnt true true l := by
  unfold cnt
  induction pairs l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.map_cons, List.sum_cons, ih]
    cases a <;> cases b <;> simp [toReal, add_comm]

/-- Eq. (21): for binary data the SCC is a function of `N`, `count1` and
`count11` alone: `SCC = (N·count11 - count1²)/(N·count1 - count1²)`. -/
theorem eq21 (l : List Bool) :
    knuthSCC l = (((l.length - 1 : ℕ) : ℝ) * cnt true true l - (count1 l : ℝ) ^ 2) /
      (((l.length - 1 : ℕ) : ℝ) * count1 l - (count1 l : ℝ) ^ 2) := by
  simp only [knuthSCC, sum_pair_prod, sum_toReal, sum_toReal_sq, count1]

/-- The normalized form: with `pc1 = count1/N`, `pc11 = count11/N`,
`SCC = (pc11 - pc1²)/(pc1 - pc1²)`. -/
theorem scc_normalized (N c1 c11 : ℝ) (hN : N ≠ 0) :
    (N * c11 - c1 ^ 2) / (N * c1 - c1 ^ 2) =
      (c11 / N - (c1 / N) ^ 2) / (c1 / N - (c1 / N) ^ 2) := by
  rcases eq_or_ne (N * c1 - c1 ^ 2) 0 with h | h
  · have h' : c1 / N - (c1 / N) ^ 2 = 0 := by
      rw [show c1 / N - (c1 / N) ^ 2 = (N * c1 - c1 ^ 2) / N ^ 2 by field_simp, h, zero_div]
    rw [h, h', div_zero, div_zero]
  · rw [show c11 / N - (c1 / N) ^ 2 = (N * c11 - c1 ^ 2) / N ^ 2 by field_simp,
        show c1 / N - (c1 / N) ^ 2 = (N * c1 - c1 ^ 2) / N ^ 2 by field_simp]
    rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hN)]

/-! ### Count coordinates and the inverse map (follow-up paper, §2) -/

namespace Markov
variable (M : Markov)

/-- The model's count coordinates: `x = Pr[xᵢ = 1] = μ`, `y = Pr[xᵢ = 1, xᵢ₊₁ = 1] = μP₁₁`. -/
def xc : ℝ := M.mu
def yc : ℝ := M.mu * M.p11

/-- The SCC computed from the count coordinates is the model's SCC, Eq. (12). -/
theorem scc_from_counts : (M.yc - M.xc ^ 2) / (M.xc - M.xc ^ 2) = M.scc := by
  have h := M.sum_pos.ne'
  have hd : M.xc - M.xc ^ 2 ≠ 0 := by
    have := mul_pos M.mu_pos (sub_pos.mpr M.mu_lt_one)
    simp only [xc]; intro h'; nlinarith
  rw [div_eq_iff hd]
  simp only [xc, yc, mu, p11, scc]
  field_simp; ring

/-- Eq. (1) of the follow-up paper: the transition probabilities from `(x, y)`. -/
theorem inverse_map :
    M.p11 = M.yc / M.xc ∧ M.p10 = 1 - M.yc / M.xc ∧
    M.p01 = (M.xc - M.yc) / (1 - M.xc) ∧ M.p00 = (1 - 2 * M.xc + M.yc) / (1 - M.xc) := by
  have h := M.sum_pos.ne'
  have hm := M.mu_pos.ne'
  have h1 : 1 - M.mu ≠ 0 := by linarith [M.mu_lt_one]
  simp only [xc, yc]
  refine ⟨by field_simp, by field_simp; simp [p11], ?_, ?_⟩
  · rw [eq_div_iff h1, one_sub_mu]; simp only [mu, p11]; field_simp; ring
  · rw [eq_div_iff h1, one_sub_mu]; simp only [mu, p11, p00]; field_simp; ring

end Markov

/-- The inverse map in counts. With `x = count1/N` and `y = count11/N`,
`x - y = count10/N` (exactly), `1 - x = count0/N`, and
`1 - 2x + y = (count00 + count01 - count10)/N`, which is within `1/N` of
`count00/N`. So `y/x = count11/count1`, `(x-y)/(1-x) = count10/count0`, and
`(1-2x+y)/(1-x)` is the empirical `P₀₀` to within one count. -/
theorem counts_inverse (l : List Bool) (hl : 2 ≤ l.length) :
    let N : ℝ := (l.length - 1 : ℕ)
    let x : ℝ := count1 l / N
    let y : ℝ := cnt true true l / N
    x - y = cnt true false l / N ∧ 1 - x = count0 l / N ∧
    1 - 2 * x + y = (cnt false false l + cnt false true l - (cnt true false l : ℝ)) / N := by
  intro N x y
  have hN : N ≠ 0 := by
    simp only [N]; have : 1 ≤ l.length - 1 := by omega
    exact_mod_cast (show l.length - 1 ≠ 0 by omega)
  have hsum : (N : ℝ) =
      cnt false false l + cnt false true l + cnt true false l + cnt true true l := by
    simp only [N]; rw [← cnt_sum]; push_cast; ring
  have h1 : (count1 l : ℝ) = cnt true false l + cnt true true l := by
    rw [count1_eq]; push_cast; ring
  have h0 : (count0 l : ℝ) = cnt false false l + cnt false true l := by
    rw [count0_eq]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [x, y]; rw [h1]; field_simp; ring
  · simp only [x]; rw [h0, h1]; field_simp; linarith
  · simp only [x, y]; rw [h1]; field_simp; linarith

end
end Polygon
