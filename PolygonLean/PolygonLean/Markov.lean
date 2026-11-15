import Mathlib

/-!
# The two-state, two-parameter Markov bit generator

Formalizes Sections 2–6 of

  D. Johnston, *Online Testing Entropy and Entropy Tests with a Two State Markov
  Model*, SPACE 2024, LNCS 15351, pp. 110–128.

and Section 3 ("The Min-Entropy Rate in Closed Form") of the follow-up paper
*An Exact Analytic Derivation of the Polygon Test Boundary*.

Contents
* the model, Eqs. (1)–(2), and its stationary distribution;
* the (μ, SCC) ↔ (P₀₁, P₁₀) bijection, Eqs. (3)–(12);
* the symbol probability of Eq. (18) and the probabilities of the MCV
  candidates of Tables 3 and 4 (with the stationary prefactor μ or 1-μ);
* Eqs. (13)–(15);
* the asymptotic min-entropy rate theorem: the per-bit min-entropy of b-bit
  symbols converges to `-log₂ max(P₁₁, P₀₀, √(P₀₁P₁₀))` (Eq. (2) of the
  follow-up paper).
-/

open Real Filter Topology

namespace Polygon

noncomputable section

/-- A two-state Markov bit generator, parameterised by `p01 = P₀₁` (a 0 is
followed by a 1) and `p10 = P₁₀` (a 1 is followed by a 0). Both are taken to be
strictly positive so that the chain is irreducible and the mean is defined. -/
structure Markov where
  p01 : ℝ
  p10 : ℝ
  p01_pos : 0 < p01
  p01_le : p01 ≤ 1
  p10_pos : 0 < p10
  p10_le : p10 ≤ 1

namespace Markov

variable (M : Markov)

/-- Eq. (1): `P₀₁ + P₀₀ = 1`. -/
def p00 : ℝ := 1 - M.p01
/-- Eq. (2): `P₁₀ + P₁₁ = 1`. -/
def p11 : ℝ := 1 - M.p10

/-- Transition probability from state `a` to state `b` (`true` = 1). -/
def P : Bool → Bool → ℝ
  | false, false => M.p00
  | false, true => M.p01
  | true, false => M.p10
  | true, true => M.p11

/-- Eq. (11): the mean. -/
def mu : ℝ := M.p01 / (M.p10 + M.p01)
/-- Eq. (12): the serial correlation coefficient. -/
def scc : ℝ := 1 - M.p10 - M.p01

/-- Stationary probability of each state: `P₁ = μ`, `P₀ = 1 - μ`. -/
def pi : Bool → ℝ
  | true => M.mu
  | false => 1 - M.mu

lemma sum_pos : 0 < M.p10 + M.p01 := add_pos M.p10_pos M.p01_pos

lemma p00_nonneg : 0 ≤ M.p00 := by unfold p00; linarith [M.p01_le]
lemma p11_nonneg : 0 ≤ M.p11 := by unfold p11; linarith [M.p10_le]
lemma p00_le_one : M.p00 ≤ 1 := by unfold p00; linarith [M.p01_pos]
lemma p11_le_one : M.p11 ≤ 1 := by unfold p11; linarith [M.p10_pos]

lemma P_nonneg (a b : Bool) : 0 ≤ M.P a b := by
  cases a <;> cases b <;> simp [P, M.p00_nonneg, M.p11_nonneg, M.p01_pos.le, M.p10_pos.le]

lemma mu_pos : 0 < M.mu := div_pos M.p01_pos M.sum_pos
lemma mu_lt_one : M.mu < 1 := by
  rw [mu, div_lt_one M.sum_pos]; linarith [M.p10_pos]
lemma one_sub_mu : 1 - M.mu = M.p10 / (M.p10 + M.p01) := by
  rw [mu]; field_simp [M.sum_pos.ne']; ring

lemma pi_pos (a : Bool) : 0 < M.pi a := by
  cases a <;> simp [pi, M.mu_pos, M.mu_lt_one]
lemma pi_le_one (a : Bool) : M.pi a ≤ 1 := by
  cases a <;> simp [pi, M.mu_pos.le, M.mu_lt_one.le]

/-- The stationary distribution is invariant: `Σₐ πₐ P(a,b) = π_b`. -/
lemma stationary (b : Bool) : M.pi false * M.P false b + M.pi true * M.P true b = M.pi b := by
  have h := M.sum_pos.ne'
  cases b <;> simp only [pi, P, p00, p11, mu] <;> field_simp <;> ring

/-! ### Eqs. (3)–(12): μ and SCC -/

/-- Eq. (3): equal transition probabilities give unbiased output. -/
theorem eq3 (h : M.p01 = M.p10) : M.mu = 1 / 2 := by
  rw [mu, h]; field_simp [M.p10_pos.ne']; ring

/-- Eq. (4): `P₀₁ = 1 - P₁₀` gives independent output. -/
theorem eq4 (h : M.p01 = 1 - M.p10) : M.scc = 0 := by
  rw [scc, h]; ring

/-- Eq. (5): the iso-μ lines `P₁₀ = P₀₁ (1-μ)/μ`. -/
theorem eq5 : M.p10 = M.p01 * (1 - M.mu) / M.mu := by
  rw [one_sub_mu, mu]; field_simp [M.sum_pos.ne', M.p01_pos.ne']

/-- Eq. (6): the iso-SCC lines `P₁₀ = 1 - SCC - P₀₁`. -/
theorem eq6 : M.p10 = 1 - M.scc - M.p01 := by rw [scc]; ring

/-- Eq. (8): `P₀₁ = μ (1 - SCC)`. -/
theorem eq8 : M.p01 = M.mu * (1 - M.scc) := by
  rw [mu, scc]; field_simp [M.sum_pos.ne']; ring

/-- Eq. (10): `P₁₀ = (1 - μ)(1 - SCC)`. -/
theorem eq10 : M.p10 = (1 - M.mu) * (1 - M.scc) := by
  rw [one_sub_mu, scc]; field_simp [M.sum_pos.ne']; ring

/-- Eqs. (8), (10) as a construction: any mean `0 < μ < 1` and correlation `s`
with `μ(1-s) ≤ 1`, `(1-μ)(1-s) ≤ 1` and `s < 1` is realised by exactly one
generator, and that generator has mean `μ` and SCC `s`. -/
def ofMuScc (μ s : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hs : s < 1)
    (h01 : μ * (1 - s) ≤ 1) (h10 : (1 - μ) * (1 - s) ≤ 1) : Markov where
  p01 := μ * (1 - s)
  p10 := (1 - μ) * (1 - s)
  p01_pos := mul_pos hμ0 (by linarith)
  p01_le := h01
  p10_pos := mul_pos (by linarith) (by linarith)
  p10_le := h10

theorem ofMuScc_mu (μ s : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hs : s < 1) (h01 h10) :
    (ofMuScc μ s hμ0 hμ1 hs h01 h10).mu = μ := by
  simp only [ofMuScc, mu]
  have : (1 - s) ≠ 0 := by linarith
  field_simp; ring

theorem ofMuScc_scc (μ s : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hs : s < 1) (h01 h10) :
    (ofMuScc μ s hμ0 hμ1 hs h01 h10).scc = s := by
  simp only [ofMuScc, scc]; ring

/-- The two parameterisations determine each other: a generator is fixed by its
mean and SCC. -/
theorem ext_of_mu_scc (M N : Markov) (h1 : M.mu = N.mu) (h2 : M.scc = N.scc) :
    M.p01 = N.p01 ∧ M.p10 = N.p10 := by
  refine ⟨by rw [M.eq8, N.eq8, h1, h2], by rw [M.eq10, N.eq10, h1, h2]⟩

/-! ### Symbol probabilities, Eq. (18) -/

/-- Product of the transition probabilities along the bits `l`, starting from
the state `a` (the bit before the first bit of `l`). -/
def chainProb : Bool → List Bool → ℝ
  | _, [] => 1
  | a, b :: l => M.P a b * chainProb b l

/-- Eq. (18): the probability of a symbol `s`, weighting the cases of a
preceding 0 and a preceding 1 by the stationary probabilities `P₀`, `P₁`. -/
def symProb (s : List Bool) : ℝ :=
  M.pi false * M.chainProb false s + M.pi true * M.chainProb true s

lemma chainProb_nonneg (a : Bool) (l : List Bool) : 0 ≤ M.chainProb a l := by
  induction l generalizing a with
  | nil => simp [chainProb]
  | cons b l ih => exact mul_nonneg (M.P_nonneg a b) (ih b)

/-- By stationarity, Eq. (18) reduces to "probability of the first bit times the
transition probabilities": `P(s₀ s₁ … ) = π(s₀) ∏ P(sᵢ, sᵢ₊₁)`. -/
theorem symProb_cons (b : Bool) (l : List Bool) :
    M.symProb (b :: l) = M.pi b * M.chainProb b l := by
  simp only [symProb, chainProb]
  rw [← M.stationary b]; ring

lemma symProb_nonneg (s : List Bool) : 0 ≤ M.symProb s := by
  unfold symProb
  exact add_nonneg (mul_nonneg (M.pi_pos _).le (M.chainProb_nonneg _ _))
    (mul_nonneg (M.pi_pos _).le (M.chainProb_nonneg _ _))

/-! ### The MCV candidates of Tables 3 and 4

Tables 3 and 4 of the SPACE 2024 paper account for the unknown preceding bit by
adding the two cases: a symbol starting with 1 whose remaining transitions have
probability `x` is given probability `P₀₁x + P₁₁x = (P₀₁ + P₁₁)x`. Eq. (18) adds
the same two cases but weights each by the probability of that preceding bit,
`P₀ = 1 - μ` and `P₁ = μ`, giving `P₀P₀₁x + P₁P₁₁x = μx` (`prefactor_one`). The
unweighted sum counts each symbol once per possible preceding bit, so over all
symbols it totals 2 rather than 1 (`sum_unweighted` vs `sum_symProb`). The
corrected tables use `μ` in place of `P₀₁ + P₁₁` and `1 - μ` in place of
`P₀₀ + P₁₀`; the theorems below use these weighted prefactors. -/

/-- `alt a k` is the alternating string of length `k` starting with bit `a`. -/
def alt : Bool → ℕ → List Bool
  | _, 0 => []
  | a, k + 1 => a :: alt (!a) k

@[simp] lemma alt_length (a : Bool) (k : ℕ) : (alt a k).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [alt, ih]

/-- Prefactor of the all-ones candidate: `P₀P₀₁ + P₁P₁₁ = μ`. -/
theorem prefactor_one : M.pi false * M.p01 + M.pi true * M.p11 = M.mu := by
  simpa [P, pi] using M.stationary true

/-- Prefactor of the all-zeros candidate: `P₀P₀₀ + P₁P₁₀ = 1 - μ`. -/
theorem prefactor_zero : M.pi false * M.p00 + M.pi true * M.p10 = 1 - M.mu := by
  simpa [P, pi] using M.stationary false

lemma chainProb_replicate (a : Bool) (n : ℕ) :
    M.chainProb a (List.replicate n a) = M.P a a ^ n := by
  induction n with
  | zero => simp [chainProb]
  | succ n ih => simp [List.replicate_succ, chainProb, ih, pow_succ, mul_comm]

/-- Tables 3/4, row `{1}ⁿ`: `P = μ · P₁₁ⁿ⁻¹`. -/
theorem prob_ones (n : ℕ) : M.symProb (List.replicate (n + 1) true) = M.mu * M.p11 ^ n := by
  rw [List.replicate_succ, symProb_cons, chainProb_replicate]; rfl

/-- Tables 3/4, row `{0}ⁿ`: `P = (1 - μ) · P₀₀ⁿ⁻¹`. -/
theorem prob_zeros (n : ℕ) :
    M.symProb (List.replicate (n + 1) false) = (1 - M.mu) * M.p00 ^ n := by
  rw [List.replicate_succ, symProb_cons, chainProb_replicate]; rfl

lemma P_alt_pair (a : Bool) : M.P a (!a) * M.P (!a) a = M.p01 * M.p10 := by
  cases a <;> simp [P, mul_comm]

lemma chainProb_alt_even (a : Bool) (k : ℕ) :
    M.chainProb a (alt (!a) (2 * k)) = (M.p01 * M.p10) ^ k := by
  induction k with
  | zero => simp [alt, chainProb]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simp only [alt, chainProb, Bool.not_not]
    rw [ih, ← M.P_alt_pair a, pow_succ]; ring

/-- Table 4, rows `{01}…{0}` and `{10}…{1}` (odd width `2k+1`):
`P = π(a) · (P₀₁P₁₀)ᵏ`. -/
theorem prob_alt_odd (a : Bool) (k : ℕ) :
    M.symProb (alt a (2 * k + 1)) = M.pi a * (M.p01 * M.p10) ^ k := by
  simp only [alt]; rw [symProb_cons, chainProb_alt_even]

/-- Table 3, rows `{01}ⁿᐟ²` and `{10}ⁿᐟ²` (even width `2k+2`):
`P = π(a) · (P₀₁P₁₀)ᵏ · P(a, ¬a)`. -/
theorem prob_alt_even (a : Bool) (k : ℕ) :
    M.symProb (alt a (2 * k + 2)) = M.pi a * (M.p01 * M.p10) ^ k * M.P a (!a) := by
  have h : alt a (2 * k + 2) = alt a (2 * k + 1) ++ [!a] := by
    induction k generalizing a with
    | zero => cases a <;> rfl
    | succ k ih =>
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 by ring,
          show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring]
      simp only [alt, Bool.not_not] at ih ⊢
      rw [ih a]; rfl
  rw [h]
  simp only [alt]
  rw [List.cons_append, symProb_cons]
  have key : ∀ (b : Bool) (j : ℕ), M.chainProb b (alt (!b) (2 * j) ++ [!b]) =
      (M.p01 * M.p10) ^ j * M.P b (!b) := by
    intro b j
    induction j with
    | zero => simp [alt, chainProb]
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simp only [alt, List.cons_append, chainProb, Bool.not_not]
      rw [ih, ← M.P_alt_pair b, pow_succ]; ring
  rw [key]; ring

/-! ### Normalization of the symbol probabilities -/

/-- All bit strings of length `n`, as a list. -/
def allStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStrings n).map (false :: ·) ++ (allStrings n).map (true :: ·)

lemma P_sum (a : Bool) : M.P a false + M.P a true = 1 := by
  cases a <;> simp [P, p00, p11]

/-- Conditioned on a known preceding bit, the symbol probabilities sum to 1. -/
theorem sum_chainProb (n : ℕ) (a : Bool) :
    ((allStrings n).map (M.chainProb a)).sum = 1 := by
  induction n generalizing a with
  | zero => simp [allStrings, chainProb]
  | succ n ih =>
    simp only [allStrings, List.map_append, List.map_map, List.sum_append]
    have e : ∀ b, M.chainProb a ∘ (b :: ·) = fun s => M.P a b * M.chainProb b s := fun b => rfl
    rw [e, e, List.sum_map_mul_left, List.sum_map_mul_left, ih, ih, mul_one, mul_one, P_sum]

/-- Eq. (18) with the weights `P₀ = 1 - μ`, `P₁ = μ`: a probability distribution. -/
theorem sum_symProb (n : ℕ) : ((allStrings n).map M.symProb).sum = 1 := by
  unfold symProb
  rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left, sum_chainProb,
    sum_chainProb]
  simp [pi]

/-- The unweighted form of Tables 3/4 (both preceding-bit cases added, no
weights): its values over all symbols sum to 2. -/
theorem sum_unweighted (n : ℕ) :
    ((allStrings n).map fun s => M.chainProb false s + M.chainProb true s).sum = 2 := by
  rw [List.sum_map_add, sum_chainProb, sum_chainProb]; norm_num

/-! ### Eqs. (13)–(15) -/

/-- Eqs. (13), (14): a three-step repeat is never more likely than a two-step one. -/
theorem eq13 : M.p11 ^ 3 ≤ M.p11 ^ 2 :=
  pow_le_pow_of_le_one M.p11_nonneg M.p11_le_one (by norm_num)
theorem eq14 : M.p00 ^ 3 ≤ M.p00 ^ 2 :=
  pow_le_pow_of_le_one M.p00_nonneg M.p00_le_one (by norm_num)

/-- The geometric rate of the dominant repeating two-bit pattern,
`m = max(P₁₁, P₀₀, √(P₀₁P₁₀))`. -/
noncomputable def m : ℝ := max (max M.p11 M.p00) (√(M.p01 * M.p10))

/-- Eq. (15): `m² = t = max(P₀₀P₀₀, P₀₁P₁₀, P₁₀P₀₁, P₁₁P₁₁)`. -/
theorem eq15 : M.m ^ 2 = max (max (M.p00 * M.p00) (M.p01 * M.p10))
    (max (M.p10 * M.p01) (M.p11 * M.p11)) := by
  have hp : 0 ≤ M.p01 * M.p10 := mul_nonneg M.p01_pos.le M.p10_pos.le
  have hs := Real.sq_sqrt hp
  have h0 := M.p00_nonneg; have h1 := M.p11_nonneg
  have hr := Real.sqrt_nonneg (M.p01 * M.p10)
  rw [show M.p10 * M.p01 = M.p01 * M.p10 from mul_comm _ _, ← hs, ← sq, ← sq]
  have mono : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → max a b ^ 2 = max (a ^ 2) (b ^ 2) := by
    intro a b ha hb
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ ha h 2)]
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hb h 2)]
  simp only [m]
  rw [mono _ _ (le_max_of_le_left h1) hr, mono _ _ h1 h0]
  have key : ∀ a b c : ℝ, max (max a b) c = max (max b c) (max c a) := by
    intro a b c; simp only [max_def]; split_ifs <;> linarith
  exact key _ _ _

lemma sqrt_pos' : 0 < √(M.p01 * M.p10) := Real.sqrt_pos.mpr (mul_pos M.p01_pos M.p10_pos)
lemma m_pos : 0 < M.m := lt_of_lt_of_le M.sqrt_pos' (le_max_right _ _)
lemma p11_le_m : M.p11 ≤ M.m := le_trans (le_max_left _ _) (le_max_left _ _)
lemma p00_le_m : M.p00 ≤ M.m := le_trans (le_max_right _ _) (le_max_left _ _)
lemma sqrt_le_m : √(M.p01 * M.p10) ≤ M.m := le_max_right _ _

/-! ### Every symbol is bounded by the dominant pattern

The gauge `w(0) = 1`, `w(1) = u = √(P₀₁/P₁₀)` turns every transition into one of
weight at most `m`: `P(a,b) w(a) ≤ m w(b)`. -/

/-- The gauge factor `u = √(P₀₁/P₁₀)`. -/
noncomputable def u : ℝ := √(M.p01 / M.p10)

lemma u_pos : 0 < M.u := Real.sqrt_pos.mpr (div_pos M.p01_pos M.p10_pos)

lemma sqrt_mul_u : √(M.p01 * M.p10) * M.u = M.p01 := by
  rw [u, ← Real.sqrt_mul (mul_nonneg M.p01_pos.le M.p10_pos.le)]
  rw [show M.p01 * M.p10 * (M.p01 / M.p10) = M.p01 ^ 2 by
    field_simp [M.p10_pos.ne']]
  exact Real.sqrt_sq M.p01_pos.le

lemma p10_mul_u : M.p10 * M.u = √(M.p01 * M.p10) := by
  rw [← Real.sqrt_sq (mul_nonneg M.p10_pos.le M.u_pos.le)]
  congr 1
  rw [mul_pow, u, Real.sq_sqrt (div_nonneg M.p01_pos.le M.p10_pos.le)]
  field_simp [M.p10_pos.ne']

/-- The gauge weights. -/
noncomputable def w : Bool → ℝ
  | false => 1
  | true => M.u

lemma w_pos (a : Bool) : 0 < M.w a := by cases a <;> simp [w, M.u_pos]

lemma gauge_step (a b : Bool) : M.P a b * M.w a ≤ M.m * M.w b := by
  have hm := M.m_pos
  cases a <;> cases b <;> simp only [P, w, mul_one]
  · exact M.p00_le_m
  · rw [← M.sqrt_mul_u]; exact mul_le_mul_of_nonneg_right M.sqrt_le_m M.u_pos.le
  · rw [M.p10_mul_u]; exact M.sqrt_le_m
  · exact mul_le_mul_of_nonneg_right M.p11_le_m M.u_pos.le

lemma chainProb_gauge (a : Bool) (l : List Bool) :
    M.chainProb a l * M.w a ≤ M.m ^ l.length * M.w (l.getLastD a) := by
  induction l generalizing a with
  | nil => simp [chainProb]
  | cons b l ih =>
    simp only [chainProb, List.length_cons, List.getLastD_cons]
    calc M.P a b * M.chainProb b l * M.w a
        = (M.P a b * M.w a) * M.chainProb b l := by ring
      _ ≤ (M.m * M.w b) * M.chainProb b l :=
          mul_le_mul_of_nonneg_right (M.gauge_step a b) (M.chainProb_nonneg b l)
      _ = M.m * (M.chainProb b l * M.w b) := by ring
      _ ≤ M.m * (M.m ^ l.length * M.w (l.getLastD b)) :=
          mul_le_mul_of_nonneg_left (ih b) M.m_pos.le
      _ = M.m ^ (l.length + 1) * M.w (l.getLastD b) := by ring

/-- The constant `K = u + 1/u`. -/
noncomputable def K : ℝ := M.u + M.u⁻¹

lemma w_ratio_le (a b : Bool) : M.w b / M.w a ≤ M.K := by
  have hu := M.u_pos
  have hi : 0 < M.u⁻¹ := inv_pos.mpr hu
  have h1 : 1 ≤ M.u + M.u⁻¹ := by
    have : 2 ≤ M.u + M.u⁻¹ := by
      have := sq_nonneg (M.u - 1)
      rw [← sub_nonneg]
      have e : M.u + M.u⁻¹ - 2 = (M.u - 1) ^ 2 / M.u := by field_simp; ring
      rw [e]; positivity
    linarith
  cases a <;> cases b <;> simp only [w, K, div_one, div_self hu.ne', one_div] <;> linarith

/-- **Upper bound.** Every symbol of `n + 1` bits has probability at most
`K · mⁿ`. -/
theorem symProb_le (b : Bool) (l : List Bool) : M.symProb (b :: l) ≤ M.K * M.m ^ l.length := by
  rw [symProb_cons]
  have hg := M.chainProb_gauge b l
  have hwa := M.w_pos b
  have hc : M.chainProb b l ≤ M.m ^ l.length * (M.w (l.getLastD b) / M.w b) := by
    rw [mul_div_assoc', le_div_iff₀ hwa]; exact hg
  calc M.pi b * M.chainProb b l ≤ 1 * M.chainProb b l :=
        mul_le_mul_of_nonneg_right (M.pi_le_one b) (M.chainProb_nonneg b l)
    _ ≤ M.m ^ l.length * (M.w (l.getLastD b) / M.w b) := by rw [one_mul]; exact hc
    _ ≤ M.m ^ l.length * M.K :=
        mul_le_mul_of_nonneg_left (M.w_ratio_le _ _) (pow_nonneg M.m_pos.le _)
    _ = M.K * M.m ^ l.length := by ring

/-- The constant `c = min(μ, 1 - μ, μ P₁₀ / √(P₀₁P₁₀))` of the lower bound. -/
noncomputable def cLow : ℝ := min (min M.mu (1 - M.mu)) (M.mu * M.p10 / √(M.p01 * M.p10))

lemma cLow_pos : 0 < M.cLow := by
  have := M.mu_pos; have := M.mu_lt_one; have := M.sqrt_pos'; have := M.p10_pos
  unfold cLow; apply lt_min (lt_min (by linarith) (by linarith)); positivity

/-- **Lower bound.** For every `n` some symbol of `n + 1` bits (one of the
repeating patterns) has probability at least `c · mⁿ`. -/
theorem exists_symProb_ge (n : ℕ) :
    ∃ s : List Bool, s.length = n + 1 ∧ M.cLow * M.m ^ n ≤ M.symProb s := by
  have hc := M.cLow_pos
  have hmu := M.mu_pos
  have hr := M.sqrt_pos'
  have hsq : √(M.p01 * M.p10) ^ 2 = M.p01 * M.p10 :=
    Real.sq_sqrt (mul_nonneg M.p01_pos.le M.p10_pos.le)
  unfold m
  rcases le_total (max M.p11 M.p00) (√(M.p01 * M.p10)) with h | h
  · rw [max_eq_right h]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · refine ⟨alt true (2 * k + 1), by simp [alt_length], ?_⟩
      · rw [prob_alt_odd, pow_mul, hsq]
        simp only [pi]
        exact mul_le_mul_of_nonneg_right (le_trans (min_le_left _ _) (min_le_left _ _))
          (pow_nonneg (mul_nonneg M.p01_pos.le M.p10_pos.le) _)
    · refine ⟨alt true (2 * k + 2), by simp [alt_length], ?_⟩
      rw [prob_alt_even, pow_succ, pow_mul, hsq]
      simp only [pi, P, Bool.not_true]
      have e : M.mu * (M.p01 * M.p10) ^ k * M.p10 =
          (M.mu * M.p10 / √(M.p01 * M.p10)) * ((M.p01 * M.p10) ^ k * √(M.p01 * M.p10)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _)
        (mul_nonneg (pow_nonneg (mul_nonneg M.p01_pos.le M.p10_pos.le) _) hr.le)
  · rw [max_eq_left h]
    rcases le_total M.p00 M.p11 with h' | h'
    · rw [max_eq_left h']
      refine ⟨List.replicate (n + 1) true, by simp, ?_⟩
      rw [prob_ones]
      exact mul_le_mul_of_nonneg_right (le_trans (min_le_left _ _) (min_le_left _ _))
        (pow_nonneg M.p11_nonneg _)
    · rw [max_eq_right h']
      refine ⟨List.replicate (n + 1) false, by simp, ?_⟩
      rw [prob_zeros]
      exact mul_le_mul_of_nonneg_right (le_trans (min_le_left _ _) (min_le_right _ _))
        (pow_nonneg M.p00_nonneg _)

/-! ### The most common value and the min-entropy rate -/

/-- All bit strings of length `n`. -/
def strings (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image List.ofFn

lemma mem_strings {n : ℕ} {s : List Bool} : s ∈ strings n ↔ s.length = n := by
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    simp
  · intro h
    subst h
    exact Finset.mem_image.mpr ⟨s.get, Finset.mem_univ _, List.ofFn_get s⟩

lemma strings_nonempty (n : ℕ) : (strings n).Nonempty :=
  ⟨List.replicate n true, mem_strings.mpr (by simp)⟩

/-- Probability of the MCV of `(n+1)`-bit symbols. -/
noncomputable def mcvProb (n : ℕ) : ℝ := (strings (n + 1)).sup' (strings_nonempty _) M.symProb

/-- Eq. (19): min-entropy per bit of `(n+1)`-bit symbols. -/
noncomputable def minEntropyPerBit (n : ℕ) : ℝ := -logb 2 (M.mcvProb n) / (n + 1)

/-- The asymptotic min-entropy rate `-log₂ max(P₁₁, P₀₀, √(P₀₁P₁₀))`. -/
noncomputable def entropyRate : ℝ := -logb 2 M.m

theorem mcvProb_le (n : ℕ) : M.mcvProb n ≤ M.K * M.m ^ n := by
  apply Finset.sup'_le
  intro s hs
  rw [mem_strings] at hs
  match s, hs with
  | b :: l, h =>
    have : l.length = n := by simpa using h
    rw [← this]; exact M.symProb_le b l

theorem mcvProb_ge (n : ℕ) : M.cLow * M.m ^ n ≤ M.mcvProb n := by
  obtain ⟨s, hs, hle⟩ := M.exists_symProb_ge n
  exact le_trans hle (Finset.le_sup' M.symProb (mem_strings.mpr hs))

/-- **Min-entropy rate theorem.** The per-bit min-entropy of `b`-bit symbols
from the generator converges, as `b → ∞`, to `-log₂ max(P₁₁, P₀₀, √(P₀₁P₁₀))`.
This is Eq. (2) of the follow-up paper; the prefactors of Tables 3 and 4 only
contribute `O(1/b)`. -/
theorem minEntropy_tendsto :
    Tendsto M.minEntropyPerBit atTop (𝓝 M.entropyRate) := by
  have hm := M.m_pos
  have hc := M.cLow_pos
  have hK : 0 < M.K := by have := M.u_pos; unfold K; positivity
  -- log₂ bounds on mcvProb
  have hpos : ∀ n, 0 < M.mcvProb n := fun n =>
    lt_of_lt_of_le (mul_pos hc (pow_pos hm n)) (M.mcvProb_ge n)
  have lo : ∀ n : ℕ, logb 2 M.cLow + n * logb 2 M.m ≤ logb 2 (M.mcvProb n) := by
    intro n
    rw [← Real.logb_pow, ← Real.logb_mul hc.ne' (pow_pos hm n).ne']
    exact Real.logb_le_logb_of_le (by norm_num) (mul_pos hc (pow_pos hm n)) (M.mcvProb_ge n)
  have hi : ∀ n : ℕ, logb 2 (M.mcvProb n) ≤ logb 2 M.K + n * logb 2 M.m := by
    intro n
    rw [← Real.logb_pow, ← Real.logb_mul hK.ne' (pow_pos hm n).ne']
    exact Real.logb_le_logb_of_le (by norm_num) (hpos n) (M.mcvProb_le n)
  -- (a + n b)/(n+1) → b
  have lim : ∀ a : ℝ, Tendsto (fun n : ℕ => -(a + n * logb 2 M.m) / (n + 1)) atTop
      (𝓝 M.entropyRate) := by
    intro a
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (logb 2 M.m - a)
    have h2 := h1.const_add (-logb 2 M.m)
    simp only [mul_zero, add_zero] at h2
    refine h2.congr' (Eventually.of_forall fun n => ?_)
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (lim (logb 2 M.K)) (lim (logb 2 M.cLow))
    (fun n => ?_) (fun n => ?_)
  · simp only [minEntropyPerBit]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [hi n]
  · simp only [minEntropyPerBit]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [lo n]

end Markov
end
end Polygon

