/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.NegativeHypergeometric
public import VCVio.EvalDist.Expectation
public import VCVio.OracleComp.ProbComp

/-!
# Drawing without replacement until enough successes

`drawUntil accept r pool` draws uniformly from `pool` without replacement and stops as soon as `r`
accepting values have been collected, or when the pool runs out. It returns the values drawn, in
order, so a caller can read off both how many draws it made and which of them accepted.

`expectedValue_length_drawUntil` identifies its expected number of draws with the negative
hypergeometric recursion `NegHypergeom.expectedDraws`, and `expectedValue_length_drawUntil_le`
gives the resulting closed-form bound. Exhaustion needs no separate treatment: the loop simply
returns the whole pool, and `NegHypergeom.expectedDraws_le` already covers that case.

The pool is a `List`, not a `Finset`, because a draw is an index rather than a value: that keeps
the loop in `ProbComp` with no failure branch, makes the recursion terminate on the pool's length,
and costs nothing, since positions are what the counting argument uses anyway. Duplicates in the
pool are allowed and are counted as distinct.

The draw count is read as the expected length of the returned list, through
`OracleComp.EvalDist.expectedValue`.
-/

@[expose] public section

open scoped ENNReal

universe u

namespace List

variable {α : Type u} {p : α → Bool}

/-- Deleting an accepting position lowers the accepting count by one. -/
theorem countP_eraseIdx_of_pos {l : List α} {i : ℕ} (hi : i < l.length) (hp : p l[i] = true) :
    (l.eraseIdx i).countP p + 1 = l.countP p := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [eraseIdx_eq_take_drop_succ, countP_append, countP_append, ← List.getElem_cons_drop hi,
    countP_cons, hp]
  simp
  omega

/-- `countP` as a sum of indicators, the form that matches `Finset.card_filter`. -/
theorem countP_eq_sum_map (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [countP_cons, map_cons, sum_cons, ih]
      cases p x
      · simp
      · simp; omega

/-- In a duplicate-free list, deleting a position removes that value entirely. -/
theorem getElem_notMem_eraseIdx {l : List α} (hl : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l[i] ∉ l.eraseIdx i := by
  have hsplit : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    rw [← List.getElem_cons_drop hi]
  rw [eraseIdx_eq_take_drop_succ, mem_append]
  rw [hsplit, nodup_append] at hl
  obtain ⟨-, htail, hdisj⟩ := hl
  refine fun hmem => hmem.elim (fun htake => ?_) (fun hdrop => ?_)
  · exact hdisj _ htake _ (mem_cons_self ..) rfl
  · exact (nodup_cons.mp htail).1 hdrop

/-- Deleting a rejecting position leaves the accepting count alone. -/
theorem countP_eraseIdx_of_neg {l : List α} {i : ℕ} (hi : i < l.length) (hp : p l[i] = false) :
    (l.eraseIdx i).countP p = l.countP p := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [eraseIdx_eq_take_drop_succ, countP_append, countP_append, ← List.getElem_cons_drop hi,
    countP_cons, hp]
  simp

end List

namespace ProbComp

variable {S : Type}

/-! ## Expected length of a list-valued computation -/

open OracleComp.EvalDist in
/-- Prefixing a fixed value adds exactly one to the expected length. -/
theorem expectedValue_length_cons_map (y : S) (mc : ProbComp (List S)) :
    expectedValue ((y :: ·) <$> mc) (fun d => (d.length : ℝ≥0∞))
      = expectedValue mc (fun d => (d.length : ℝ≥0∞)) + 1 := by
  rw [expectedValue_map]
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
  rw [expectedValue_add, expectedValue_const (probFailure_of_liftM_PMF mc)]

/-! ## The loop -/

/-- Draw uniformly at random from `pool` without replacement, keeping every value drawn, until `r`
of them have been accepted or the pool is exhausted. -/
noncomputable def drawUntil (accept : S → Bool) : ℕ → List S → ProbComp (List S)
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | r + 1, x :: xs => do
      let i ← $[0..xs.length]
      let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
      (y :: ·) <$> drawUntil accept (if accept y then r else r + 1) ((x :: xs).eraseIdx i)
  termination_by _ l => l.length
  decreasing_by
    have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
    rw [List.length_eraseIdx_of_lt hi]
    simp only [List.length_cons] at hi ⊢
    omega

@[simp] theorem drawUntil_zero (accept : S → Bool) (l : List S) :
    drawUntil accept 0 l = pure [] := by rw [drawUntil]

@[simp] theorem drawUntil_nil (accept : S → Bool) (r : ℕ) :
    drawUntil accept r [] = pure [] := by cases r <;> rw [drawUntil]

theorem drawUntil_cons (accept : S → Bool) (r : ℕ) (x : S) (xs : List S) :
    drawUntil accept (r + 1) (x :: xs) =
      (do
        let i ← $[0..xs.length]
        let y := (x :: xs)[(i : ℕ)]'(by simpa using i.isLt)
        (y :: ·) <$>
          drawUntil accept (if accept y then r else r + 1) ((x :: xs).eraseIdx i)) := by
  rw [drawUntil]


/-! ## What the loop returns

Success is a property of the pool alone: the loop collects `r` accepting values exactly when the
pool holds that many, and otherwise stops having drained it. That is what lets the extractor read
its own success off the acceptance table. -/

theorem mem_of_mem_support_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → ∀ d ∈ support (drawUntil accept r l),
      ∀ y ∈ d, y ∈ l := by
  induction n with
  | zero =>
      intro r l hl d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ n ih =>
      intro r l hl d hd
      cases r with
      | zero => simp_all
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        rw [drawUntil_cons, mem_support_bind_iff] at hd
        obtain ⟨i, -, hd⟩ := hd
        rw [support_map] at hd
        obtain ⟨rest, hrest, rfl⟩ := hd
        have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
        have hlen : ((x :: xs).eraseIdx i).length = n := by
          rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.getElem_mem hi
        · exact List.mem_of_mem_eraseIdx (ih _ _ hlen rest hrest y hy)

theorem nodup_of_mem_support_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → l.Nodup → ∀ d ∈ support (drawUntil accept r l),
      d.Nodup := by
  induction n with
  | zero =>
      intro r l hl _ d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ n ih =>
      intro r l hl hnd d hd
      cases r with
      | zero => simp_all
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        rw [drawUntil_cons, mem_support_bind_iff] at hd
        obtain ⟨i, -, hd⟩ := hd
        rw [support_map] at hd
        obtain ⟨rest, hrest, rfl⟩ := hd
        have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
        have hlen : ((x :: xs).eraseIdx i).length = n := by
          rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
        refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih _ _ hlen (hnd.eraseIdx i) rest hrest⟩
        exact List.getElem_notMem_eraseIdx hnd hi
          (mem_of_mem_support_drawUntil accept _ _ _ hlen rest hrest _ hmem)

/-- The loop collects `min r (accepting values in the pool)` of them: it stops either because it
has enough or because the pool ran out. -/
theorem countP_of_mem_support_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n → ∀ d ∈ support (drawUntil accept r l),
      d.countP accept = min r (l.countP accept) := by
  induction n with
  | zero =>
      intro r l hl d hd
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp_all
  | succ n ih =>
      intro r l hl d hd
      cases r with
      | zero => simp_all
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        rw [drawUntil_cons, mem_support_bind_iff] at hd
        obtain ⟨i, -, hd⟩ := hd
        rw [support_map] at hd
        obtain ⟨rest, hrest, rfl⟩ := hd
        have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
        have hlen : ((x :: xs).eraseIdx i).length = n := by
          rw [List.length_eraseIdx_of_lt hi]; simpa using hxs
        cases hacc : accept ((x :: xs)[(i : ℕ)]) with
        | false =>
            rw [hacc] at hrest
            simp only [Bool.false_eq_true, if_false] at hrest
            have hcount := ih _ _ hlen rest hrest
            have hneg := List.countP_eraseIdx_of_neg hi hacc
            rw [List.countP_cons, hacc]
            simp only [Bool.false_eq_true, if_false]
            omega
        | true =>
            rw [hacc] at hrest
            simp only [if_true] at hrest
            have hcount := ih _ _ hlen rest hrest
            have hpos := List.countP_eraseIdx_of_pos hi hacc
            rw [List.countP_cons, hacc]
            simp only [if_true]
            omega

/-! ## Expected number of draws -/

private theorem sum_map_ite (l : List S) (p : S → Bool) (a b : ℝ≥0∞) :
    (l.map fun x => if p x then a else b).sum
      = (l.countP p : ℝ≥0∞) * a + (l.countP (fun x => !p x) : ℝ≥0∞) * b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      cases hx : p x <;>
        · simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true]
          push_cast
          ring

private theorem sum_fin_ite (l : List S) (p : S → Bool) (a b : ℝ≥0∞) :
    ∑ i : Fin l.length, (if p l[(i : ℕ)] then a else b)
      = (l.countP p : ℝ≥0∞) * a + (l.countP (fun x => !p x) : ℝ≥0∞) * b := by
  rw [← List.sum_ofFn (f := fun i : Fin l.length => if p l[(i : ℕ)] then a else b),
    show (List.ofFn fun i : Fin l.length => if p l[(i : ℕ)] then a else b)
      = l.map (fun y => if p y then a else b) from
      List.ofFn_getElem_eq_map l (fun y => if p y then a else b),
    sum_map_ite]

open OracleComp.EvalDist in
/-- The loop's expected number of draws is the negative hypergeometric expectation at the pool's
size and accepting count. -/
theorem expectedValue_length_drawUntil (accept : S → Bool) (n : ℕ) :
    ∀ (r : ℕ) (l : List S), l.length = n →
      expectedValue (drawUntil accept r l) (fun d => (d.length : ℝ≥0∞))
        = NegHypergeom.expectedDraws n (l.countP accept) r := by
  induction n with
  | zero =>
      intro r l hl
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hl
      simp
  | succ n ih =>
      intro r l hl
      cases r with
      | zero => simp
      | succ r =>
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
          cases l with
          | nil => simp at hl
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hxs : xs.length = n := by simpa using hl
        subst hxs
        set G : ℕ := (x :: xs).countP accept with hG
        set B : ℕ := (x :: xs).countP (fun y => !accept y) with hB
        have hGB : xs.length + 1 = G + B := by
          simpa only [List.length_cons, decide_not, Bool.decide_eq_true] using
            List.length_eq_countP_add_countP accept (l := x :: xs)
        have hne : ((xs.length : ℝ≥0∞) + 1) ≠ 0 := by positivity
        have htop : ((xs.length : ℝ≥0∞) + 1) ≠ ⊤ := by finiteness
        -- Drawing at index `i` leaves a pool one shorter, with one fewer accepting value exactly
        -- when the drawn value accepted.
        have hstep : ∀ i : Fin (xs.length + 1),
            expectedValue ((((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) :: ·) <$>
                drawUntil accept
                  (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then r else r + 1)
                  ((x :: xs).eraseIdx i)) (fun d => (d.length : ℝ≥0∞))
              = (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then
                  NegHypergeom.expectedDraws xs.length (G - 1) r
                else NegHypergeom.expectedDraws xs.length G (r + 1)) + 1 := by
          intro i
          have hi : (i : ℕ) < (x :: xs).length := by simpa using i.isLt
          have hlen : ((x :: xs).eraseIdx i).length = xs.length := by
            rw [List.length_eraseIdx_of_lt hi]; simp
          rw [expectedValue_length_cons_map, ih _ _ hlen]
          congr 1
          cases hacc : accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              rw [List.countP_eraseIdx_of_neg hi hacc]
          | true =>
              simp only [if_true]
              have hcount : ((x :: xs).eraseIdx i).countP accept = G - 1 := by
                have h := List.countP_eraseIdx_of_pos hi hacc
                omega
              rw [hcount]
        -- Average the step over a uniform index.
        rw [drawUntil_cons, expectedValue_bind, expectedValue_def]
        simp only [hstep, probOutput_uniformFin_eq_div]
        rw [ENNReal.tsum_mul_left, tsum_fintype (L := .unconditional _), Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        -- The indexed sum is a sum over the pool.
        have hcancel : ((xs.length : ℝ≥0∞) + 1)⁻¹ * ((xs.length : ℝ≥0∞) + 1) = 1 :=
          ENNReal.inv_mul_cancel hne htop
        rw [show (∑ i : Fin (xs.length + 1),
              (if accept ((x :: xs)[(i : ℕ)]'(by simpa using i.isLt)) then
                  NegHypergeom.expectedDraws xs.length (G - 1) r
                else NegHypergeom.expectedDraws xs.length G (r + 1)))
            = ∑ i : Fin (x :: xs).length,
                (if accept ((x :: xs)[(i : ℕ)]) then
                    NegHypergeom.expectedDraws xs.length (G - 1) r
                  else NegHypergeom.expectedDraws xs.length G (r + 1)) from rfl,
          sum_fin_ite, NegHypergeom.expectedDraws_succ,
          show xs.length + 1 - G = B from by omega,
          show ((xs.length + 1 : ℕ) : ℝ≥0∞) = (xs.length : ℝ≥0∞) + 1 from by push_cast; ring]
        simp only [div_eq_mul_inv, one_mul]
        rw [mul_add, mul_add, hcancel]
        ring

open OracleComp.EvalDist in
/-- The closed-form bound on the loop's expected number of draws. Exhaustion is covered: when the
pool holds fewer than `r` accepting values the loop draws all of it, and the bound still holds. -/
theorem expectedValue_length_drawUntil_le (accept : S → Bool) (r : ℕ) (l : List S) :
    expectedValue (drawUntil accept r l) (fun d => (d.length : ℝ≥0∞))
      ≤ r * (l.length + 1) / (l.countP accept + 1) := by
  rw [expectedValue_length_drawUntil accept l.length r l rfl]
  exact NegHypergeom.expectedDraws_le List.countP_le_length

end ProbComp
