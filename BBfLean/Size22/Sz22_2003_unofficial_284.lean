import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #284: [14/15, 9/22, 125/2, 11/7, 22/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_284

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain
theorem d_to_e : ⟨0, 0, c, d+j, e⟩ [fm]⊢* ⟨0, 0, c, d, e+j⟩ := by
  induction j generalizing d e with
  | zero => exists 0
  | succ j ih =>
    rw [show d + (j + 1) = (d + j) + 1 from by omega]
    step fm; apply stepStar_trans (ih (d := d) (e := e + 1))
    rw [show e + 1 + j = e + (j + 1) from by omega]; finish

-- R3 chain
theorem r3_chain : ⟨a+j, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+3*j, d, 0⟩ := by
  induction j generalizing a c with
  | zero => exists 0
  | succ j ih =>
    rw [show a + (j + 1) = (a + j) + 1 from by omega]
    step fm; apply stepStar_trans (ih (a := a) (c := c + 3))
    rw [show c + 3 + 3 * j = c + 3 * (j + 1) from by ring]; finish

-- R2 drain
theorem r2_drain : ⟨a+j, b, 0, d, j⟩ [fm]⊢* ⟨a, b+2*j, 0, d, 0⟩ := by
  induction j generalizing a b with
  | zero => exists 0
  | succ j ih =>
    rw [show a + (j + 1) = (a + j) + 1 from by omega]
    step fm; apply stepStar_trans (ih (a := a) (b := b + 2))
    rw [show b + 2 + 2 * j = b + 2 * (j + 1) from by ring]; finish

-- Merge step
theorem merge_step : ⟨j, 2, c+2, 2*j, e+1⟩ [fm]⊢* ⟨j+1, 2, c, 2*(j+1), e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Merge iteration
theorem merge_iter : ⟨0, 2, c+2*j, 0, d+j⟩ [fm]⊢* ⟨j, 2, c, 2*j, d⟩ := by
  induction j generalizing c d with
  | zero => exists 0
  | succ j ih =>
    rw [show c + 2 * (j + 1) = (c + 2) + 2 * j from by ring,
        show d + (j + 1) = (d + 1) + j from by omega]
    apply stepStar_trans (ih (c := c + 2) (d := d + 1))
    exact merge_step (j := j) (c := c) (e := d)

-- Expand step
theorem expand_step : ⟨a+1, b+3, 0, d, 0⟩ [fm]⊢* ⟨a+3, b, 0, d+3, 0⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Expand b=0
theorem expand_0 : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 3*a, d, 0⟩ := by
  have h := r3_chain (a := 0) (j := a) (c := 0) (d := d)
  simp at h; exact h

-- Expand b=1 (a >= 1)
theorem expand_1 : ⟨a+1, 1, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 3*a+5, d+1, 0⟩ := by
  step fm; step fm
  have h := r3_chain (a := 0) (j := a + 1) (c := 2) (d := d + 1)
  simp at h
  rw [show 3 * a + 5 = 2 + 3 * (a + 1) from by ring]
  exact h

-- Expand b=2 (a >= 1)
theorem expand_2 : ⟨a+1, 2, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 3*a+7, d+2, 0⟩ := by
  step fm; step fm; step fm
  have h := r3_chain (a := 0) (j := a + 2) (c := 1) (d := d + 2)
  simp at h
  rw [show 3 * a + 7 = 1 + 3 * (a + 2) from by ring]
  exact h

-- General expand by induction on b (mod 3 decomposition)
theorem expand_general : ⟨a+1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 3*(a+1)+2*b, d+b, 0⟩ := by
  induction b using Nat.strongRecOn generalizing a d with
  | _ b ih =>
    match b with
    | 0 =>
      rw [show 3 * (a + 1) + 2 * 0 = 3 * (a + 1) from by ring,
          show d + 0 = d from by omega]
      exact expand_0 (a := a + 1) (d := d)
    | 1 =>
      rw [show 3 * (a + 1) + 2 * 1 = 3 * a + 5 from by ring]
      exact expand_1 (a := a) (d := d)
    | 2 =>
      rw [show 3 * (a + 1) + 2 * 2 = 3 * a + 7 from by ring]
      exact expand_2 (a := a) (d := d)
    | b+3 =>
      apply stepStar_trans (expand_step (a := a) (b := b) (d := d))
      rw [show a + 3 = (a + 2) + 1 from by omega]
      have h := ih b (by omega) (a := a + 2) (d := d + 3)
      rw [show 3 * (a + 2 + 1) + 2 * b = 3 * (a + 1) + 2 * (b + 3) from by ring,
          show d + 3 + b = d + (b + 3) from by ring] at h
      exact h

-- Cycle for even c: (0, 2, 2*m, 0, d) →⁺ (0, 2, 2*m+d+3, 0, 2*d+2)
theorem cycle_even (m d : ℕ) (hd : d ≥ m) (hmd : 2*m ≥ d + 1) :
    ⟨0, 2, 2*m, 0, d⟩ [fm]⊢⁺ ⟨0, 2, 2*m+d+3, 0, 2*d+2⟩ := by
  -- Merge m iterations
  have h1 : ⟨0, 2, 2*m, 0, d⟩ [fm]⊢* ⟨m, 2, 0, 2*m, d - m⟩ := by
    have := merge_iter (c := 0) (j := m) (d := d - m)
    rwa [show 0 + 2 * m = 2 * m from by omega,
         show (d - m) + m = d from by omega] at this
  apply stepStar_stepPlus_stepPlus h1
  -- R2 drain (d-m) times
  have h2 : ⟨m, 2, 0, 2*m, d - m⟩ [fm]⊢* ⟨2*m - d, 2 + 2*(d - m), 0, 2*m, 0⟩ := by
    have := r2_drain (a := 2*m - d) (b := 2) (d := 2*m) (j := d - m)
    rwa [show (2*m - d) + (d - m) = m from by omega] at this
  apply stepStar_stepPlus_stepPlus h2
  -- Expand
  have h3 : ⟨2*m - d, 2 + 2*(d - m), 0, 2*m, 0⟩ [fm]⊢*
      ⟨0, 0, 2*m + d + 4, 2*d + 2, 0⟩ := by
    rw [show 2*m - d = (2*m - d - 1) + 1 from by omega]
    have := expand_general (a := 2*m - d - 1) (b := 2 + 2*(d - m)) (d := 2*m)
    rwa [show 3 * (2*m - d - 1 + 1) + 2 * (2 + 2*(d - m)) = 2*m + d + 4 from by omega,
         show 2*m + (2 + 2*(d - m)) = 2*d + 2 from by omega] at this
  apply stepStar_stepPlus_stepPlus h3
  -- d_to_e
  have h4 : ⟨0, 0, 2*m + d + 4, 2*d + 2, 0⟩ [fm]⊢*
      ⟨0, 0, 2*m + d + 4, 0, 2*d + 2⟩ := by
    have := d_to_e (c := 2*m + d + 4) (d := 0) (e := 0) (j := 2*d + 2)
    simp only [Nat.zero_add] at this
    exact this
  apply stepStar_stepPlus_stepPlus h4
  -- init_merge: 2 steps
  rw [show 2*m + d + 4 = (2*m + d + 3) + 1 from by omega]
  step fm; step fm; finish

-- Cycle for odd c: (0, 2, 2*m+1, 0, d) →⁺ (0, 2, 2*m+d+4, 0, 2*d+2)
theorem cycle_odd (m d : ℕ) (hd : d ≥ m) (hmd : 2*m ≥ d) :
    ⟨0, 2, 2*m+1, 0, d⟩ [fm]⊢⁺ ⟨0, 2, 2*m+d+4, 0, 2*d+2⟩ := by
  -- Merge m iterations
  have h1 : ⟨0, 2, 2*m+1, 0, d⟩ [fm]⊢* ⟨m, 2, 1, 2*m, d - m⟩ := by
    have := merge_iter (c := 1) (j := m) (d := d - m)
    rw [show 1 + 2 * m = 2*m+1 from by omega,
        show (d - m) + m = d from by omega] at this
    exact this
  apply stepStar_stepPlus_stepPlus h1
  -- R1 step
  apply step_stepStar_stepPlus
  · show fm ⟨m, 2, 1, 2 * m, d - m⟩ = some ⟨m + 1, 1, 0, 2 * m + 1, d - m⟩; rfl
  -- R2 drain (d-m) times
  have h2 : ⟨m + 1, 1, 0, 2*m + 1, d - m⟩ [fm]⊢*
      ⟨2*m + 1 - d, 1 + 2*(d - m), 0, 2*m + 1, 0⟩ := by
    have := r2_drain (a := 2*m + 1 - d) (b := 1) (d := 2*m + 1) (j := d - m)
    rw [show (2*m + 1 - d) + (d - m) = m + 1 from by omega] at this
    exact this
  apply stepStar_trans h2
  -- Expand
  have h3 : ⟨2*m + 1 - d, 1 + 2*(d - m), 0, 2*m + 1, 0⟩ [fm]⊢*
      ⟨0, 0, 2*m + d + 5, 2*d + 2, 0⟩ := by
    rw [show 2*m + 1 - d = (2*m - d) + 1 from by omega]
    have := expand_general (a := 2*m - d) (b := 1 + 2*(d - m)) (d := 2*m + 1)
    rw [show 3 * (2*m - d + 1) + 2 * (1 + 2*(d - m)) = 2*m + d + 5 from by omega,
        show (2*m + 1) + (1 + 2*(d - m)) = 2*d + 2 from by omega] at this
    exact this
  apply stepStar_trans h3
  -- d_to_e
  have h4 : ⟨0, 0, 2*m + d + 5, 2*d + 2, 0⟩ [fm]⊢*
      ⟨0, 0, 2*m + d + 5, 0, 2*d + 2⟩ := by
    have := d_to_e (c := 2*m + d + 5) (d := 0) (e := 0) (j := 2*d + 2)
    simp only [Nat.zero_add] at this
    exact this
  apply stepStar_trans h4
  -- init_merge
  rw [show 2*m + d + 5 = (2*m + d + 4) + 1 from by omega]
  step fm; step fm; finish

-- Sequences
mutual
def c_val : ℕ → ℕ
  | 0 => 5
  | n+1 => c_val n + d_val n + 3
def d_val : ℕ → ℕ
  | 0 => 2
  | n+1 => 2 * d_val n + 2
end

theorem cd_diff : ∀ n, c_val n = d_val n + n + 3 := by
  intro n; induction n with
  | zero => decide
  | succ n ih => simp [c_val, d_val]; omega

theorem d_val_ge : ∀ n, d_val n ≥ n + 2 := by
  intro n; induction n with
  | zero => decide
  | succ n ih => simp [d_val]; omega

-- c_val n >= 5
theorem c_val_ge : ∀ n, c_val n ≥ 5 := by
  intro n; have h1 := cd_diff n; have h2 := d_val_ge n; omega

-- Main cycle
theorem main_cycle (n : ℕ) :
    ⟨0, 2, c_val n, 0, d_val n⟩ [fm]⊢⁺ ⟨0, 2, c_val (n+1), 0, d_val (n+1)⟩ := by
  have hcd := cd_diff n
  have hdge := d_val_ge n
  have hcge := c_val_ge n
  -- Unfold the next step
  show ⟨0, 2, c_val n, 0, d_val n⟩ [fm]⊢⁺
    ⟨0, 2, c_val n + d_val n + 3, 0, 2 * d_val n + 2⟩
  rcases Nat.even_or_odd (c_val n) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- Even: c_val n = m + m
    have hdm : d_val n ≥ m := by omega
    have hmd : 2 * m ≥ d_val n + 1 := by omega
    have h := cycle_even m (d_val n) hdm hmd
    -- h : (0,2,2*m,0,d_val n) ⊢⁺ (0,2,2*m+d_val n+3,0,2*d_val n+2)
    rw [show c_val n = 2 * m from by omega]
    exact h
  · -- Odd: c_val n = 2*m + 1
    have hdm : d_val n ≥ m := by omega
    have hmd : 2 * m ≥ d_val n := by omega
    have h := cycle_odd m (d_val n) hdm hmd
    -- h : (0,2,2*m+1,0,d_val n) ⊢⁺ (0,2,2*m+d_val n+4,0,2*d_val n+2)
    rw [show c_val n = 2 * m + 1 from by omega,
        show 2 * m + 1 + d_val n + 3 = 2 * m + d_val n + 4 from by omega]
    exact h

-- Initial: c₀ →⁺ (0, 2, 5, 0, 2)
theorem init : c₀ [fm]⊢⁺ ⟨0, 2, c_val 0, 0, d_val 0⟩ := by
  show c₀ [fm]⊢⁺ ⟨0, 2, 5, 0, 2⟩
  execute fm 11

theorem nonhalt : ¬halts fm c₀ := by
  apply stepPlus_not_halts_not_halts init
  apply progress_nonhalt_simple (fm := fm) (C := fun n ↦ ⟨0, 2, c_val n, 0, d_val n⟩) (i₀ := 0)
  intro n
  exact ⟨n + 1, main_cycle n⟩

end Sz22_2003_unofficial_284
