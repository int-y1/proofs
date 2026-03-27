import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #225: [108/35, 1/363, 5/3, 11/5, 21/2]

Vector representation:
```
 2  3 -1 -1  0
 0 -1  0  0 -2
 0 -1  1  0  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_225

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: c → e when b = 0 and d = 0
theorem c_to_e : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R3 chain: b → c when d = 0 and e ≤ 1
theorem b_to_c : ∀ k, ∀ a c e, e ≤ 1 → ⟨a, k, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e _; simp; exists 0
  | succ k ih =>
    intro a c e he
    have hstep : fm ⟨a, k + 1, c, 0, e⟩ = some ⟨a, k, c + 1, 0, e⟩ := by
      rcases e with _ | _ | e <;> simp [fm]; omega
    apply stepStar_trans (step_stepStar hstep)
    have := ih a (c + 1) e he
    rw [show c + 1 + k = c + (k + 1) from by ring] at this
    exact this

-- R5/R2 drain (even): (a+k, 0, 0, d, 2*k) →* (a, 0, 0, d+k, 0)
theorem r5r2_even : ∀ k, ∀ a d, ⟨a + k, 0, 0, d, 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R5/R2 drain (odd): (a+k, 0, 0, d, 2*k+1) →* (a, 0, 0, d+k, 1)
theorem r5r2_odd : ∀ k, ∀ a d, ⟨a + k, 0, 0, d, 2 * k + 1⟩ [fm]⊢* ⟨a, 0, 0, d + k, 1⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R1/R3 pump: (a, b, 1, k+1, e) →* (a+2*(k+1), b+2*(k+1)+1, 0, 0, e) when e ≤ 1
theorem r1r3_pump : ∀ k, ∀ a b e, e ≤ 1 →
    ⟨a, b, 1, k + 1, e⟩ [fm]⊢* ⟨a + 2 * (k + 1), b + 2 * (k + 1) + 1, 0, 0, e⟩ := by
  intro k; induction k with
  | zero =>
    intro a b e _
    step fm
    ring_nf; finish
  | succ k ih =>
    intro a b e he
    -- R1: (a, b, 1, k+2, e) → (a+2, b+3, 0, k+1, e)
    step fm
    -- R3: (a+2, b+3, 0, k+1, e) → (a+2, b+2, 1, k+1, e) since e ≤ 1
    have hstep : fm ⟨a + 2, b + 3, 0, k + 1, e⟩ = some ⟨a + 2, b + 2, 1, k + 1, e⟩ := by
      rcases e with _ | _ | e <;> simp [fm]; omega
    apply stepStar_trans (step_stepStar hstep)
    have := ih (a + 2) (b + 2) e he
    rw [show a + 2 + 2 * (k + 1) = a + 2 * (k + 1 + 1) from by ring,
        show b + 2 + 2 * (k + 1) + 1 = b + 2 * (k + 1 + 1) + 1 from by ring] at this
    exact this

-- R5 then R3: (a+1, 0, 0, d, e) →* (a, 0, 1, d+1, e) when e ≤ 1
theorem r5_r3 (a d e : ℕ) (he : e ≤ 1) :
    ⟨a + 1, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 1, d + 1, e⟩ := by
  have hstep1 : fm ⟨a + 1, 0, 0, d, e⟩ = some ⟨a, 1, 0, d + 1, e⟩ := by
    rcases e with _ | _ | e <;> simp [fm]
  apply stepStar_trans (step_stepStar hstep1)
  have hstep2 : fm ⟨a, 1, 0, d + 1, e⟩ = some ⟨a, 0, 1, d + 1, e⟩ := by
    rcases e with _ | _ | e <;> simp [fm]; omega
  exact step_stepStar hstep2

-- Main transition: (3*n*(n+1)+2, 0, 6*n+3, 0, 0) ⊢⁺ (3*(n+1)*(n+2)+2, 0, 6*(n+1)+3, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨3*n*(n+1)+2, 0, 6*n+3, 0, 0⟩ [fm]⊢⁺ ⟨3*(n+1)*(n+2)+2, 0, 6*(n+1)+3, 0, 0⟩ := by
  -- Phase 1: c→e: (A, 0, C, 0, 0) → (A, 0, 0, 0, C) where C=6n+3
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*(n+1)+2, 0, 0, 0, 6*n+3⟩)
  · have h := c_to_e (6*n+3) (3*n*(n+1)+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5/R2 odd drain: e=6n+3=2*(3n+1)+1, k=3n+1
  --   (A, 0, 0, 0, 6n+3) → (A-(3n+1), 0, 0, 3n+1, 1)
  --   A-(3n+1) = 3n²+3n+2-3n-1 = 3n²+1
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+1, 0, 0, 3*n+1, 1⟩)
  · have h := r5r2_odd (3*n+1) (3*n*n+1) 0
    rw [show 3*n*n+1+(3*n+1) = 3*n*(n+1)+2 from by ring,
        show 2*(3*n+1)+1 = 6*n+3 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2b: R5+R3: (3n²+1, 0, 0, 3n+1, 1) → (3n², 0, 1, 3n+2, 1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n, 0, 1, 3*n+2, 1⟩)
  · exact r5_r3 (3*n*n) (3*n+1) 1 (by omega)
  -- Phase 3: R1/R3 pump: (3n², 0, 1, 3n+2, 1) → (3n²+6n+4, 6n+5, 0, 0, 1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+6*n+4, 6*n+5, 0, 0, 1⟩)
  · have h := r1r3_pump (3*n+1) (3*n*n) 0 1 (by omega)
    rw [show 3*n+1+1 = 3*n+2 from by ring,
        show 3*n*n + 2*(3*n+1+1) = 3*n*n+6*n+4 from by ring,
        show 0 + 2*(3*n+1+1)+1 = 6*n+5 from by ring] at h
    exact h
  -- Phase 4: R3 chain: b→c: (3n²+6n+4, 6n+5, 0, 0, 1) → (3n²+6n+4, 0, 6n+5, 0, 1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+6*n+4, 0, 6*n+5, 0, 1⟩)
  · have h := b_to_c (6*n+5) (3*n*n+6*n+4) 0 1 (by omega)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: c→e: (3n²+6n+4, 0, 6n+5, 0, 1) → (3n²+6n+4, 0, 0, 0, 6n+6)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+6*n+4, 0, 0, 0, 6*n+6⟩)
  · have h := c_to_e (6*n+5) (3*n*n+6*n+4) 1
    rw [show 1 + (6*n+5) = 6*n+6 from by ring] at h
    exact h
  -- Phase 6: R5/R2 even drain: e=6n+6=2*(3n+3), k=3n+3
  --   (3n²+6n+4, 0, 0, 0, 6n+6) → (3n²+3n+1, 0, 0, 3n+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+3*n+1, 0, 0, 3*n+3, 0⟩)
  · have h := r5r2_even (3*n+3) (3*n*n+3*n+1) 0
    rw [show 3*n*n+3*n+1+(3*n+3) = 3*n*n+6*n+4 from by ring,
        show 2*(3*n+3) = 6*n+6 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6b: R5+R3: (3n²+3n+1, 0, 0, 3n+3, 0) → (3n²+3n, 0, 1, 3n+4, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+3*n, 0, 1, 3*n+4, 0⟩)
  · exact r5_r3 (3*n*n+3*n) (3*n+3) 0 (by omega)
  -- Phase 7: R1/R3 pump: (3n²+3n, 0, 1, 3n+4, 0) → (3n²+9n+8, 6n+9, 0, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*n*n+9*n+8, 6*n+9, 0, 0, 0⟩)
  · have h := r1r3_pump (3*n+3) (3*n*n+3*n) 0 0 (by omega)
    rw [show 3*n+3+1 = 3*n+4 from by ring,
        show 3*n*n+3*n + 2*(3*n+3+1) = 3*n*n+9*n+8 from by ring,
        show 0 + 2*(3*n+3+1)+1 = 6*n+9 from by ring] at h
    exact h
  -- Phase 8: R3 chain: b→c: (3n²+9n+8, 6n+9, 0, 0, 0) → (3n²+9n+8, 0, 6n+9, 0, 0)
  -- This is the target state: 3(n+1)(n+2)+2 = 3n²+9n+8, 6(n+1)+3 = 6n+9
  have htarget1 : 3*(n+1)*(n+2)+2 = 3*n*n+9*n+8 := by ring
  have htarget2 : 6*(n+1)+3 = 6*n+9 := by ring
  rw [htarget1, htarget2]
  have h := b_to_c (6*n+9) (3*n*n+9*n+8) 0 0 (by omega)
  simp only [Nat.zero_add] at h
  exact stepStar_stepPlus h (by
    intro heq
    have := congr_arg (fun q : Q => q.2.1) heq
    simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 3, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3*n*(n+1)+2, 0, 6*n+3, 0, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_225
