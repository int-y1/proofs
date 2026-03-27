import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #364: [2/15, 3/98, 1375/2, 7/5, 4/11]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -2  0
-1  0  3  0  1
 0  0 -1  1  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_364

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- Helper: R3 fires when b may be nonzero, c=0, d ∈ {0,1}
private theorem r3_d0 (a b e : ℕ) : fm ⟨a+1, b, 0, 0, e⟩ = some ⟨a, b, 3, 0, e+1⟩ := by
  cases b <;> rfl
private theorem r3_d1 (a b e : ℕ) : fm ⟨a+1, b, 0, 1, e⟩ = some ⟨a, b, 3, 1, e+1⟩ := by
  cases b <;> rfl
-- Helper: R2 fires when b may be nonzero, c=0
private theorem r2_step (a b d e : ℕ) : fm ⟨a+1, b, 0, d+2, e⟩ = some ⟨a, b+1, 0, d, e⟩ := by
  cases b <;> rfl

-- R4 repeated: convert c to d
theorem c_to_d : ∀ k c d e, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R3 repeated with d=0, b=0
theorem a_to_ce_d0 : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R3 repeated with d=1, b=0
theorem a_to_ce_d1 : ∀ k a c e, ⟨a+k, 0, c, 1, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 1, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R1^3+R3 loop with d=0
theorem r1r3_loop_d0 : ∀ k a b e, ⟨a, b+3*k, 3, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 3, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 1 + 1 + 1 = (a + 2) + 1 from by ring]
  apply stepStar_trans (step_stepStar (r3_d0 (a+2) (b + 3*k) e))
  apply stepStar_trans (ih (a + 2) b (e + 1)); ring_nf; finish

-- R1^3+R3 loop with d=1
theorem r1r3_loop_d1 : ∀ k a b e, ⟨a, b+3*k, 3, 1, e⟩ [fm]⊢* ⟨a+2*k, b, 3, 1, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 1 + 1 + 1 = (a + 2) + 1 from by ring]
  apply stepStar_trans (step_stepStar (r3_d1 (a+2) (b + 3*k) e))
  apply stepStar_trans (ih (a + 2) b (e + 1)); ring_nf; finish

-- R5+R2+R2 loop
theorem r5r2r2_loop : ∀ k b d e, ⟨0, b, 0, d+4*k, e+k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + 4 * (k + 1) = d + 4 * k + 2 + 2 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm  -- R5
  apply stepStar_trans (step_stepStar (r2_step 1 b (d + 4*k + 2) (e + k)))
  rw [show d + 4 * k + 2 = (d + 4 * k) + 2 from by ring]
  apply stepStar_trans (step_stepStar (r2_step 0 (b+1) (d + 4*k) (e + k)))
  apply stepStar_trans (ih (b + 2) d e); ring_nf; finish

-- R5+R2+R3(d=0) sequence: (0, b, 0, 2, e+1) -> R5 -> R2 -> R3 -> (0, b+1, 3, 0, e+1)
theorem r5_r2_r3_d0 (b e : ℕ) : ⟨0, b, 0, 2, e+1⟩ [fm]⊢* ⟨0, b+1, 3, 0, e+1⟩ := by
  apply stepStar_trans (step_stepStar (show fm ⟨0, b, 0, 2, e+1⟩ = some ⟨2, b, 0, 2, e⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (r2_step 1 b 0 e))
  apply stepStar_trans (step_stepStar (r3_d0 0 (b+1) e))
  finish

-- R5+R3(d=1) sequence: (0, b, 0, 1, e+1) -> R5: (2, b, 0, 1, e) -> R3: (1, b, 3, 1, e+1)
theorem r5_r3_d1 (b e : ℕ) : ⟨0, b, 0, 1, e+1⟩ [fm]⊢* ⟨1, b, 3, 1, e+1⟩ := by
  apply stepStar_trans (step_stepStar (show fm ⟨0, b, 0, 1, e+1⟩ = some ⟨2, b, 0, 1, e⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (r3_d1 1 b e))
  finish

-- Phase 1+1b+1c combined: consume b with d=1, then R3 chain
-- (0, 6n+1, 3, 1, e) ⊢* (0, 0, 12n+5, 1, e+6n+1)
theorem phase_1 (n e : ℕ) :
    ⟨0, 6*n+1, 3, 1, e⟩ [fm]⊢* ⟨0, 0, 12*n+5, 1, e+6*n+1⟩ := by
  -- r1r3_loop_d1(2n): ⊢* (4n, 1, 3, 1, e+2n)
  apply stepStar_trans (c₂ := ⟨4*n, 1, 3, 1, e+2*n⟩)
  · have h := r1r3_loop_d1 (2*n) 0 1 e
    simp only [(by ring : 1 + 3 * (2 * n) = 6 * n + 1),
               (by ring : 0 + 2 * (2 * n) = 4 * n)] at h; exact h
  -- R1: ⊢ (4n+1, 0, 2, 1, e+2n)
  apply stepStar_trans
  · apply step_stepStar; show fm ⟨4*n, 1, 3, 1, e+2*n⟩ = some ⟨4*n+1, 0, 2, 1, e+2*n⟩; simp [fm]
  -- a_to_ce_d1(4n+1): ⊢* (0, 0, 12n+5, 1, e+6n+1)
  have h := a_to_ce_d1 (4*n+1) 0 2 (e+2*n)
  simp only [Nat.zero_add,
             (by ring : 2 + 3 * (4 * n + 1) = 12 * n + 5),
             (by ring : e + 2 * n + (4 * n + 1) = e + 6 * n + 1)] at h; exact h

-- Phase 5+5b combined: consume b with d=0, then R3 chain
-- (0, 6n+3, 3, 0, e) ⊢* (0, 0, 12n+9, 0, e+6n+3)
theorem phase_5 (n e : ℕ) :
    ⟨0, 6*n+3, 3, 0, e⟩ [fm]⊢* ⟨0, 0, 12*n+9, 0, e+6*n+3⟩ := by
  -- r1r3_loop_d0(2n+1): ⊢* (4n+2, 0, 3, 0, e+2n+1)
  apply stepStar_trans (c₂ := ⟨4*n+2, 0, 3, 0, e+2*n+1⟩)
  · have h := r1r3_loop_d0 (2*n+1) 0 0 e
    simp only [(by ring : 0 + 3 * (2 * n + 1) = 6 * n + 3),
               (by ring : 0 + 2 * (2 * n + 1) = 4 * n + 2)] at h; exact h
  -- a_to_ce_d0(4n+2): ⊢* (0, 0, 12n+9, 0, e+6n+3)
  have h := a_to_ce_d0 (4*n+2) 0 3 (e+2*n+1)
  simp only [Nat.zero_add,
             (by ring : 3 + 3 * (4 * n + 2) = 12 * n + 9),
             (by ring : e + 2 * n + 1 + (4 * n + 2) = e + 6 * n + 3)] at h; exact h

-- Phase 9: consume b+4 with R1^3+R3 loop starting from (1, b+4, 3, 1, e)
-- (1, 6n+4, 3, 1, e) ⊢* (0, 0, 12n+14, 1, e+6n+5)
theorem phase_9 (n e : ℕ) :
    ⟨1, 6*n+4, 3, 1, e⟩ [fm]⊢* ⟨0, 0, 12*n+14, 1, e+6*n+5⟩ := by
  -- R1^3: (4, 6n+1, 0, 1, e)
  rw [show 6 * n + 4 = (6 * n + 1) + 1 + 1 + 1 from by ring]
  step fm; step fm; step fm
  -- R3: (3, 6n+1, 3, 1, e+1)
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (step_stepStar (r3_d1 3 (6*n+1) e))
  -- r1r3_loop_d1(2n): (3, 6n+1, 3, 1, e+1) ⊢* (4n+3, 1, 3, 1, e+2n+1)
  apply stepStar_trans (c₂ := ⟨4*n+3, 1, 3, 1, e+2*n+1⟩)
  · have h := r1r3_loop_d1 (2*n) 3 1 (e+1)
    simp only [(by ring : 1 + 3 * (2 * n) = 6 * n + 1),
               (by ring : 3 + 2 * (2 * n) = 4 * n + 3),
               (by ring : e + 1 + 2 * n = e + 2 * n + 1)] at h; exact h
  -- R1: (4n+4, 0, 2, 1, e+2n+1)
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨4*n+3, 1, 3, 1, e+2*n+1⟩ = some ⟨4*n+4, 0, 2, 1, e+2*n+1⟩; simp [fm]
  -- a_to_ce_d1(4n+4): ⊢* (0, 0, 12n+14, 1, e+6n+5)
  have h := a_to_ce_d1 (4*n+4) 0 2 (e+2*n+1)
  simp only [Nat.zero_add,
             (by ring : 2 + 3 * (4 * n + 4) = 12 * n + 14),
             (by ring : e + 2 * n + 1 + (4 * n + 4) = e + 6 * n + 5)] at h; exact h

-- Main transition: (0, 6n+1, 3, 1, e+1) ⊢⁺ (0, 6(n+1)+1, 3, 1, (e+9n+3)+1)
theorem main_trans (n e : ℕ) :
    ⟨0, 6*n+1, 3, 1, e+1⟩ [fm]⊢⁺ ⟨0, 6*(n+1)+1, 3, 1, (e+9*n+3)+1⟩ := by
  -- Phase 1: (0, 6n+1, 3, 1, e+1) ⊢* (0, 0, 12n+5, 1, e+6n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 12*n+5, 1, e+6*n+2⟩)
  · have h := phase_1 n (e+1)
    simp only [(by ring : e + 1 + 6 * n + 1 = e + 6 * n + 2)] at h; exact h
  -- Phase 2: c_to_d(12n+5): ⊢* (0, 0, 0, 12n+6, e+6n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 12*n+6, e+6*n+2⟩)
  · have h := c_to_d (12*n+5) 0 1 (e+6*n+2)
    simp only [Nat.zero_add, (by ring : 1 + (12 * n + 5) = 12 * n + 6)] at h; exact h
  -- Phase 3: r5r2r2_loop(3n+1): ⊢* (0, 6n+2, 0, 2, e+3n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*n+2, 0, 2, e+3*n+1⟩)
  · have h := r5r2r2_loop (3*n+1) 0 2 (e+3*n+1)
    simp only [(by ring : 2 + 4 * (3 * n + 1) = 12 * n + 6),
               (by ring : e + 3 * n + 1 + (3 * n + 1) = e + 6 * n + 2),
               (by ring : 0 + 2 * (3 * n + 1) = 6 * n + 2)] at h; exact h
  -- Phase 4: R5+R2+R3: (0, 6n+2, 0, 2, e+3n+1) ⊢* (0, 6n+3, 3, 0, e+3n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*n+3, 3, 0, e+3*n+1⟩)
  · exact r5_r2_r3_d0 (6*n+2) (e+3*n)
  -- Phase 5: (0, 6n+3, 3, 0, e+3n+1) ⊢* (0, 0, 12n+9, 0, e+9n+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 12*n+9, 0, e+9*n+4⟩)
  · have h := phase_5 n (e+3*n+1)
    simp only [(by ring : e + 3 * n + 1 + 6 * n + 3 = e + 9 * n + 4)] at h; exact h
  -- Phase 6: c_to_d(12n+9): ⊢* (0, 0, 0, 12n+9, e+9n+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 12*n+9, e+9*n+4⟩)
  · have h := c_to_d (12*n+9) 0 0 (e+9*n+4)
    simp only [(by ring : 0 + (12 * n + 9) = 12 * n + 9)] at h; exact h
  -- Phase 7: r5r2r2_loop(3n+2): ⊢* (0, 6n+4, 0, 1, e+6n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*n+4, 0, 1, e+6*n+2⟩)
  · have h := r5r2r2_loop (3*n+2) 0 1 (e+6*n+2)
    simp only [(by ring : 1 + 4 * (3 * n + 2) = 12 * n + 9),
               (by ring : e + 6 * n + 2 + (3 * n + 2) = e + 9 * n + 4),
               (by ring : 0 + 2 * (3 * n + 2) = 6 * n + 4)] at h; exact h
  -- Phase 8: R5+R3: (0, 6n+4, 0, 1, e+6n+2) ⊢* (1, 6n+4, 3, 1, e+6n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 6*n+4, 3, 1, e+6*n+2⟩)
  · exact r5_r3_d1 (6*n+4) (e+6*n+1)
  -- Phase 9: (1, 6n+4, 3, 1, e+6n+2) ⊢* (0, 0, 12n+14, 1, e+12n+7)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 12*n+14, 1, e+12*n+7⟩)
  · have h := phase_9 n (e+6*n+2)
    simp only [(by ring : e + 6 * n + 2 + 6 * n + 5 = e + 12 * n + 7)] at h; exact h
  -- Phase 10: c_to_d(12n+14): ⊢* (0, 0, 0, 12n+15, e+12n+7)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 12*n+15, e+12*n+7⟩)
  · have h := c_to_d (12*n+14) 0 1 (e+12*n+7)
    simp only [Nat.zero_add, (by ring : 1 + (12 * n + 14) = 12 * n + 15)] at h; exact h
  -- Phase 11: r5r2r2_loop(3n+3): ⊢* (0, 6n+6, 0, 3, e+9n+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 6*n+6, 0, 3, e+9*n+4⟩)
  · have h := r5r2r2_loop (3*n+3) 0 3 (e+9*n+4)
    simp only [(by ring : 3 + 4 * (3 * n + 3) = 12 * n + 15),
               (by ring : e + 9 * n + 4 + (3 * n + 3) = e + 12 * n + 7),
               (by ring : 0 + 2 * (3 * n + 3) = 6 * n + 6)] at h; exact h
  -- Phase 12: R5+R2+R3: (0, 6n+6, 0, 3, e+9n+4) ⊢⁺ (0, 6n+7, 3, 1, e+9n+4)
  -- R5 step first, then rest as stepStar
  apply step_stepStar_stepPlus
  · show fm ⟨0, 6*n+6, 0, 3, (e+9*n+3)+1⟩ = some ⟨2, 6*n+6, 0, 3, e+9*n+3⟩; simp [fm]
  apply stepStar_trans (step_stepStar (r2_step 1 (6*n+6) 1 (e+9*n+3)))
  apply stepStar_trans (step_stepStar (r3_d1 0 (6*n+7) (e+9*n+3)))
  show ⟨0, 6*n+7, 3, 1, e+9*n+3+1⟩ [fm]⊢* ⟨0, 6*(n+1)+1, 3, 1, (e+9*n+3)+1⟩
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 3, 1, 0+1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 6*n+1, 3, 1, e+1⟩) ⟨0, 0⟩
  intro ⟨n, e⟩; exact ⟨⟨n+1, e+9*n+3⟩, main_trans n e⟩

end Sz22_2003_unofficial_364
