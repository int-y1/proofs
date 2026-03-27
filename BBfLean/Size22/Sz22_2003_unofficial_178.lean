import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #178: [1/45, 98/5, 25/539, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0 -1  2  0
 0  0  2 -2 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_178

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: d → b (when c=0, e=0)
theorem d_to_b : ∀ k a b d, ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, (0 : ℕ), d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Up-phase: R2,R2,R3 cycle
-- (a, 0, 2, d, e+k) →* (a+2*k, 0, 2, d+2*k, e)
theorem up_phase : ∀ k a d e, ⟨a, 0, 2, d, e+k⟩ [fm]⊢* ⟨a+2*k, (0 : ℕ), 2, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    -- R2: c=2=1+1, b=0<2 so R1 doesn't match
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- R2: c=1=0+1
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- R3: d+4 = (d+2)+2, e+k+1 = (e+k)+1
    rw [show d + 4 = (d + 2) + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Drain phase: R5,R1 paired
-- (a+k, 2*k, 0, 0, e) →* (a, 0, 0, 0, e+k)
theorem drain : ∀ k a e, ⟨a+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    -- R5: a+k+1 >= 1, b=2k+2, c=0, d=0
    step fm
    -- R1: b=2k+2 >= 2, c=1
    rw [show (2 * k + 1 + 1) = (2 * k) + 2 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1)
-- C(n) = (n^2+n+1, 0, 0, 0, 2*n+2)
-- C(n+1) = (n^2+3*n+3, 0, 0, 0, 2*n+4)
theorem main_trans (n : ℕ) :
    ⟨n^2+n+1, 0, 0, 0, 2*n+2⟩ [fm]⊢⁺ ⟨n^2+3*n+3, (0 : ℕ), 0, 0, 2*n+4⟩ := by
  -- Phase 1 (R5): -> (n^2+n, 0, 1, 0, 2*n+3)
  rw [show n ^ 2 + n + 1 = (n ^ 2 + n) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨n^2+n, 0, 1, 0, 2*n+3⟩)
  · rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]; rfl
  -- Phase 2 (R2): -> (n^2+n+1, 0, 0, 2, 2*n+3)
  apply stepStar_trans (c₂ := ⟨n^2+n+1, 0, 0, 2, 2*n+3⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 3 (R3): -> (n^2+n+1, 0, 2, 0, 2*n+2)
  apply stepStar_trans (c₂ := ⟨n^2+n+1, 0, 2, 0, 2*n+2⟩)
  · rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    step fm; finish
  -- Phase 4 (up_phase, 2*n+2 iterations): -> (n^2+5*n+5, 0, 2, 4*n+4, 0)
  apply stepStar_trans (c₂ := ⟨n^2+5*n+5, 0, 2, 4*n+4, 0⟩)
  · have h := up_phase (2*n+2) (n^2+n+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show n ^ 2 + n + 1 + 2 * (2 * n + 2) = n ^ 2 + 5 * n + 5 from by ring,
        show 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 5 (R2, R2): -> (n^2+5*n+7, 0, 0, 4*n+8, 0)
  apply stepStar_trans (c₂ := ⟨n^2+5*n+7, 0, 0, 4*n+8, 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 6 (d_to_b): -> (n^2+5*n+7, 4*n+8, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨n^2+5*n+7, 4*n+8, 0, 0, 0⟩)
  · have h := d_to_b (4*n+8) (n^2+5*n+7) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 7 (drain): -> (n^2+3*n+3, 0, 0, 0, 2*n+4)
  · have h := drain (2*n+4) (n^2+3*n+3) 0
    simp only [Nat.zero_add] at h
    rw [show n ^ 2 + 3 * n + 3 + (2 * n + 4) = n ^ 2 + 5 * n + 7 from by ring,
        show 2 * (2 * n + 4) = 4 * n + 8 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 2⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun c ↦ ∃ n : ℕ, c = ⟨n^2+n+1, 0, 0, 0, 2*n+2⟩)
  · intro c ⟨n, hc⟩
    refine ⟨⟨n^2+3*n+3, 0, 0, 0, 2*n+4⟩, ⟨n+1, ?_⟩, ?_⟩
    · rw [show (n + 1) ^ 2 + (n + 1) + 1 = n ^ 2 + 3 * n + 3 from by ring,
          show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
    · rw [hc]; exact main_trans n
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_178
