import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #127: [1/45, 100/21, 33/2, 1/3, 63/11]

Vector representation:
```
 0 -2 -1  0  0
 2 -1  2 -1  0
-1  1  0  0  1
 0 -1  0  0  0
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_127

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R2-R3 interleave: (a, 1, c, d+1, e) -> R2 -> R3 -> (a+1, 1, c+2, d, e+1)
-- Iterated k times: (a, 1, c, d+k, e) -> (a+k, 1, c+2*k, d, e+k)
theorem interleave : ∀ k, ∀ a c d e,
    ⟨a, 1, c, d+k, e⟩ [fm]⊢* ⟨a+k, 1, c+2*k, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3-R1-R3 drain step: (a+2, 1, c+1, 0, f) -> (a, 1, c, 0, f+2)
theorem drain_step : ∀ a c f,
    ⟨a+2, 1, c+1, 0, f⟩ [fm]⊢* ⟨a, 1, c, 0, f+2⟩ := by
  intro a c f; step fm; step fm; step fm; finish

-- Even drain: (2*m, 1, c+m, 0, f) -> (0, 1, c, 0, f+2*m)
theorem drain_even : ∀ m, ∀ c f,
    ⟨2*m, 1, c+m, 0, f⟩ [fm]⊢* ⟨0, 1, c, 0, f+2*m⟩ := by
  intro m; induction' m with m ih <;> intro c f
  · exists 0
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
      show c + (m + 1) = (c + m) + 1 from by ring]
  apply stepStar_trans (drain_step _ _ _)
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Odd drain: (2*m+1, 1, c+m+1, 0, f) -> (0, 0, c, 0, f+2*m+1)
theorem drain_odd : ∀ m, ∀ c f,
    ⟨2*m+1, 1, c+m+1, 0, f⟩ [fm]⊢* ⟨0, 0, c, 0, f+2*m+1⟩ := by
  intro m; induction' m with m ih <;> intro c f
  · step fm; step fm; finish
  rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 from by ring,
      show c + (m + 1) + 1 = (c + m + 1) + 1 from by ring]
  apply stepStar_trans (drain_step _ _ _)
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 step: (0, 1, c, 0, f) -> (0, 0, c, 0, f)
theorem r4_step : ∀ c f, ⟨0, 1, c, 0, f⟩ [fm]⊢* ⟨0, 0, c, 0, f⟩ := by
  intro c f; step fm; finish

-- R5-R1 drain: (0, 0, c+1, d, f+1) -> (0, 0, c, d+1, f) in 2 steps
-- Iterated: (0, 0, c+k, d, f+k) -> (0, 0, c, d+k, f)
theorem r5r1_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c+k, d, f+k⟩ [fm]⊢* ⟨0, 0, c, d+k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih c (d+1) f)
  ring_nf; finish

-- Main transition for d = 2*k (even case):
-- (0,0,0,2*k,e+1) -> (0,0,0,3*k+1,e+k+1)
theorem trans_even (k : ℕ) (e : ℕ) :
    ⟨0, 0, 0, 2*k, e+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k+1, e+k+1⟩ := by
  -- R5: -> (0,2,0,2k+1,e). R2: -> (2,1,2,2k,e).
  step fm; step fm
  -- Interleave 2k times: (2,1,2,2k,e) -> (2k+2,1,4k+2,0,e+2k)
  apply stepStar_trans (c₂ := ⟨2*k+2, 1, 4*k+2, 0, e+2*k⟩)
  · have h := interleave (2*k) 2 2 0 e
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Even drain: (2*(k+1), 1, (3k+1)+(k+1), 0, e+2k) -> (0, 1, 3k+1, 0, e+4k+2)
  apply stepStar_trans (c₂ := ⟨0, 1, 3*k+1, 0, e+4*k+2⟩)
  · have h := drain_even (k+1) (3*k+1) (e+2*k)
    convert h using 2; ring_nf
  -- R4: -> (0, 0, 3k+1, 0, e+4k+2)
  apply stepStar_trans (r4_step _ _)
  -- R5-R1 drain: (0, 0, 0+(3k+1), 0, (e+k+1)+(3k+1)) -> (0, 0, 0, 3k+1, e+k+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 3*k+1, e+k+1⟩)
  · have h := r5r1_drain (3*k+1) 0 0 (e+k+1)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  finish

-- Main transition for d = 2*k+1 (odd case):
-- (0,0,0,2*k+1,e+1) -> (0,0,0,3*k+2,e+k+2)
theorem trans_odd (k : ℕ) (e : ℕ) :
    ⟨0, 0, 0, 2*k+1, e+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k+2, e+k+2⟩ := by
  -- R5: -> (0,2,0,2k+2,e). R2: -> (2,1,2,2k+1,e).
  step fm; step fm
  -- Interleave 2k+1 times: (2,1,2,2k+1,e) -> (2k+3,1,4k+4,0,e+2k+1)
  apply stepStar_trans (c₂ := ⟨2*k+3, 1, 4*k+4, 0, e+2*k+1⟩)
  · have h := interleave (2*k+1) 2 2 0 e
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Odd drain: (2*(k+1)+1, 1, (3k+2)+(k+1)+1, 0, e+2k+1) -> (0, 0, 3k+2, 0, e+4k+4)
  apply stepStar_trans (c₂ := ⟨0, 0, 3*k+2, 0, e+4*k+4⟩)
  · have h := drain_odd (k+1) (3*k+2) (e+2*k+1)
    convert h using 2; ring_nf
  -- R5-R1 drain: (0, 0, 0+(3k+2), 0, (e+k+2)+(3k+2)) -> (0, 0, 0, 3k+2, e+k+2)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 3*k+2, e+k+2⟩)
  · have h := r5r1_drain (3*k+2) 0 0 (e+k+2)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  finish

-- Combined main transition
theorem main_trans (d e : ℕ) :
    ∃ d' e', (⟨0, 0, 0, d, e+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d', e'+1⟩) := by
  rcases Nat.even_or_odd d with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨3*k+1, e+k, ?_⟩
    have h := trans_even k e; convert h using 2; ring_nf
  · exact ⟨3*k+2, e+k+1, trans_odd k e⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e+1⟩)
  · intro c ⟨d, e, hq⟩
    subst hq
    obtain ⟨d', e', hstep⟩ := main_trans d e
    exact ⟨⟨0, 0, 0, d', e'+1⟩, ⟨d', e', rfl⟩, hstep⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_127
