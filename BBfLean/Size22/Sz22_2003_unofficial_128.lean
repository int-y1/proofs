import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #128: [1/45, 1078/15, 3/7, 275/2, 3/11]

Vector representation:
```
 0 -2 -1  0  0
 1 -1 -1  2  1
 0  1  0 -1  0
-1  0  2  0  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_128

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: d → b (when c = 0)
theorem d_to_b : ∀ k b d e a, ⟨a, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e a; exists 0
  | succ k ih =>
    intro b d e a
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R4 repeated: a → c, e (when b = 0, d = 0)
theorem a_to_c : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Ascending phase: interleaved R3+R2, consuming c and producing a, d, e
-- (a, 0, c+k, a+1, e) →* (a+k, 0, c, a+k+1, e+k)
theorem ascending : ∀ k a c e, ⟨a, 0, c + k, a + 1, e⟩ [fm]⊢* ⟨a + k, 0, c, a + k + 1, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show a + 1 = (a) + 1 from by ring]
    step fm
    rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- Cleanup B≥4: (a+1, b+4, 0, 0, e) →* (a, b, 0, 0, e+1) in 3 steps
-- R4 → R1 → R1
theorem cleanup_b4 : ∀ a b e, ⟨a + 1, b + 4, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + 1⟩ := by
  intro a b e
  rw [show b + 4 = (b + 2) + 2 from by ring]
  step fm
  rw [show b + 2 + 2 = (b + 2) + 2 from by ring]
  step fm
  rw [show b + 2 = (b) + 2 from by ring]
  step fm
  finish

-- Cleanup loop: iterate cleanup_b4
-- (a+k, b+4*k, 0, 0, e) →* (a, b, 0, 0, e+k)
theorem cleanup_loop : ∀ k a b e, ⟨a + k, b + 4 * k, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring]
    apply stepStar_trans (cleanup_b4 _ _ _)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Cleanup B=3: (a+1, 3, 0, 0, e) →* (a+1, 2, 0, 0, e+2) in 5 steps
-- R4 → R1 → R2 → R3 → R3
theorem cleanup_b3 : ∀ a e, ⟨a + 1, 3, 0, 0, e⟩ [fm]⊢* ⟨a + 1, 2, 0, 0, e + 2⟩ := by
  intro a e
  rw [show (3 : ℕ) = 1 + 2 from by ring]
  step fm
  rw [show (3 : ℕ) = 1 + 2 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Cleanup B=2: (a+1, 2, 0, 0, e) →* (0, 0, 2*a+1, 0, e+a+1)
-- R4 → R1 → a_to_c
theorem cleanup_b2 : ∀ a e, ⟨a + 1, 2, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 1, 0, e + a + 1⟩ := by
  intro a e
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  have h := a_to_c a 0 1 (e + 1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- Cleanup B=1: (a+1, 1, 0, 0, e) →* (0, 0, 2*a+3, 0, e+a+7)
-- R4 → R2 → R3 → R2 → d_to_b(3) → cleanup_b3 → cleanup_b2
theorem cleanup_b1 : ∀ a e, ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3, 0, e + a + 7⟩ := by
  intro a e
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨a + 2, 3, 0, 0, e + 3⟩)
  · have h := d_to_b 3 0 0 (e + 3) (a + 2)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (cleanup_b3 (a + 1) (e + 3))
  apply stepStar_trans (cleanup_b2 (a + 1) (e + 5))
  ring_nf; finish

-- Cleanup B=0: just a_to_c
-- (a, 0, 0, 0, e) →* (0, 0, 2*a, 0, e+a)
theorem cleanup_b0 : ∀ a e, ⟨a, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a, 0, e + a⟩ := by
  intro a e
  have h := a_to_c a 0 0 e
  simp only [Nat.zero_add] at h; exact h

-- Full ascending phase: (0, 0, C+1, 0, E+1) →* (C+1, 0, 0, C+2, E+C+1)
-- R5 → R2 → ascending(C)
theorem full_ascending : ∀ C E, ⟨0, 0, C + 1, 0, E + 1⟩ [fm]⊢* ⟨C + 1, 0, 0, C + 2, E + C + 1⟩ := by
  intro C E
  rw [show E + 1 = E + 1 from by ring]
  step fm
  rw [show C + 1 = C + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨1 + C, 0, 0, 1 + C + 1, E + 1 + C⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    have h := ascending C 1 0 (E + 1)
    simp only [Nat.zero_add] at h; exact h
  ring_nf; finish

-- Main transition for C%4=0: C=4*(m+1)
-- (0, 0, 4*m+4, 0, E+1) ⊢⁺ (0, 0, 6*m+7, 0, E+8*m+14)
theorem main_c4m (m E : ℕ) : ⟨0, 0, 4 * m + 4, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 7, 0, E + 8 * m + 14⟩ := by
  rw [show E + 1 = (E) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 4, 0, E⟩)
    (by simp [fm])
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨4 * m + 4, 0, 0, 4 * m + 5, E + 4 * m + 4⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    have h := ascending (4 * m + 3) 1 0 (E + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨4 * m + 4, 4 * m + 5, 0, 0, E + 4 * m + 4⟩)
  · have h := d_to_b (4 * m + 5) 0 0 (E + 4 * m + 4) (4 * m + 4)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨3 * m + 3, 1, 0, 0, E + 5 * m + 5⟩)
  · rw [show 4 * m + 4 = (3 * m + 3) + (m + 1) from by ring,
        show 4 * m + 5 = 1 + 4 * (m + 1) from by ring]
    apply stepStar_trans (cleanup_loop (m + 1) (3 * m + 3) 1 (E + 4 * m + 4))
    ring_nf; finish
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (cleanup_b1 (3 * m + 2) (E + 5 * m + 5))
  ring_nf; finish

-- Main transition for C%4=1: C=4*m+1
-- (0, 0, 4*m+1, 0, E+1) ⊢⁺ (0, 0, 6*m+1, 0, E+8*m+2)
theorem main_c4m1 (m E : ℕ) : ⟨0, 0, 4 * m + 1, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 1, 0, E + 8 * m + 2⟩ := by
  rw [show E + 1 = (E) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 1, 0, E⟩)
    (by simp [fm])
  rw [show 4 * m + 1 = (4 * m) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨4 * m + 1, 0, 0, 4 * m + 2, E + 4 * m + 1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    have h := ascending (4 * m) 1 0 (E + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨4 * m + 1, 4 * m + 2, 0, 0, E + 4 * m + 1⟩)
  · have h := d_to_b (4 * m + 2) 0 0 (E + 4 * m + 1) (4 * m + 1)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨3 * m + 1, 2, 0, 0, E + 5 * m + 1⟩)
  · rw [show 4 * m + 1 = (3 * m + 1) + m from by ring,
        show 4 * m + 2 = 2 + 4 * m from by ring]
    apply stepStar_trans (cleanup_loop m (3 * m + 1) 2 (E + 4 * m + 1))
    ring_nf; finish
  rw [show 3 * m + 1 = (3 * m) + 1 from by ring]
  apply stepStar_trans (cleanup_b2 (3 * m) (E + 5 * m + 1))
  ring_nf; finish

-- Main transition for C%4=2: C=4*m+2
-- (0, 0, 4*m+2, 0, E+1) ⊢⁺ (0, 0, 6*m+3, 0, E+8*m+6)
theorem main_c4m2 (m E : ℕ) : ⟨0, 0, 4 * m + 2, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 3, 0, E + 8 * m + 6⟩ := by
  rw [show E + 1 = (E) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 2, 0, E⟩)
    (by simp [fm])
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨4 * m + 2, 0, 0, 4 * m + 3, E + 4 * m + 2⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    have h := ascending (4 * m + 1) 1 0 (E + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨4 * m + 2, 4 * m + 3, 0, 0, E + 4 * m + 2⟩)
  · have h := d_to_b (4 * m + 3) 0 0 (E + 4 * m + 2) (4 * m + 2)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨3 * m + 2, 3, 0, 0, E + 5 * m + 2⟩)
  · rw [show 4 * m + 2 = (3 * m + 2) + m from by ring,
        show 4 * m + 3 = 3 + 4 * m from by ring]
    apply stepStar_trans (cleanup_loop m (3 * m + 2) 3 (E + 4 * m + 2))
    ring_nf; finish
  apply stepStar_trans (c₂ := ⟨3 * m + 2, 2, 0, 0, E + 5 * m + 4⟩)
  · rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring]
    apply stepStar_trans (cleanup_b3 (3 * m + 1) (E + 5 * m + 2))
    ring_nf; finish
  rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring]
  apply stepStar_trans (cleanup_b2 (3 * m + 1) (E + 5 * m + 4))
  ring_nf; finish

-- Main transition for C%4=3: C=4*m+3
-- (0, 0, 4*m+3, 0, E+1) ⊢⁺ (0, 0, 6*m+4, 0, E+8*m+6)
theorem main_c4m3 (m E : ℕ) : ⟨0, 0, 4 * m + 3, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 4, 0, E + 8 * m + 6⟩ := by
  rw [show E + 1 = (E) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 3, 0, E⟩)
    (by simp [fm])
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨4 * m + 3, 0, 0, 4 * m + 4, E + 4 * m + 3⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    have h := ascending (4 * m + 2) 1 0 (E + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨4 * m + 3, 4 * m + 4, 0, 0, E + 4 * m + 3⟩)
  · have h := d_to_b (4 * m + 4) 0 0 (E + 4 * m + 3) (4 * m + 3)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨3 * m + 2, 0, 0, 0, E + 5 * m + 4⟩)
  · rw [show 4 * m + 3 = (3 * m + 2) + (m + 1) from by ring,
        show 4 * m + 4 = 0 + 4 * (m + 1) from by ring]
    apply stepStar_trans (cleanup_loop (m + 1) (3 * m + 2) 0 (E + 4 * m + 3))
    ring_nf; finish
  apply stepStar_trans (cleanup_b0 (3 * m + 2) (E + 5 * m + 4))
  ring_nf; finish

-- Combined transition: for any C >= 1 and E >= 0, (0, 0, C+1, 0, E+1) ⊢⁺ some canonical state
theorem main_trans (C E : ℕ) : ∃ C' E', ⟨0, 0, C + 1, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, C' + 1, 0, E' + 1⟩ := by
  rcases Nat.even_or_odd C with ⟨K, hK⟩ | ⟨K, hK⟩
  · rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩
    · -- C = 4M → C+1 = 4M+1
      refine ⟨6 * M, E + 8 * M + 1, ?_⟩
      rw [show C + 1 = 4 * M + 1 from by omega]
      exact main_c4m1 M E
    · -- C = 4M+2 → C+1 = 4M+3
      refine ⟨6 * M + 3, E + 8 * M + 5, ?_⟩
      rw [show C + 1 = 4 * M + 3 from by omega]
      exact main_c4m3 M E
  · rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩
    · -- C = 4M+1 → C+1 = 4M+2
      refine ⟨6 * M + 2, E + 8 * M + 5, ?_⟩
      rw [show C + 1 = 4 * M + 2 from by omega]
      exact main_c4m2 M E
    · -- C = 4M+3 → C+1 = 4M+4
      refine ⟨6 * M + 6, E + 8 * M + 13, ?_⟩
      rw [show C + 1 = 4 * M + 4 from by omega]
      exact main_c4m M E

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C E, q = ⟨0, 0, C + 1, 0, E + 1⟩)
  · intro q ⟨C, E, hq⟩
    subst hq
    obtain ⟨C', E', h⟩ := main_trans C E
    exact ⟨⟨0, 0, C' + 1, 0, E' + 1⟩, ⟨C', E', rfl⟩, h⟩
  · exact ⟨1, 0, rfl⟩

end Sz22_2003_unofficial_128
