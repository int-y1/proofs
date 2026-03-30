import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #747: [35/6, 4/55, 1859/2, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  2
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_747

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1) (f + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d f)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e f, ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

-- Opening: R3 + R4 + R5 + R1 + R2
-- From (n+2, 0, 0, n+1, 0, F) to (2, n+1, 0, 1, n+1, F + 2*n + 3)
-- f goes: F -> F + 2*(n+2) [R3 adds 2 per step, n+2 steps]
--       -> same [R4 doesn't change f]
--       -> F + 2*(n+2) - 1 = F + 2*n + 3 [R5 subtracts 1]
--       -> same [R1, R2 don't change f]
theorem opening_phase (n F : ℕ) :
    ⟨n + 2, 0, 0, n + 1, 0, F⟩ [fm]⊢⁺ ⟨2, n + 1, 0, 1, n + 1, F + 2 * n + 3⟩ := by
  -- R3 chain (n+2 steps)
  have h1 := r3_chain (a := 0) (n + 2) (n + 1) 0 F
  simp only [Nat.zero_add] at h1
  -- R4 chain (n+1 steps)
  have h2 := r4_chain (d := 0) (n + 1) 0 (n + 2) (F + 2 * (n + 2))
  simp only [Nat.zero_add] at h2
  -- R5: f component is F + 2*(n+2), and we need it as (...) + 1
  -- R5: (0, n+1, 0, 0, n+2, F+2*(n+2)) => (1, n+2, 0, 0, n+2, F+2*(n+2)-1)
  -- F+2*(n+2)-1 = F+2*n+3
  -- R1: (1, n+2, 0, 0, n+2, F+2*n+3) => (0, n+1, 1, 1, n+2, F+2*n+3)
  -- R2: (0, n+1, 1, 1, n+2, F+2*n+3) => (2, n+1, 0, 1, n+1, F+2*n+3)
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  rw [show F + 2 * (n + 2) = (F + 2 * n + 3) + 1 from by ring,
      show n + 1 = (n) + 1 from by ring]
  step fm
  rw [show n + 1 + 1 = (n + 1) + 1 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  step fm
  rw [show (n + 1 : ℕ) + 1 = (n + 1) + 1 from by ring]
  step fm; finish

-- Even case tail: after opening and R1R1R2 chain
-- (2, 1, m, 2*m+1, 1+m, F) -> R1 -> R2 drain -> (2*m+3, 0, 0, 2*m+2, 0, F)
theorem even_tail (m F : ℕ) :
    ⟨2, 1, m, 2 * m + 1, 1 + m, F⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, F⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show 1 + m = m + 1 from by ring]
  have h := r2_drain (c := 0) (e := 0) (m + 1) 1 (2 * m + 2) F
  simp only [Nat.zero_add] at h
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
  exact h

-- Odd case tail: after opening and R1R1R2 chain
-- (2, 0, m+1, 2*m+3, m+1, F) -> R2 drain -> (2*m+4, 0, 0, 2*m+3, 0, F)
theorem odd_tail (m F : ℕ) :
    ⟨2, 0, m + 1, 2 * m + 3, m + 1, F⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 2 * m + 3, 0, F⟩ := by
  have h := r2_drain (c := 0) (e := 0) (m + 1) 2 (2 * m + 3) F
  simp only [Nat.zero_add] at h
  rw [show 2 + 2 * (m + 1) = 2 * m + 4 from by ring] at h
  exact h

theorem main_trans_even (m : ℕ) :
    ⟨2 * m + 2, 0, 0, 2 * m + 1, 0, (2 * m + 1) ^ 2⟩ [fm]⊢⁺
    ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, (2 * m + 2) ^ 2⟩ := by
  have hop := opening_phase (2 * m) ((2 * m + 1) ^ 2)
  rw [show (2 * m + 1) ^ 2 + 2 * (2 * m) + 3 = (2 * m + 2) ^ 2 from by ring] at hop
  apply stepPlus_stepStar_stepPlus hop
  -- State: (2, 2*m+1, 0, 1, 2*m+1, (2*m+2)^2)
  have hchain := r1r1r2_chain m 1 0 1 (1 + m) ((2 * m + 2) ^ 2)
  rw [show 1 + 2 * m = 2 * m + 1 from by ring,
      show (1 + m) + m = 2 * m + 1 from by ring] at hchain
  apply stepStar_trans hchain
  simp only [Nat.zero_add]
  exact even_tail m ((2 * m + 2) ^ 2)

theorem main_trans_odd (m : ℕ) :
    ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, (2 * m + 2) ^ 2⟩ [fm]⊢⁺
    ⟨2 * m + 4, 0, 0, 2 * m + 3, 0, (2 * m + 3) ^ 2⟩ := by
  have hop := opening_phase (2 * m + 1) ((2 * m + 2) ^ 2)
  rw [show (2 * m + 2) ^ 2 + 2 * (2 * m + 1) + 3 = (2 * m + 3) ^ 2 from by ring,
      show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
      show 2 * m + 1 + 1 = 2 * m + 2 from by ring] at hop
  apply stepPlus_stepStar_stepPlus hop
  -- State: (2, 2*m+2, 0, 1, 2*m+2, (2*m+3)^2)
  have hchain := r1r1r2_chain (m + 1) 0 0 1 (m + 1) ((2 * m + 3) ^ 2)
  rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
      show (m + 1) + (m + 1) = 2 * m + 2 from by ring] at hchain
  apply stepStar_trans hchain
  simp only [Nat.zero_add]
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  exact odd_tail m ((2 * m + 3) ^ 2)

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, n + 1, 0, (n + 1) ^ 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0, (n + 2) ^ 2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    convert main_trans_even m using 2
  · subst hm
    convert main_trans_odd m using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 0, 4⟩) (by execute fm 12)
  rw [show (3 : ℕ) = 1 + 2 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show (4 : ℕ) = (1 + 1) ^ 2 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0, (n + 1) ^ 2⟩) 1
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_747
