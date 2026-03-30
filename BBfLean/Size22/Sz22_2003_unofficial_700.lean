import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #700: [35/6, 4/55, 121/2, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_700

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem interleave_even : ∀ k, ∀ c d e, ⟨2, 2 * k + 2, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 2, d + 2 * k + 2, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem interleave_odd : ∀ k, ∀ c d e, ⟨2, 2 * k + 1, c, d, e + k⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem trans_odd_to_even (m : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, (m + 1) * (2 * m + 5)⟩ [fm]⊢⁺
    ⟨0, 2 * m + 2, 0, 0, (2 * m + 3) * (m + 3)⟩ := by
  -- R5 + R2 opening
  rw [show (m + 1) * (2 * m + 5) = (2 * m * m + 7 * m + 3) + 1 + 1 from by ring,
      show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm -- R5: (0, 2*m+2, 1, 0, 2*m*m+7*m+3+1)
  rw [show 2 * m * m + 7 * m + 3 + 1 = (2 * m * m + 7 * m + 3) + 1 from by ring]
  step fm -- R2: (2, 2*m+2, 0, 0, 2*m*m+7*m+3)
  -- interleave_even with k=m
  rw [show 2 * m * m + 7 * m + 3 = (2 * m * m + 6 * m + 3) + m from by ring]
  apply stepStar_trans (interleave_even m 0 0 (2 * m * m + 6 * m + 3))
  -- r2_chain with k=m+2
  rw [show 0 + m + 2 = 0 + (m + 2) from by ring,
      show 2 * m * m + 6 * m + 3 = (2 * m * m + 5 * m + 1) + (m + 2) from by ring]
  apply stepStar_trans (r2_chain (m + 2) 0 0 (0 + 2 * m + 2) (2 * m * m + 5 * m + 1))
  -- r3_chain with k=2*m+4
  rw [show 0 + 2 * (m + 2) = 0 + (2 * m + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 4) 0 (0 + 2 * m + 2) (2 * m * m + 5 * m + 1))
  -- r4_chain with k=2*m+2
  rw [show 0 + 2 * m + 2 = 2 * m + 2 from by ring,
      show 2 * m * m + 5 * m + 1 + 2 * (2 * m + 4) = (2 * m + 3) * (m + 3) from by ring]
  have key := r4_chain (2 * m + 2) 0 0 ((2 * m + 3) * (m + 3))
  simp only [Nat.zero_add] at key
  exact key

theorem trans_even_to_odd (m : ℕ) :
    ⟨0, 2 * m + 2, 0, 0, (2 * m + 3) * (m + 3)⟩ [fm]⊢⁺
    ⟨0, 2 * m + 3, 0, 0, (m + 2) * (2 * m + 7)⟩ := by
  -- R5 + R2 opening
  rw [show (2 * m + 3) * (m + 3) = (2 * m * m + 9 * m + 7) + 1 + 1 from by ring,
      show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm -- R5
  rw [show 2 * m * m + 9 * m + 7 + 1 = (2 * m * m + 9 * m + 7) + 1 from by ring]
  step fm -- R2
  -- interleave_odd with k=m+1
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring,
      show 2 * m * m + 9 * m + 7 = (2 * m * m + 8 * m + 6) + (m + 1) from by ring]
  apply stepStar_trans (interleave_odd (m + 1) 0 0 (2 * m * m + 8 * m + 6))
  -- r2_chain with k=m+2
  rw [show 0 + (m + 1) + 1 = 0 + (m + 2) from by ring,
      show 2 * m * m + 8 * m + 6 = (2 * m * m + 7 * m + 4) + (m + 2) from by ring]
  apply stepStar_trans (r2_chain (m + 2) 1 0 (0 + 2 * (m + 1) + 1) (2 * m * m + 7 * m + 4))
  -- r3_chain with k=2*m+5
  rw [show 1 + 2 * (m + 2) = 0 + (2 * m + 5) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 5) 0 (0 + 2 * (m + 1) + 1) (2 * m * m + 7 * m + 4))
  -- r4_chain with k=2*m+3
  rw [show 0 + 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
      show 2 * m * m + 7 * m + 4 + 2 * (2 * m + 5) = (m + 2) * (2 * m + 7) from by ring]
  have key := r4_chain (2 * m + 3) 0 0 ((m + 2) * (2 * m + 7))
  simp only [Nat.zero_add] at key
  exact key

theorem main_trans (m : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, (m + 1) * (2 * m + 5)⟩ [fm]⊢⁺
    ⟨0, 2 * m + 3, 0, 0, (m + 2) * (2 * m + 7)⟩ :=
  stepPlus_trans (trans_odd_to_even m) (trans_even_to_odd m)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 5⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 2 * m + 1, 0, 0, (m + 1) * (2 * m + 5)⟩) 0
  intro m; exact ⟨m + 1, main_trans m⟩

end Sz22_2003_unofficial_700
