import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1144: [5/6, 44/35, 539/2, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  1
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1144

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a (d + 2) (e + 1)); ring_nf; finish

theorem r4_drain : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]; step fm
  apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

theorem r1r1r2_loop : ∀ k b c d e, ⟨2, b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih b (c + 1) d (e + 1)); ring_nf; finish

theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 2) c d (e + 1)); ring_nf; finish

theorem r3r2r2_chain : ∀ k a c e, ⟨a + 1, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, c, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 3) c (e + 3)); ring_nf; finish

theorem interleaved_even : ∀ g r, ⟨0, 2 * g + 2 * r + 2, 0, g + 2 * r + 2, 0⟩ [fm]⊢*
    ⟨2 * r + 1, 0, g + 1, 0, g + 2 * r + 2⟩ := by
  intro g r
  step fm; step fm; step fm
  rw [show 2 * g + 2 * r + 1 = 1 + 2 * (g + r) from by ring,
      show g + 2 * r = r + (g + r) from by ring]
  apply stepStar_trans (r1r1r2_loop (g + r) 1 0 r 2)
  simp only [Nat.zero_add]
  rw [show 2 + (g + r) = g + r + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  have h := r2_chain r 1 (g + 1) 0 (g + r + 2)
  simp only [Nat.zero_add] at h
  ring_nf at h ⊢
  exact h

theorem interleaved_odd : ∀ g r, ⟨0, 2 * g + 2 * r + 3, 0, g + 2 * r + 3, 0⟩ [fm]⊢*
    ⟨2 * r + 2, 0, g + 1, 0, g + 2 * r + 3⟩ := by
  intro g r
  step fm; step fm; step fm
  rw [show 2 * g + 2 * r + 2 = 0 + 2 * (g + r + 1) from by ring,
      show g + 2 * r + 1 = r + (g + r + 1) from by ring]
  apply stepStar_trans (r1r1r2_loop (g + r + 1) 0 0 r 2)
  simp only [Nat.zero_add]
  rw [show 2 + (g + r + 1) = g + r + 3 from by ring]
  have h := r2_chain r 2 (g + 1) 0 (g + r + 3)
  simp only [Nat.zero_add] at h
  ring_nf at h ⊢
  exact h

theorem c1_to_drain : ∀ a e, ⟨a + 1, 0, 1, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 5, a + e + 4⟩ := by
  intro a e
  step fm
  step fm
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (r3_drain (a + 2) 0 1 (e + 2))
  ring_nf; finish

theorem main_trans : ∀ m k, ⟨m + k + 1, 0, 0, 0, m + 3 * k + 1⟩ [fm]⊢⁺
    ⟨4 * m + 7 * k + 6, 0, 0, 0, 4 * m + 9 * k + 8⟩ := by
  intro m k
  rw [show m + k + 1 = (m + k) + 1 from by ring]
  step fm
  rw [show m + 3 * k + 1 + 1 = m + 3 * k + 2 from by ring,
      show m + k = 0 + (m + k) from by ring]
  apply stepStar_trans (r3_drain (m + k) 0 2 (m + 3 * k + 2))
  rw [show 2 + 2 * (m + k) = 2 * m + 2 * k + 2 from by ring,
      show m + 3 * k + 2 + (m + k) = 0 + (2 * m + 4 * k + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * m + 4 * k + 2) 0 (2 * m + 2 * k + 2) 0)
  rw [show 0 + (2 * m + 4 * k + 2) = 2 * (2 * k) + 2 * m + 2 from by ring,
      show 2 * m + 2 * k + 2 = 2 * k + 2 * m + 2 from by ring]
  apply stepStar_trans (interleaved_even (2 * k) m)
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r3r2r2_chain k (2 * m) 1 (2 * k + 2 * m + 2))
  rw [show 2 * m + 1 + 3 * k = (2 * m + 3 * k) + 1 from by ring,
      show 2 * k + 2 * m + 2 + 3 * k = 2 * m + 5 * k + 2 from by ring]
  apply stepStar_trans (c1_to_drain (2 * m + 3 * k) (2 * m + 5 * k + 2))
  rw [show 2 * (2 * m + 3 * k) + 5 = 4 * m + 6 * k + 5 from by ring,
      show 2 * m + 3 * k + (2 * m + 5 * k + 2) + 4 = 0 + (4 * m + 8 * k + 6) from by ring]
  apply stepStar_trans (r4_drain (4 * m + 8 * k + 6) 0 (4 * m + 6 * k + 5) 0)
  rw [show 0 + (4 * m + 8 * k + 6) = 2 * (2 * k + 1) + 2 * (2 * m + 2 * k + 1) + 2 from by ring,
      show 4 * m + 6 * k + 5 = (2 * k + 1) + 2 * (2 * m + 2 * k + 1) + 2 from by ring]
  apply stepStar_trans (interleaved_even (2 * k + 1) (2 * m + 2 * k + 1))
  rw [show 2 * (2 * m + 2 * k + 1) + 1 = (4 * m + 4 * k + 2) + 1 from by ring,
      show (2 * k + 1) + 1 = 0 + 2 * (k + 1) from by ring,
      show (2 * k + 1) + 2 * (2 * m + 2 * k + 1) + 2 = 4 * m + 6 * k + 5 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) (4 * m + 4 * k + 2) 0 (4 * m + 6 * k + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m k, q = ⟨m + k + 1, 0, 0, 0, m + 3 * k + 1⟩)
  · intro c ⟨m, k, hq⟩; subst hq
    exact ⟨⟨4 * m + 7 * k + 6, 0, 0, 0, 4 * m + 9 * k + 8⟩,
      ⟨4 * m + 6 * k + 4, k + 1, by ring_nf⟩,
      main_trans m k⟩
  · exact ⟨1, 0, by ring_nf⟩
