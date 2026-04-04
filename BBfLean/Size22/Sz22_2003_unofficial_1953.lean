import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1953: [9/70, 7/15, 275/7, 2/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1 -1  1  0
 0  0  2 -1  1
 1  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1953

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (c + 2) d (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) c e); ring_nf; finish

theorem b_drain_even : ∀ k, ∀ d, ⟨0, 2 * k, 0, d + 1, d⟩ [fm]⊢* ⟨0, 0, 0, d + k + 1, d + k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem b_drain_odd : ∀ k, ∀ d, ⟨0, 2 * k + 1, 0, d + 1, d⟩ [fm]⊢* ⟨0, 1, 0, d + k + 1, d + k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b c, ⟨a + k, b + 1, c + 2 * k, 0, 0⟩ [fm]⊢*
    ⟨a, b + 1 + k, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) c); ring_nf; finish

theorem macro5 : ⟨a + 2, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 2, 0, 0, 0⟩ := by
  execute fm 5

theorem macro5_chain : ∀ k, ∀ a b, ⟨a + k + 1, b, 0, 0, 0⟩ [fm]⊢*
    ⟨a + 1, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (macro5 (a := a + k) (b := b)))
    apply stepStar_trans (ih a (b + 2)); ring_nf; finish

theorem opening : ⟨a + 2, 0, a + 3, 0, 0⟩ [fm]⊢⁺ ⟨a, 3, a + 2, 0, 0⟩ := by
  execute fm 2

theorem spiral_even (m : ℕ) :
    ⟨2 * m + 6, 0, 2 * m + 7, 0, 0⟩ [fm]⊢⁺ ⟨m + 1, m + 6, 0, 0, 0⟩ := by
  rw [show 2 * m + 6 = (2 * m + 4) + 2 from by ring,
      show 2 * m + 7 = (2 * m + 4) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (a := 2 * m + 4))
  have h := r2r1_chain (m + 3) (m + 1) 2 0
  rw [show (m + 1) + (m + 3) = 2 * m + 4 from by ring,
      show (2 : ℕ) + 1 = 3 from by ring,
      show 0 + 2 * (m + 3) = 2 * m + 6 from by ring,
      show 2 + 1 + (m + 3) = m + 6 from by ring] at h
  exact h

theorem spiral_odd (m : ℕ) :
    ⟨2 * m + 5, 0, 2 * m + 6, 0, 0⟩ [fm]⊢⁺ ⟨m + 1, m + 5, 0, 0, 0⟩ := by
  rw [show 2 * m + 5 = (2 * m + 3) + 2 from by ring,
      show 2 * m + 6 = (2 * m + 3) + 3 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (a := 2 * m + 3))
  have h := r2r1_chain (m + 2) (m + 1) 2 1
  rw [show (m + 1) + (m + 2) = 2 * m + 3 from by ring,
      show (2 : ℕ) + 1 = 3 from by ring,
      show 1 + 2 * (m + 2) = 2 * m + 5 from by ring,
      show 2 + 1 + (m + 2) = m + 5 from by ring] at h
  apply stepStar_trans h
  rw [show m + 5 = (m + 4) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem phase_even (n : ℕ) :
    ⟨0, 2 * (n + 2), 0, 1, 0⟩ [fm]⊢* ⟨2 * n + 5, 0, 2 * n + 6, 0, 0⟩ := by
  have h1 := b_drain_even (n + 2) 0
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show 0 + (n + 2) = n + 2 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring] at h1
  have h2 := r3_chain (n + 3) 0 0 (n + 2)
  rw [show 0 + (n + 3) = n + 3 from by ring,
      show 0 + 2 * (n + 3) = 2 * n + 6 from by ring,
      show (n + 2) + (n + 3) = 2 * n + 5 from by ring] at h2
  have h3 := r4_chain (2 * n + 5) 0 (2 * n + 6) 0
  rw [show 0 + (2 * n + 5) = 2 * n + 5 from by ring] at h3
  apply stepStar_trans h1
  apply stepStar_trans h2
  apply stepStar_trans h3
  ring_nf; finish

theorem phase_odd (n : ℕ) :
    ⟨0, 2 * (n + 2) + 1, 0, 1, 0⟩ [fm]⊢* ⟨2 * n + 6, 0, 2 * n + 7, 0, 0⟩ := by
  have h1 := b_drain_odd (n + 2) 0
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show 0 + (n + 2) = n + 2 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring] at h1
  apply stepStar_trans h1
  rw [show n + 3 = (n + 2) + 1 from by ring]
  step fm; step fm
  rw [show n + 2 + 1 = n + 3 from by ring]
  have h2 := r3_chain (n + 3) 1 0 (n + 3)
  rw [show 0 + (n + 3) = n + 3 from by ring,
      show 1 + 2 * (n + 3) = 2 * n + 7 from by ring,
      show (n + 3) + (n + 3) = 2 * n + 6 from by ring] at h2
  have h3 := r4_chain (2 * n + 6) 0 (2 * n + 7) 0
  rw [show 0 + (2 * n + 6) = 2 * n + 6 from by ring] at h3
  apply stepStar_trans h2
  apply stepStar_trans h3
  ring_nf; finish

theorem drain_ab (n : ℕ) :
    ⟨n + 1, n + 5, 0, 0, 0⟩ [fm]⊢* ⟨0, 3 * n + 6, 0, 1, 0⟩ := by
  have h := macro5_chain n 0 (n + 5)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show n + 5 + 2 * n = 3 * n + 5 from by ring,
      show 0 + 1 = 1 from by ring] at h
  apply stepStar_trans h
  step fm; ring_nf; finish

theorem drain_ab' (n : ℕ) :
    ⟨n + 1, n + 6, 0, 0, 0⟩ [fm]⊢* ⟨0, 3 * n + 7, 0, 1, 0⟩ := by
  have h := macro5_chain n 0 (n + 6)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show n + 6 + 2 * n = 3 * n + 6 from by ring,
      show 0 + 1 = 1 from by ring] at h
  apply stepStar_trans h
  step fm; ring_nf; finish

theorem full_even (n : ℕ) :
    ⟨0, 2 * n + 4, 0, 1, 0⟩ [fm]⊢⁺ ⟨0, 3 * n + 6, 0, 1, 0⟩ := by
  rw [show 2 * n + 4 = 2 * (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (phase_even n)
  apply stepPlus_stepStar_stepPlus (spiral_odd n)
  exact drain_ab n

theorem full_odd (n : ℕ) :
    ⟨0, 2 * n + 5, 0, 1, 0⟩ [fm]⊢⁺ ⟨0, 3 * n + 7, 0, 1, 0⟩ := by
  rw [show 2 * n + 5 = 2 * (n + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase_odd n)
  apply stepPlus_stepStar_stepPlus (spiral_even n)
  exact drain_ab' n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 0, 1, 0⟩)
  · execute fm 40
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, n + 4, 0, 1, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      refine ⟨⟨0, 3 * k + 6, 0, 1, 0⟩, ⟨3 * k + 2, by ring_nf⟩, ?_⟩
      rw [show k + k + 4 = 2 * k + 4 from by ring]
      exact full_even k
    · subst hk
      refine ⟨⟨0, 3 * k + 7, 0, 1, 0⟩, ⟨3 * k + 3, by ring_nf⟩, ?_⟩
      exact full_odd k
  · exact ⟨0, rfl⟩
