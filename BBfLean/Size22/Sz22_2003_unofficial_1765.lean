import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1765: [9/10, 22/21, 4459/2, 5/11, 3/13]

Vector representation:
```
-1  2 -1  0  0  0
 1 -1  0 -1  1  0
-1  0  0  3  0  1
 0  0  1  0 -1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1765

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+3, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem e_to_c : ∀ k c d e f, ⟨(0 : ℕ), 0, c, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e f)
    ring_nf; finish

theorem r2r1_chain : ∀ k b d e f, ⟨(0 : ℕ), b + 1, k, d + k, e, f⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · ring_nf; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) d (e + 1) f)
    ring_nf; finish

theorem r3_chain : ∀ k a d e f, ⟨a + k, (0 : ℕ), 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 3) e (f + 1))
    ring_nf; finish

theorem drain : ∀ b a d e f,
    ⟨(a : ℕ), b, 0, d + 1, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 3 * a + 2 * b, e + b, f + a + b⟩ := by
  intro b; induction' b with b ih <;> intro a d e f
  · rw [show d + 1 + 3 * a + 2 * 0 = (d + 1) + 3 * a from by ring,
        show e + 0 = e from by ring, show f + a + 0 = f + a from by ring]
    have := r3_chain a 0 (d + 1) e f
    simpa using this
  · rcases d with _ | d'
    · step fm
      step fm
      rw [show (3 : ℕ) = 2 + 1 from by ring]
      apply stepStar_trans (ih a 2 (e + 1) (f + 1))
      ring_nf; finish
    · rw [show d' + 1 + 1 = (d' + 1) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a + 1) d' (e + 1) f)
      ring_nf; finish

theorem main_trans : ∀ G n,
    ⟨(0 : ℕ), 0, 0, G + 2 * n + 8, G + n + 3, G + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * G + 3 * n + 13, 2 * G + 2 * n + 7, 2 * G + n + 5⟩ := by
  intro G n
  -- Phase 1: R4 chain (G+n+3 steps)
  -- (0, 0, 0, G+2n+8, G+n+3, G+2) →* (0, 0, G+n+3, G+2n+8, 0, G+2)
  have phase1 : ⟨(0 : ℕ), 0, 0, G + 2 * n + 8, G + n + 3, G + 2⟩ [fm]⊢*
      ⟨0, 0, G + n + 3, G + 2 * n + 8, 0, G + 2⟩ := by
    rw [show G + n + 3 = 0 + (G + n + 3) from by ring]
    exact e_to_c (G + n + 3) 0 (G + 2 * n + 8) 0 (G + 2)
  -- Phase 2: R5 step
  -- (0, 0, G+n+3, G+2n+8, 0, G+2) → (0, 1, G+n+3, G+2n+8, 0, G+1)
  have phase2 : ⟨(0 : ℕ), 0, G + n + 3, G + 2 * n + 8, 0, G + 2⟩ [fm]⊢
      ⟨0, 1, G + n + 3, G + 2 * n + 8, 0, G + 1⟩ := by
    rw [show G + 2 = (G + 1) + 1 from by ring]; simp [fm]
  -- Phase 3: R2+R1 interleave
  -- (0, 1, G+n+3, G+2n+8, 0, G+1) →* (0, G+n+4, 0, n+5, G+n+3, G+1)
  have phase3 : ⟨(0 : ℕ), 1, G + n + 3, G + 2 * n + 8, 0, G + 1⟩ [fm]⊢*
      ⟨0, G + n + 4, 0, n + 5, G + n + 3, G + 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show G + 2 * n + 8 = (n + 5) + (G + n + 3) from by ring]
    have := r2r1_chain (G + n + 3) 0 (n + 5) 0 (G + 1)
    rw [show 0 + (G + n + 3) + 1 = G + n + 4 from by ring,
        show 0 + (G + n + 3) = G + n + 3 from by ring] at this
    exact this
  -- Phase 4: Drain
  -- (0, G+n+4, 0, n+5, G+n+3, G+1) →* (0, 0, 0, 2G+3n+13, 2G+2n+7, 2G+n+5)
  have phase4 : ⟨(0 : ℕ), G + n + 4, 0, n + 5, G + n + 3, G + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * G + 3 * n + 13, 2 * G + 2 * n + 7, 2 * G + n + 5⟩ := by
    rw [show n + 5 = (n + 4) + 1 from by ring]
    apply stepStar_trans (drain (G + n + 4) 0 (n + 4) (G + n + 3) (G + 1))
    ring_nf; finish
  -- Compose
  exact stepStar_stepPlus_stepPlus phase1
    (step_stepStar_stepPlus phase2
      (stepStar_trans phase3 phase4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 8, 3, 2⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨G, n⟩ ↦ ⟨0, 0, 0, G + 2 * n + 8, G + n + 3, G + 2⟩) ⟨0, 0⟩
  intro ⟨G, n⟩
  refine ⟨⟨2 * G + n + 3, n + 1⟩, ?_⟩
  show ⟨0, 0, 0, G + 2 * n + 8, G + n + 3, G + 2⟩ [fm]⊢⁺
       ⟨0, 0, 0, (2 * G + n + 3) + 2 * (n + 1) + 8, (2 * G + n + 3) + (n + 1) + 3, (2 * G + n + 3) + 2⟩
  rw [show (2 * G + n + 3) + 2 * (n + 1) + 8 = 2 * G + 3 * n + 13 from by ring,
      show (2 * G + n + 3) + (n + 1) + 3 = 2 * G + 2 * n + 7 from by ring,
      show (2 * G + n + 3) + 2 = 2 * G + n + 5 from by ring]
  exact main_trans G n
