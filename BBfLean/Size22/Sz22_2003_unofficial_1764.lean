import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1764: [9/10, 22/21, 343/2, 5/11, 9/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 0  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1764

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

theorem r2r1_chain : ∀ k b c d e, ⟨0, b + 1, c + k, d + k, e⟩ [fm]⊢* ⟨0, b + k + 1, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) c d (e + 1))
    ring_nf; finish

theorem spiral : ∀ C D, ⟨0, 0, C, D + C + 1, 0⟩ [fm]⊢* ⟨0, C + 2, 0, D, C⟩ := by
  intro C D
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (C : ℕ) = 0 + C from by omega,
      show D + (0 + C) = D + C from by omega]
  apply stepStar_trans (r2r1_chain C 1 0 D 0)
  ring_nf; finish

theorem r2_drain : ∀ k a b d e, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih a (b + 1) (d + 1) e)
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨a + k, b + 1, 0, d + 1, e + k⟩ [fm]⊢ ⟨a + k + 1, b, 0, d, e + k + 1⟩))
    ring_nf; finish

theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨(a + k) + 1, 0, 0, d, e⟩ [fm]⊢ ⟨a + k, 0, 0, d + 3, e⟩))
    apply stepStar_trans (ih a (d + 3) e)
    ring_nf; finish

theorem full_drain : ∀ B A F, ⟨A + 1, B, 0, 0, F⟩ [fm]⊢* ⟨0, 0, 0, 3 * A + 2 * B + 3, F + B⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro A F
  rcases B with _ | _ | _ | B
  · rw [show (A + 1 : ℕ) = 0 + (A + 1) from by omega]
    apply stepStar_trans (r3_drain (A + 1) 0 0 F)
    ring_nf; finish
  · apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 1, 1, 0, 0, F⟩ [fm]⊢ ⟨A, 1, 0, 3, F⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A, 1, 0, 3, F⟩ [fm]⊢ ⟨A + 1, 0, 0, 2, F + 1⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 1, 0, 0, 2, F + 1⟩ [fm]⊢ ⟨A, 0, 0, 5, F + 1⟩))
    rw [show (A : ℕ) = 0 + A from by omega]
    apply stepStar_trans (r3_drain A 0 5 (F + 1))
    ring_nf; finish
  · apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 1, 2, 0, 0, F⟩ [fm]⊢ ⟨A, 2, 0, 3, F⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A, 2, 0, 3, F⟩ [fm]⊢ ⟨A + 1, 1, 0, 2, F + 1⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 1, 1, 0, 2, F + 1⟩ [fm]⊢ ⟨A + 2, 0, 0, 1, F + 2⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 2, 0, 0, 1, F + 2⟩ [fm]⊢ ⟨A + 1, 0, 0, 4, F + 2⟩))
    rw [show (A + 1 : ℕ) = 0 + (A + 1) from by omega]
    apply stepStar_trans (r3_drain (A + 1) 0 4 (F + 2))
    ring_nf; finish
  · apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 1, B + 3, 0, 0, F⟩ [fm]⊢ ⟨A, B + 3, 0, 3, F⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A, B + 3, 0, 3, F⟩ [fm]⊢ ⟨A + 1, B + 2, 0, 2, F + 1⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 1, B + 2, 0, 2, F + 1⟩ [fm]⊢ ⟨A + 2, B + 1, 0, 1, F + 2⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A + 2, B + 1, 0, 1, F + 2⟩ [fm]⊢ ⟨A + 3, B, 0, 0, F + 3⟩))
    rw [show (A + 3 : ℕ) = (A + 2) + 1 from by ring]
    apply stepStar_trans (ih B (by omega) (A + 2) (F + 3))
    ring_nf; finish

theorem phase12 : ∀ G H, ⟨0, 0, 0, 2 * G + H + 7, G + H + 2⟩ [fm]⊢*
    ⟨0, G + H + 4, 0, G + 4, G + H + 2⟩ := by
  intro G H
  rw [show (G + H + 2 : ℕ) = 0 + (G + H + 2) from by omega]
  apply stepStar_trans (e_to_c (G + H + 2) 0 (2 * G + H + 7) 0)
  rw [show 0 + (G + H + 2) = G + H + 2 from by omega,
      show (2 * G + H + 7 : ℕ) = (G + 4) + (G + H + 2) + 1 from by ring]
  apply stepStar_trans (spiral (G + H + 2) (G + 4))
  ring_nf; finish

theorem phase3 : ∀ G H, ⟨0, G + H + 4, 0, G + 4, G + H + 2⟩ [fm]⊢*
    ⟨G + 4, H, 0, 0, 2 * G + H + 6⟩ := by
  intro G H
  rw [show (G + H + 4 : ℕ) = H + (G + 4) from by ring]
  have h := r2_drain (G + 4) 0 H 0 (G + H + 2)
  simp at h
  apply stepStar_trans h
  ring_nf; finish

theorem phase4 : ∀ G H, ⟨G + 4, H, 0, 0, 2 * G + H + 6⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * G + 2 * H + 12, 2 * G + 2 * H + 6⟩ := by
  intro G H
  rw [show (G + 4 : ℕ) = (G + 3) + 1 from by ring]
  apply stepStar_trans (full_drain H (G + 3) (2 * G + H + 6))
  ring_nf; finish

theorem main_trans : ∀ G H, ⟨0, 0, 0, 2 * G + H + 7, G + H + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * G + 2 * H + 12, 2 * G + 2 * H + 6⟩ := by
  intro G H
  -- First R4 step gives ⊢⁺
  rw [show (G + H + 2 : ℕ) = (G + H + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show ⟨0, 0, 0, 2 * G + H + 7, (G + H + 1) + 1⟩ [fm]⊢ ⟨0, 0, 1, 2 * G + H + 7, G + H + 1⟩ from by simp [fm])
  -- Now at (0, 0, 1, 2G+H+7, G+H+1)
  rw [show (G + H + 1 : ℕ) = 0 + (G + H + 1) from by omega]
  apply stepStar_trans (e_to_c (G + H + 1) 1 (2 * G + H + 7) 0)
  -- Now at (0, 0, G+H+2, 2G+H+7, 0)
  rw [show 1 + (G + H + 1) = G + H + 2 from by omega,
      show (2 * G + H + 7 : ℕ) = (G + 4) + (G + H + 2) + 1 from by ring]
  apply stepStar_trans (spiral (G + H + 2) (G + 4))
  apply stepStar_trans (phase3 G H)
  exact phase4 G H

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 11, 6⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨G, H⟩ ↦ ⟨0, 0, 0, 2 * G + H + 7, G + H + 2⟩) ⟨0, 4⟩
  intro ⟨G, H⟩
  refine ⟨⟨G + 1, G + 2 * H + 3⟩, ?_⟩
  show ⟨0, 0, 0, 2 * G + H + 7, G + H + 2⟩ [fm]⊢⁺
       ⟨0, 0, 0, 2 * (G + 1) + (G + 2 * H + 3) + 7, (G + 1) + (G + 2 * H + 3) + 2⟩
  rw [show 2 * (G + 1) + (G + 2 * H + 3) + 7 = 3 * G + 2 * H + 12 from by ring,
      show (G + 1) + (G + 2 * H + 3) + 2 = 2 * G + 2 * H + 6 from by ring]
  exact main_trans G H
