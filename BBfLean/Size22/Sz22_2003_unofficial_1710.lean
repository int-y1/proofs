import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1710: [77/15, 9/91, 3718/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  2  0 -1  0 -1
 1 -1  0  0  1  2
 0  0  1  0 -1  0
-1  1  0  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1710

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e+1, f+2⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k a c e fv, ⟨a, 0, c, 0, e + k, fv⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro a c e fv
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e fv)
    ring_nf; finish

theorem r3_chain : ∀ k a e fv, ⟨a, k, 0, 0, e, fv⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k, fv + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e fv
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1) (fv + 2))
    ring_nf; finish

theorem r2_chain : ∀ k a b e fv, ⟨a, b, 0, k, e, fv + k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro a b e fv
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl, show fv + (k + 1) = (fv + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) e fv)
    ring_nf; finish

theorem interleave : ∀ M, ∀ A B C D E F,
    2 * C + D = M → F ≥ C →
    ⟨A, B + 1, C, D, E, F⟩ [fm]⊢*
    ⟨A + B + 1 + C + 2 * D, 0, 0, 0, E + B + 1 + 2 * C + 2 * D, F + 2 * B + 2 + C + 3 * D⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E F hM hF
  rcases C with _ | C
  · rcases D with _ | D
    · simp
      exact r3_chain (B + 1) A E F |>.imp fun n h => by
        rw [show A + (B + 1) = A + B + 1 from by ring,
            show E + (B + 1) = E + B + 1 from by ring,
            show F + 2 * (B + 1) = F + 2 * B + 2 from by ring] at h; exact h
    · show ⟨A, B + 1, 0, D + 1, E, F⟩ [fm]⊢*
        ⟨A + B + 1 + 0 + 2 * (D + 1), 0, 0, 0, E + B + 1 + 0 + 2 * (D + 1),
         F + 2 * B + 2 + 0 + 3 * (D + 1)⟩
      rcases F with _ | F'
      · step fm
        rw [show (2 : ℕ) = 1 + 1 from rfl]
        step fm
        have h := ih D (by omega) (A + 1) (B + 1) 0 D (E + 1) 1 (by ring) (by omega)
        rw [show A + 1 + (B + 1) + 1 + 0 + 2 * D = A + B + 1 + 0 + 2 * (D + 1) from by ring,
            show E + 1 + (B + 1) + 1 + 0 + 2 * D = E + B + 1 + 0 + 2 * (D + 1) from by ring,
            show 1 + 2 * (B + 1) + 2 + 0 + 3 * D = 0 + 2 * B + 2 + 0 + 3 * (D + 1) from by ring] at h
        exact h
      · rw [show F' + 1 = F' + 1 from rfl]
        step fm
        have h := ih D (by omega) A (B + 2) 0 D E F' (by ring) (by omega)
        rw [show A + (B + 2) + 1 + 0 + 2 * D = A + B + 1 + 0 + 2 * (D + 1) from by ring,
            show E + (B + 2) + 1 + 0 + 2 * D = E + B + 1 + 0 + 2 * (D + 1) from by ring,
            show F' + 2 * (B + 2) + 2 + 0 + 3 * D = F' + 1 + 2 * B + 2 + 0 + 3 * (D + 1) from by ring] at h
        exact h
  · rcases B with _ | B
    · obtain ⟨G, hG⟩ : ∃ G, F = G + C + 1 := ⟨F - C - 1, by omega⟩
      subst hG
      show ⟨A, 0 + 1, C + 1, D, E, G + C + 1⟩ [fm]⊢*
        ⟨A + 0 + 1 + (C + 1) + 2 * D, 0, 0, 0, E + 0 + 1 + 2 * (C + 1) + 2 * D,
         G + C + 1 + 2 * 0 + 2 + (C + 1) + 3 * D⟩
      step fm
      rw [show G + C + 1 = (G + C) + 1 from by ring]
      step fm
      have h := ih (2 * C + D) (by omega) A 1 C D (E + 1) (G + C) (by ring) (by omega)
      rw [show A + 1 + 1 + C + 2 * D = A + 0 + 1 + (C + 1) + 2 * D from by ring,
          show E + 1 + 1 + 1 + 2 * C + 2 * D = E + 0 + 1 + 2 * (C + 1) + 2 * D from by ring,
          show G + C + 2 * 1 + 2 + C + 3 * D = G + C + 1 + 2 * 0 + 2 + (C + 1) + 3 * D from by ring] at h
      exact h
    · show ⟨A, B + 1 + 1, C + 1, D, E, F⟩ [fm]⊢*
        ⟨A + (B + 1) + 1 + (C + 1) + 2 * D, 0, 0, 0, E + (B + 1) + 1 + 2 * (C + 1) + 2 * D,
         F + 2 * (B + 1) + 2 + (C + 1) + 3 * D⟩
      rw [show B + 1 + 1 = (B + 1) + 1 from by ring]
      step fm
      have h := ih (2 * C + (D + 1)) (by omega) A B C (D + 1) (E + 1) F rfl (by omega)
      rw [show A + B + 1 + C + 2 * (D + 1) = A + (B + 1) + 1 + (C + 1) + 2 * D from by ring,
          show E + 1 + B + 1 + 2 * C + 2 * (D + 1) = E + (B + 1) + 1 + 2 * (C + 1) + 2 * D from by ring,
          show F + 2 * B + 2 + C + 3 * (D + 1) = F + 2 * (B + 1) + 2 + (C + 1) + 3 * D from by ring] at h
      exact h

theorem main_trans (a c g : ℕ) :
    ⟨a + 1, 0, c + 1, 0, 0, g + c + 1⟩ [fm]⊢⁺ ⟨a + c + 2, 0, 2 * c + 3, 0, 0, g + 2 * c + 4⟩ := by
  have phase1 : ⟨a + 1, 0, c + 1, 0, 0, g + c + 1⟩ [fm]⊢⁺ ⟨a, 1, c + 1, 0, 0, g + c + 1⟩ := by
    rw [show c + 1 = 0 + (c + 1) from by ring]
    step fm; finish
  have phase2 : ⟨a, 1, c + 1, 0, 0, g + c + 1⟩ [fm]⊢*
      ⟨a + c + 2, 0, 0, 0, 2 * c + 3, g + 2 * c + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    have h := interleave (2 * (c + 1) + 0) a 0 (c + 1) 0 0 (g + c + 1) (by ring) (by omega)
    rw [show a + 0 + 1 + (c + 1) + 2 * 0 = a + c + 2 from by ring,
        show 0 + 0 + 1 + 2 * (c + 1) + 2 * 0 = 2 * c + 3 from by ring,
        show g + c + 1 + 2 * 0 + 2 + (c + 1) + 3 * 0 = g + 2 * c + 4 from by ring] at h
    exact h
  have phase3 : ⟨a + c + 2, 0, 0, 0, 2 * c + 3, g + 2 * c + 4⟩ [fm]⊢*
      ⟨a + c + 2, 0, 2 * c + 3, 0, 0, g + 2 * c + 4⟩ := by
    have h := r4_chain (2 * c + 3) (a + c + 2) 0 0 (g + 2 * c + 4)
    simp at h; exact h
  exact stepPlus_stepStar_stepPlus (stepPlus_stepStar_stepPlus phase1 phase2) phase3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 0, 0, 2⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, 0, p.2.1 + 1, 0, 0, p.2.2 + p.2.1 + 1⟩) ⟨0, 0, 1⟩
  intro ⟨a, c, g⟩
  refine ⟨⟨a + c + 1, 2 * c + 2, g + 1⟩, ?_⟩
  show ⟨a + 1, 0, c + 1, 0, 0, g + c + 1⟩ [fm]⊢⁺
    ⟨a + c + 1 + 1, 0, 2 * c + 2 + 1, 0, 0, g + 1 + (2 * c + 2) + 1⟩
  rw [show a + c + 1 + 1 = a + c + 2 from by ring,
      show 2 * c + 2 + 1 = 2 * c + 3 from by ring,
      show g + 1 + (2 * c + 2) + 1 = g + 2 * c + 4 from by ring]
  exact main_trans a c g
