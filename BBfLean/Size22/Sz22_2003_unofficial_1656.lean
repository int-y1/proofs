import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1656: [77/15, 338/3, 9/91, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 1 -1  0  0  0  2
 0  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1656

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+2⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k a c e fv, ⟨a, 0, c, 0, e + k, fv⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro a c e fv
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e fv)
    ring_nf; finish

theorem r2_chain : ∀ k a d e f, ⟨a, k, 0, d, e, f⟩ [fm]⊢* ⟨a + k, 0, 0, d, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) d e (f + 2))
    ring_nf; finish

theorem interleave : ∀ M, ∀ A B C D E F,
    2 * C + D = M → F ≥ C →
    ⟨A, B + 1, C, D, E, F⟩ [fm]⊢* ⟨A + B + 1 + C + 2 * D, 0, 0, 0, E + C, F + 2 * B + 2 + C + 3 * D⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E F hM hF
  rcases C with _ | C
  · rcases D with _ | D
    · simp
      have := r2_chain (B + 1) A 0 E F
      rw [show A + (B + 1) = A + B + 1 from by ring,
          show F + 2 * (B + 1) = F + 2 * B + 2 from by ring] at this
      exact this
    · show ⟨A, B + 1, 0, D + 1, E, F⟩ [fm]⊢*
        ⟨A + B + 1 + 0 + 2 * (D + 1), 0, 0, 0, E + 0, F + 2 * B + 2 + 0 + 3 * (D + 1)⟩
      have phase1 := r2_chain (B + 1) A (D + 1) E F
      rw [show A + (B + 1) = A + B + 1 from by ring,
          show F + 2 * (B + 1) = F + 2 * B + 2 from by ring] at phase1
      apply stepStar_trans phase1
      rw [show D + 1 = D + 1 from rfl, show F + 2 * B + 2 = (F + 2 * B + 1) + 1 from by ring]
      step fm
      have h := ih (2 * 0 + D) (by omega) (A + B + 1) 1 0 D E (F + 2 * B + 1) (by ring) (by omega)
      rw [show A + B + 1 + 1 + 1 + 0 + 2 * D = A + B + 1 + 0 + 2 * (D + 1) from by ring,
          show E + 0 = E + 0 from rfl,
          show F + 2 * B + 1 + 2 * 1 + 2 + 0 + 3 * D = F + 2 * B + 2 + 0 + 3 * (D + 1) from by ring] at h
      exact h
  · rcases B with _ | B
    · -- C>=1, B=0: R1 then R3 then IH
      -- We know F >= C+1, so write F = G + C + 1 for some G
      obtain ⟨G, hG⟩ : ∃ G, F = G + C + 1 := ⟨F - C - 1, by omega⟩
      subst hG
      show ⟨A, 0 + 1, C + 1, D, E, G + C + 1⟩ [fm]⊢*
        ⟨A + 0 + 1 + (C + 1) + 2 * D, 0, 0, 0, E + (C + 1), G + C + 1 + 2 * 0 + 2 + (C + 1) + 3 * D⟩
      rw [show C + 1 = C + 1 from rfl]
      step fm
      rw [show D + 1 = D + 1 from rfl, show G + C + 1 = (G + C) + 1 from by ring]
      step fm
      have h := ih (2 * C + D) (by omega) A 1 C D (E + 1) (G + C) (by ring) (by omega)
      rw [show A + 1 + 1 + C + 2 * D = A + 0 + 1 + (C + 1) + 2 * D from by ring,
          show E + 1 + C = E + (C + 1) from by ring,
          show G + C + 2 * 1 + 2 + C + 3 * D = G + C + 1 + 2 * 0 + 2 + (C + 1) + 3 * D from by ring] at h
      exact h
    · -- C>=1, B>=1: R1 then IH
      have hMlt : 2 * C + (D + 1) < M := by omega
      show ⟨A, B + 1 + 1, C + 1, D, E, F⟩ [fm]⊢*
        ⟨A + (B + 1) + 1 + (C + 1) + 2 * D, 0, 0, 0, E + (C + 1), F + 2 * (B + 1) + 2 + (C + 1) + 3 * D⟩
      rw [show B + 1 + 1 = (B + 1) + 1 from by ring, show C + 1 = C + 1 from rfl]
      step fm
      have hFge : F ≥ C := by omega
      have h := ih (2 * C + (D + 1)) hMlt A B C (D + 1) (E + 1) F rfl hFge
      rw [show A + B + 1 + C + 2 * (D + 1) = A + (B + 1) + 1 + (C + 1) + 2 * D from by ring,
          show E + 1 + C = E + (C + 1) from by ring,
          show F + 2 * B + 2 + C + 3 * (D + 1) = F + 2 * (B + 1) + 2 + (C + 1) + 3 * D from by ring] at h
      exact h

theorem main_trans (a e g : ℕ) :
    ⟨a + 1, 0, 0, 0, e + 1, g + e + 1⟩ [fm]⊢⁺ ⟨a + e + 2, 0, 0, 0, e + 2, g + 2 * e + 4⟩ := by
  have phase1 : ⟨a + 1, 0, 0, 0, e + 1, g + e + 1⟩ [fm]⊢* ⟨a + 1, 0, e + 1, 0, 0, g + e + 1⟩ := by
    have := r4_chain (e + 1) (a + 1) 0 0 (g + e + 1); simp at this; exact this
  have phase2 : ⟨a + 1, 0, e + 1, 0, 0, g + e + 1⟩ [fm]⊢⁺ ⟨a, 1, e + 1, 0, 1, g + e + 1⟩ := by
    rw [show e + 1 = 0 + (e + 1) from by ring]; step fm; finish
  have phase3 : ⟨a, 1, e + 1, 0, 1, g + e + 1⟩ [fm]⊢*
      ⟨a + e + 2, 0, 0, 0, e + 2, g + 2 * e + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    have h := interleave (2 * (e + 1) + 0) a 0 (e + 1) 0 1 (g + e + 1) (by ring) (by omega)
    rw [show a + 0 + 1 + (e + 1) + 2 * 0 = a + e + 2 from by ring,
        show 1 + (e + 1) = e + 2 from by ring,
        show g + e + 1 + 2 * 0 + 2 + (e + 1) + 3 * 0 = g + 2 * e + 4 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus phase1 (stepPlus_stepStar_stepPlus phase2 phase3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 5⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, 0, 0, 0, p.2.1 + 1, p.2.2 + p.2.1 + 1⟩) ⟨1, 1, 3⟩
  intro ⟨a, e, g⟩
  refine ⟨⟨a + e + 1, e + 1, g + e + 2⟩, ?_⟩
  show ⟨a + 1, 0, 0, 0, e + 1, g + e + 1⟩ [fm]⊢⁺
    ⟨a + e + 1 + 1, 0, 0, 0, e + 1 + 1, g + e + 2 + (e + 1) + 1⟩
  rw [show a + e + 1 + 1 = a + e + 2 from by ring,
      show e + 1 + 1 = e + 2 from by ring,
      show g + e + 2 + (e + 1) + 1 = g + 2 * e + 4 from by ring]
  exact main_trans a e g
