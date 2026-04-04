import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1649: [77/15, 28/3, 9/154, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  1  0
-1  2  0 -1 -1
 0  0  1 -1  0
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1649

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm; apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem r3r2r2_tail : ∀ k, ∀ a d,
    ⟨a + 1, 0, 0, d + 1, k + 1⟩ [fm]⊢* ⟨a + 3 * k + 4, 0, 0, d + k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; step fm; finish
  · rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 1)); ring_nf; finish

theorem r1r1r3_loop : ∀ k, ∀ X C K,
    ⟨X + k + 1, 2, C + 2 * k, K, K⟩ [fm]⊢* ⟨X + 1, 2, C, K + k, K + k⟩ := by
  intro k; induction' k with k ih <;> intro X C K
  · exists 0
  · rw [show X + (k + 1) + 1 = (X + k + 1) + 1 from by omega,
        show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by omega]
    step fm
    rw [show C + 2 * k + 1 = (C + 2 * k) + 1 from by omega]
    step fm
    rw [show X + k + 1 = (X + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih X C (K + 1)); ring_nf; finish

theorem main_trans (A D : ℕ) :
    ⟨A + D + 2, 0, 0, D + 1, 0⟩ [fm]⊢⁺ ⟨A + 2 * D + 4, 0, 0, D + 2, 0⟩ := by
  have phase1 : ⟨A + D + 2, 0, 0, D + 1, 0⟩ [fm]⊢* ⟨A + D + 2, 0, D + 1, 0, 0⟩ := by
    have h := r4_chain (D + 1) (A + D + 2) 0; simp at h; exact h
  rcases D with _ | D
  · rw [show A + 2 * 0 + 4 = A + 4 from by omega,
        show (0 : ℕ) + 2 = 2 from by omega]
    apply stepStar_stepPlus_stepPlus phase1
    rw [show A + 0 + 2 = (A + 1) + 1 from by omega]
    step fm; step fm
    rcases A with _ | A
    · execute fm 3
    · step fm; step fm; step fm; finish
  · have phase2 : ⟨A + D + 3, 0, D + 2, 0, 0⟩ [fm]⊢⁺ ⟨A + D + 1, 2, D + 1, 0, 0⟩ := by
      rw [show A + D + 3 = (A + D + 2) + 1 from by omega,
          show D + 2 = (D + 1) + 1 from by omega]
      step fm
      rw [show D + 1 + 1 = (D + 1) + 1 from rfl]
      step fm
      rw [show A + D + 2 = (A + D + 1) + 1 from by omega]
      step fm; finish
    rcases Nat.even_or_odd (D + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk1 : k ≥ 1 := by omega
      have phase3 : ⟨A + D + 1, 2, D + 1, 0, 0⟩ [fm]⊢*
          ⟨A + 2 * (D + 1) + 4, 0, 0, (D + 1) + 2, 0⟩ := by
        have hAD : A + D + 1 = (A + k - 1) + k + 1 := by omega
        have hC : D + 1 = 0 + 2 * k := by omega
        rw [hAD, hC]
        apply stepStar_trans (r1r1r3_loop k (A + k - 1) 0 0)
        simp
        rw [show A + k - 1 + 1 = A + k from by omega]
        rcases k with _ | k'
        · omega
        · step fm; step fm
          rw [show A + (k' + 1) + 2 + 2 = A + k' + 5 from by omega,
              show k' + 1 + 1 + 1 = k' + 3 from by omega,
              show A + 2 * (2 * (k' + 1)) + 4 = A + 4 * k' + 8 from by ring,
              show 2 * (k' + 1) + 2 = 2 * k' + 4 from by ring]
          have h := r3r2r2_tail k' (A + k' + 4) (k' + 2)
          rw [show A + k' + 4 + 1 = A + k' + 5 from by omega,
              show k' + 2 + 1 = k' + 3 from by omega] at h
          apply stepStar_trans h
          ring_nf; finish
      rw [show A + (D + 1) + 2 = A + D + 3 from by omega]
      exact stepPlus_stepStar_stepPlus
        (stepStar_stepPlus_stepPlus phase1 phase2) phase3
    · have phase3 : ⟨A + D + 1, 2, D + 1, 0, 0⟩ [fm]⊢*
          ⟨A + 2 * (D + 1) + 4, 0, 0, (D + 1) + 2, 0⟩ := by
        have hAD : A + D + 1 = (A + k) + k + 1 := by omega
        have hC : D + 1 = 1 + 2 * k := by omega
        rw [hAD, hC]
        apply stepStar_trans (r1r1r3_loop k (A + k) 1 0)
        simp
        step fm; step fm
        rw [show A + k + 1 + 2 = A + k + 3 from by omega,
            show k + 1 + 1 = k + 2 from by omega,
            show A + 2 * (1 + 2 * k) + 4 = A + 4 * k + 6 from by ring,
            show 1 + 2 * k + 2 = 2 * k + 3 from by omega]
        have h := r3r2r2_tail k (A + k + 2) (k + 1)
        rw [show A + k + 2 + 1 = A + k + 3 from by omega,
            show k + 1 + 1 = k + 2 from by omega] at h
        apply stepStar_trans h
        ring_nf; finish
      rw [show A + (D + 1) + 2 = A + D + 3 from by omega]
      exact stepPlus_stepStar_stepPlus
        (stepStar_stepPlus_stepPlus phase1 phase2) phase3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 2, 0, 0, p.2 + 1, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  refine ⟨⟨a + d + 1, d + 1⟩, ?_⟩
  show ⟨a + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺
    ⟨a + d + 1 + (d + 1) + 2, 0, 0, (d + 1) + 1, 0⟩
  rw [show a + d + 1 + (d + 1) + 2 = a + 2 * d + 4 from by ring]
  exact main_trans a d
