import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1752: [9/10, 196/33, 121/2, 5/7, 3/11]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0  2 -1
-1  0  0  0  2
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1752

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a d (e + 2)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

theorem r5_r2 : ⟨0, 0, d, 0, e + 2⟩ [fm]⊢⁺ ⟨2, 0, d, 2, e⟩ := by
  step fm; step fm; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = c + 2 + 2 * k from by ring,
        show e + (k + 1) = e + 1 + k from by ring]
    apply stepStar_trans (ih b (c + 2) d (e + 1))
    step fm; step fm; step fm; ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b d, ⟨a, b + k, 0, d, k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 2) b (d + 2)); ring_nf; finish

theorem r3r2r2_one : ∀ a b d, ⟨a + 1, b + 2, 0, d, 0⟩ [fm]⊢* ⟨a + 4, b, 0, d + 4, 0⟩ := by
  intro a b d; step fm
  rw [show b + 2 = (b + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a b d,
    ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 4 * k, b, 0, d + 4 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    apply stepStar_trans (r3r2r2_one (a + k) (b + 2 * k) d)
    rw [show a + k + 4 = (a + 4) + k from by ring]
    apply stepStar_trans (ih (a + 4) b (d + 4)); ring_nf; finish

theorem main_trans (hF : F ≤ M + 1) :
    ⟨M + 2 + F, 0, 0, 2 * (M + 1), 0⟩ [fm]⊢⁺ ⟨5 * M + F + 7, 0, 0, 8 * M + 10, 0⟩ := by
  -- Phase 1: R3 x (M+2+F)
  apply stepStar_stepPlus_stepPlus
  · rw [show M + 2 + F = 0 + (M + 2 + F) from by ring]
    exact r3_chain (M + 2 + F) 0 (2 * (M + 1)) 0
  -- (0, 0, 0, 2M+2, 2M+2F+4)
  -- Phase 2: R4 x (2M+2)
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (M + 2 + F) = 2 * M + 2 * F + 4 from by ring,
        show 2 * (M + 1) = 0 + (2 * M + 2) from by ring]
    exact r4_chain (2 * M + 2) 0 0 (2 * M + 2 * F + 4)
  -- (0, 0, 2M+2, 0, 2M+2F+4)
  -- Phase 3: R5+R2
  apply stepPlus_stepStar_stepPlus
  · rw [show 0 + (2 * M + 2) = 2 * M + 2 from by ring,
        show 2 * M + 2 * F + 4 = (2 * M + 2 * F + 2) + 2 from by ring]
    exact r5_r2
  -- (2, 0, 2M+2, 2, 2M+2F+2)
  -- Phase 4: R1R1R2 x (M+1)
  apply stepStar_trans
  · rw [show 2 * M + 2 = 0 + 2 * (M + 1) from by ring,
        show 2 * M + 2 * F + 2 = (M + 2 * F + 1) + (M + 1) from by ring]
    exact r1r1r2_chain (M + 1) 0 0 2 (M + 2 * F + 1)
  -- (2, 3M+3, 0, 2M+4, M+2F+1)
  -- Phase 5: R2 drain x (M+2F+1)
  apply stepStar_trans
  · rw [show 0 + 3 * (M + 1) = 2 * (M + 1 - F) + (M + 2 * F + 1) from by omega,
        show 2 + 2 * (M + 1) = 2 * M + 4 from by ring]
    exact r2_drain (M + 2 * F + 1) 2 (2 * (M + 1 - F)) (2 * M + 4)
  -- (2M+4F+4, 2*(M+1-F), 0, 4M+4F+6, 0)
  -- Phase 6: R3R2R2 x (M+1-F)
  rw [show 2 + 2 * (M + 2 * F + 1) = (M + 5 * F + 3) + (M + 1 - F) from by omega,
      show 2 * (M + 1 - F) = 0 + 2 * (M + 1 - F) from by ring,
      show 2 * M + 4 + 2 * (M + 2 * F + 1) = 4 * M + 4 * F + 6 from by ring]
  apply stepStar_trans (r3r2r2_chain (M + 1 - F) (M + 5 * F + 3) 0 (4 * M + 4 * F + 6))
  have h1 : M + 5 * F + 3 + 4 * (M + 1 - F) = 5 * M + F + 7 := by omega
  have h2 : 4 * M + 4 * F + 6 + 4 * (M + 1 - F) = 8 * M + 10 := by omega
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ F M, q = ⟨M + 2 + F, 0, 0, 2 * (M + 1), 0⟩ ∧ F ≤ M + 1)
  · intro c ⟨F, M, hq, hF⟩; subst hq
    exact ⟨⟨5 * M + F + 7, 0, 0, 8 * M + 10, 0⟩,
      ⟨M + F + 1, 4 * M + 4, by ring_nf, by omega⟩, main_trans hF⟩
  · exact ⟨0, 0, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1752
