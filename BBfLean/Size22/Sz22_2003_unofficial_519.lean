import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #519: [28/15, 3/22, 845/2, 11/7, 21/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  2
 0  0  0 -1  1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_519

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R3 chain: drain a into c and f (when b=0, e=0)
theorem a_to_cf (d : ℕ) : ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d, 0, f+2*k⟩ := by
  have many_step : ∀ k c f, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d, 0, f+2*k⟩ := by
    intro k; induction' k with k h <;> intro c f
    · exists 0
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c f

-- R4 chain: drain d into e (when a=0, b=0)
theorem d_to_e (c f : ℕ) : ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- R2 chain: drain e into b (when c=0)
theorem e_to_b (d f : ℕ) : ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- R1/R2 interleaved chain with final R1
theorem r1r2_chain : ⟨a, 1, k+1, d, k+1+m, f⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, m+1, f⟩ := by
  have many_step : ∀ k, ∀ a d m f, ⟨a, 1, k+1, d, k+1+m, f⟩ [fm]⊢*
      ⟨a+k+2, 0, 0, d+k+1, m+1, f⟩ := by
    intro k; induction' k with k h <;> intro a d m f
    · step fm; ring_nf; finish
    rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    rw [show (k + 1) + 1 + m = (k + 1) + (m + 1) from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  exact many_step k a d m f

-- (R3, R1) interleaved chain: drain b, grow a and d, grow f
theorem r3r1_chain : ⟨a+1, k, 0, d, 0, f⟩ [fm]⊢* ⟨a+1+k, 0, 0, d+k, 0, f+2*k⟩ := by
  have many_step : ∀ k, ∀ a d f, ⟨a+1, k, 0, d, 0, f⟩ [fm]⊢*
      ⟨a+1+k, 0, 0, d+k, 0, f+2*k⟩ := by
    intro k; induction' k with k h <;> intro a d f
    · exists 0
    step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a d f

-- Main transition: (n+2, 0, 0, 2n+2, 0, f) →⁺ (n+3, 0, 0, 2n+4, 0, f+4n+5)
theorem main_trans : ⟨n+2, 0, 0, 2*n+2, 0, f⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0, f+4*n+5⟩ := by
  -- Phase 1: R3 chain - drain a into c and f
  apply stepStar_stepPlus_stepPlus (a_to_cf (2*n+2) (k := n+2) (c := 0) (f := f))
  -- Now at (0, 0, n+2, 2n+2, 0, f+2n+4)
  simp only [Nat.zero_add]
  rw [show f + 2 * (n + 2) = f + 2 * n + 4 from by ring]
  -- Phase 2: R4 chain - drain d into e
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (n+2) (f+2*n+4) (k := 2*n+2) (d := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Now at (0, 0, n+2, 0, 2n+2, f+2n+4)
  -- Phase 3a: R5 step (gives ⊢⁺)
  rw [show f + 2 * n + 4 = (f + 2 * n + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now at (0, 1, n+2, 1, 2n+2, f+2n+3)
  -- Phase 3b: R1/R2 chain
  rw [show (0 : ℕ) + 1 = 1 from by ring]
  rw [show n + 1 + 1 = (n + 1) + 1 from by ring]
  rw [show (2 * n + 1).succ = (n + 1) + 1 + n from by omega]
  apply stepStar_trans (r1r2_chain (k := n+1) (a := 0) (d := 1) (m := n) (f := f+2*n+3))
  -- Now at (n+3, 0, 0, n+3, n+1, f+2n+3)
  rw [show 0 + (n + 1) + 2 = 2 + (n + 1) from by ring]
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring]
  -- Phase 3c: R2 chain - drain e into b
  apply stepStar_trans (e_to_b (n+3) (f+2*n+3) (k := n+1) (a := 2) (b := 0))
  -- Now at (2, n+1, 0, n+3, 0, f+2n+3)
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring]
  -- Phase 4: (R3, R1) chain
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1_chain (k := n+1) (a := 1) (d := n+3) (f := f+2*n+3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨n+2, 0, 0, 2*n+2, 0, f⟩)
  · intro c ⟨n, f, hq⟩; subst hq
    exact ⟨⟨n+3, 0, 0, 2*n+4, 0, f+4*n+5⟩,
      ⟨n+1, f+4*n+5, by ring_nf⟩, main_trans⟩
  · exact ⟨0, 1, by ring_nf⟩

end Sz22_2003_unofficial_519
