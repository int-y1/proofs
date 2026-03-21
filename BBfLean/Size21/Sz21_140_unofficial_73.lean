import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #73: [4/15, 33/14, 65/2, 7/11, 21/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_73

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- Phase 1: drain a into c,f
theorem phase1 : ∀ k, ∀ a c n f, ⟨a+k, 0, c, 0, n, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, n, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a c n f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 2: drain e into d
theorem phase2 : ∀ k, ∀ c d n f, ⟨0, 0, c, d, n+k, f⟩ [fm]⊢* ⟨0, 0, c, d+k, n, f⟩ := by
  intro k; induction' k with k ih <;> intro c d n f
  · exists 0
  rw [show n + (k + 1) = n + k + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 3: interleaved R2-R1 chain
theorem r2r1_chain : ∀ k, ∀ a c d e f, ⟨a+1, 0, c+k, d+k, e, f⟩ [fm]⊢* ⟨a+1+k, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih _ _ _ _ _)
  ring_nf; finish

-- Phase 3 tail
theorem phase3_tail : ⟨d+2, 0, 0, 1, d, f⟩ [fm]⊢⁺ ⟨d+2, 0, 0, 0, d+1, f+1⟩ := by
  step fm
  step fm
  step fm
  finish

-- Full Phase 3
theorem phase3 : ⟨0, 0, d+1, d, 0, f+1⟩ [fm]⊢⁺ ⟨d+2, 0, 0, 0, d+1, f+1⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, d + 1, d, 0, f + 1⟩ = some ⟨0, 1, d + 1, d + 1, 0, f⟩; simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨0, 0 + 1, (d + 1), d + 1, 0, f⟩ = some ⟨2, 0, d, d + 1, 0, f⟩; simp [fm]
  apply stepStar_trans
  · have h := @r2r1_chain d 1 0 1 0 f
    simp only [Nat.zero_add] at h
    rw [show 1 + d = d + 1 from by ring] at h
    exact h
  have h := @phase3_tail d f
  rw [show 2 + d = d + 2 from by ring]
  exact stepPlus_stepStar h

-- Main transition
theorem main_trans (_hT : T ≥ 1) :
    ⟨n+1, 0, 0, 0, n, T⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1, T+n+1⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, n, T+(n+1)⟩)
  · have h := @phase1 (n+1) 0 0 n T
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, n, 0, T+(n+1)⟩)
  · have h := @phase2 n (n+1) 0 0 (T+(n+1))
    simp only [Nat.zero_add] at h; exact h
  have hf : T + (n + 1) = (T + n) + 1 := by ring
  rw [hf]
  have h := @phase3 n (T + n)
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1, 1⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n T, q = ⟨n+1, 0, 0, 0, n, T⟩ ∧ T ≥ 1)
  · intro c ⟨n, T, hq, hT⟩
    subst hq
    exact ⟨⟨n+2, 0, 0, 0, n+1, T+n+1⟩, ⟨n+1, T+n+1, rfl, by omega⟩, main_trans hT⟩
  · exact ⟨1, 1, rfl, by omega⟩

end Sz21_140_unofficial_73
