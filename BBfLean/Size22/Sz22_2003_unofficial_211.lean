import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #211: [1/6, 44/35, 55/2, 3/5, 98/33]

Vector representation:
```
-1 -1  0  0  0
 2  0 -1 -1  1
-1  0  1  0  1
 0  1 -1  0  0
 1 -1  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_211

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- Phase 1: Interleaved R2+R3 converting c=1,d>0 into a accumulation
-- (a, 0, 1, k+1, e) →* (a+k+2, 0, 0, 0, e+2k+1)
theorem convert_cd : ∀ k, ∀ a e, ⟨a, 0, 1, k + 1, e⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- Phase 2: Drain a into c (with b=0, d=0)
-- (a, 0, c, 0, e) →* (0, 0, c+a, 0, e+a)
theorem drain_a : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- Phase 3: Drain c into b (with a=0, d=0)
-- (0, b, c, 0, e) →* (0, b+c, 0, 0, e)
theorem drain_c_to_b : ∀ k, ∀ b e, ⟨0, b, k, 0, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- Phase 4: R5+R1 pairs converting b,e into d
-- (0, 2*k+1, 0, d, e+k) →* (0, 1, 0, d+2*k, e)
theorem convert_be : ∀ k, ∀ d e, ⟨0, 2 * k + 1, 0, d, e + k⟩ [fm]⊢* ⟨0, 1, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

-- Main transition: (0, 0, 1, 2*(n+1), e) →⁺ (0, 0, 1, 2*(n+2), e + 5*(n+1))
theorem main_trans : ∀ n e,
    ⟨0, 0, 1, 2 * (n + 1), e⟩ [fm]⊢⁺ ⟨0, 0, 1, 2 * (n + 2), e + 5 * (n + 1)⟩ := by
  intro n e
  -- Phase 1: convert_cd with k = 2n+1
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2 * n + 3, 0, 0, 0, e + 2 * (2 * n + 1) + 1⟩)
  · have h := convert_cd (2 * n + 1) 0 e
    rw [show 0 + (2 * n + 1) + 2 = 2 * n + 3 from by ring] at h
    exact h
  -- Phase 2: drain_a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * n + 3, 0, e + 2 * (2 * n + 1) + 1 + (2 * n + 3)⟩)
  · have h := drain_a (2 * n + 3) 0 (e + 2 * (2 * n + 1) + 1)
    rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring] at h
    exact h
  -- Phase 3: drain_c_to_b
  apply stepStar_stepPlus_stepPlus
    (c₂ := ⟨0, 2 * n + 3, 0, 0, e + 2 * (2 * n + 1) + 1 + (2 * n + 3)⟩)
  · have h := drain_c_to_b (2 * n + 3) 0 (e + 2 * (2 * n + 1) + 1 + (2 * n + 3))
    rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring] at h
    exact h
  -- Phase 4: convert_be with k = n+1
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 2 * (n + 1), e + 5 * (n + 1)⟩)
  · have h := convert_be (n + 1) 0 (e + 5 * (n + 1))
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring,
        show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring,
        show e + 5 * (n + 1) + (n + 1) = e + 2 * (2 * n + 1) + 1 + (2 * n + 3) from by ring] at h
    exact h
  -- Phase 5: R5 + R3
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring,
      show e + 5 * (n + 1) = (e + 5 * n + 4) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0 + 1, 0, (2 * n + 1) + 1, (e + 5 * n + 4) + 1⟩ =
         some ⟨0 + 1, 0, 0, (2 * n + 1) + 1 + 2, e + 5 * n + 4⟩
    simp [fm]
  rw [show (2 * n + 1) + 1 + 2 = 2 * (n + 2) from by ring,
      show (0 : ℕ) + 1 = 1 from by ring]
  step fm
  rw [show e + 5 * n + 4 + 1 = e + 5 * (n + 1) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 2, 1⟩) (by unfold c₀; execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 1, 2 * (n + 1), e⟩) ⟨0, 1⟩
  intro ⟨n, e⟩
  exact ⟨⟨n + 1, e + 5 * (n + 1)⟩, main_trans n e⟩

end Sz22_2003_unofficial_211
