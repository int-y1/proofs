import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1590: [72/35, 5/22, 21/2, 11/3, 5/11]

Vector representation:
```
 3  2 -1 -1  0
-1  0  1  0 -1
-1  1  0  1  0
 0 -1  0  0  1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1590

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4: transfer b to e (with a=0, c=0).
theorem b_to_e : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- R3: drain a to b and d (with c=0, e=0).
theorem a_to_bd : ∀ k, ∀ b d, ⟨k, b, 0, d, 0⟩ [fm]⊢* ⟨0, b + k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1))
    ring_nf; finish

-- R1-R2 chain: d rounds draining d and e, increasing a and b by 2 each.
theorem r1r2_chain : ∀ k, ∀ a b d e, ⟨a, b, 1, d + k, e + k⟩ [fm]⊢* ⟨a + 2 * k, b + 2 * k, 1, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (b + 2) d e)
    ring_nf; finish

-- R2 drain: a and e decrease, c increases (with d=0).
theorem r2_drain : ∀ k, ∀ a b c, ⟨a + k, b, c, 0, k⟩ [fm]⊢* ⟨a, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a b (c + 1))
    ring_nf; finish

-- R3-R1 chain: each round R3 then R1 when c >= 1, d = 0, e = 0.
theorem r3r1_chain : ∀ k, ∀ a b, ⟨a + 1, b, k, 0, 0⟩ [fm]⊢* ⟨a + 2 * k + 1, b + 3 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (b + 3))
    ring_nf; finish

-- Full transition: (0, 0, 0, d+1, e+d+1) ⊢⁺ (0, 0, 0, 2d+e+3, 4d+4e+5)
theorem full_transition (d e : ℕ) (he : e ≤ 2 * d + 2) :
    (⟨0, 0, 0, d + 1, e + d + 1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 2 * d + e + 3, 4 * d + 4 * e + 5⟩ := by
  -- Phase 1: R5 (establishes ⊢⁺)
  rw [show e + d + 1 = (e + d) + 1 from by ring]
  step fm
  -- State: (0, 0, 1, d+1, e+d)
  -- Phase 2: R1-R2 chain (d rounds)
  rw [show d + 1 = 1 + d from by ring,
      show e + d = e + d from rfl]
  apply stepStar_trans (r1r2_chain d 0 0 1 e)
  -- State: (0+2d, 0+2d, 1, 1, e) = (2d, 2d, 1, 1, e)
  -- Phase 3: Last R1 step
  rw [show 0 + 2 * d = 2 * d from by ring]
  step fm
  -- State: (2d+3, 2d+2, 0, 0, e)
  -- Phase 4: R2 drain (e rounds)
  rw [show 2 * d + 3 = (2 * d + 3 - e) + e from by omega]
  apply stepStar_trans (r2_drain e (2 * d + 3 - e) (2 * d + 2) 0)
  rw [show 0 + e = e from by ring]
  -- State: (2d+3-e, 2d+2, e, 0, 0)
  -- Phase 5: R3-R1 chain (e rounds)
  rw [show 2 * d + 3 - e = (2 * d + 3 - e - 1) + 1 from by omega]
  apply stepStar_trans (r3r1_chain e (2 * d + 3 - e - 1) (2 * d + 2))
  rw [show (2 * d + 3 - e - 1) + 2 * e + 1 = 2 * d + e + 3 from by omega,
      show (2 * d + 2) + 3 * e = 2 * d + 3 * e + 2 from by ring]
  -- State: (2d+e+3, 2d+3e+2, 0, 0, 0)
  -- Phase 6: R3 drain a to b and d
  apply stepStar_trans (a_to_bd (2 * d + e + 3) (2 * d + 3 * e + 2) 0)
  rw [show (2 * d + 3 * e + 2) + (2 * d + e + 3) = 4 * d + 4 * e + 5 from by ring,
      show 0 + (2 * d + e + 3) = 2 * d + e + 3 from by ring]
  -- State: (0, 4d+4e+5, 0, 2d+e+3, 0)
  -- Phase 7: R4 drain b to e
  rw [show (4 * d + 4 * e + 5 : ℕ) = 0 + (4 * d + 4 * e + 5) from by ring]
  apply stepStar_trans (b_to_e (4 * d + 4 * e + 5) 0 (2 * d + e + 3) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + d + 1⟩ ∧ e ≤ 2 * d + 2)
  · intro c ⟨d, e, hq, he⟩
    exact ⟨⟨0, 0, 0, 2 * d + e + 3, 4 * d + 4 * e + 5⟩,
      ⟨2 * d + e + 2, 2 * d + 3 * e + 2, by ring_nf, by omega⟩,
      hq ▸ full_transition d e he⟩
  · exact ⟨0, 0, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1590
