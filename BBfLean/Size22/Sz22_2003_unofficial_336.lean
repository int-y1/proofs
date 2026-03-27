import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #336: [189/10, 121/2, 2/33, 5/7, 14/11]

Vector representation:
```
-1  3 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_336

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_loop : ∀ k c e, ⟨0, 0, c, k + 1, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; finish
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r1r3_loop : ∀ c b d e, ⟨1, b, c + 1, d, e + c⟩ [fm]⊢* ⟨0, b + 2 * c + 3, 0, d + c + 1, e⟩ := by
  intro c; induction' c with c ih <;> intro b d e
  · step fm; ring_nf; finish
  · rw [show e + (c + 1) = (e + c) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2) (d + 1) e)
    ring_nf; finish

theorem drain_loop : ∀ k d e, ⟨0, k + 1, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + k + 2⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; finish
  · step fm; step fm
    rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

theorem main_trans (n r : ℕ) :
    ⟨0, 0, 0, n + 1, n + r + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, 2 * n + r + 4⟩ := by
  -- Phase 1: R4 loop
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n + 1, 0, n + r + 2⟩)
  · have h := r4_loop n 0 (n + r + 2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, n + 1, 0, n + r + 2⟩ = some ⟨1, 0, n + 1, 1, n + r + 1⟩
    rw [show n + r + 2 = (n + r + 1) + 1 from by ring]; simp [fm]
  -- Phase 3: R1/R3 loop
  rw [show n + r + 1 = (r + 1) + n from by ring]
  apply stepStar_trans (r1r3_loop n 0 1 (r + 1))
  rw [show 0 + 2 * n + 3 = 2 * n + 3 from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  -- Phase 4: drain
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  apply stepStar_trans (drain_loop (2 * n + 2) (n + 2) r)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    obtain ⟨r, hr⟩ : ∃ r, e = d + r + 2 := ⟨e - d - 2, by omega⟩
    subst hr
    exact ⟨⟨0, 0, 0, d + 2, 2 * d + r + 4⟩,
           ⟨d + 1, 2 * d + r + 4, rfl, by omega⟩,
           main_trans d r⟩
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_336
