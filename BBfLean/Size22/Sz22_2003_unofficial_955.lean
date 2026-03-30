import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #955: [4/15, 33/14, 3025/2, 7/11, 2/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  2
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_955

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b e, ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 2) (e + 2))
    ring_nf; finish

theorem phase6 : ∀ B, ∀ a c E, c ≥ 1 → ⟨a, B, c, 0, E⟩ [fm]⊢* ⟨0, 0, c + 2 * a + 3 * B, 0, E + 2 * a + 4 * B⟩ := by
  intro B; induction' B with B ih <;> intro a c E hc
  · exact r3_drain a c E
  · rcases c with _ | _ | c
    · omega
    · rw [show (1 : ℕ) = 0 + 1 from by ring]
      step fm
      rw [show a + 2 = (a + 1) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a + 1) 2 (E + 2) (by omega))
      ring_nf; finish
    · rw [show c + 2 = (c + 1) + 1 from by ring,
          show (B + 1 : ℕ) = B + 1 from rfl]
      step fm
      apply stepStar_trans (ih (a + 2) (c + 1) E (by omega))
      ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 3 * n + 5, 0, 6 * n + 8⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * n + 2) (n + 2) 0)
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  step fm
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show 2 * n + 1 + 1 = (n + 1) + (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) 0 0 (n + 1) 0)
  rw [show 0 + (n + 1) + 1 = 1 + (n + 1) from by ring,
      show (0 : ℕ) + (n + 1) = n + 1 from by ring]
  apply stepStar_trans (r2_drain (n + 1) 1 0 (n + 1))
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring]
  step fm
  rw [show n + 1 + (n + 1) + 2 = 2 * n + 4 from by ring]
  apply stepStar_trans (phase6 (n + 1) 0 2 (2 * n + 4) (by omega))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0 + 2, 0, 2 * 0 + 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨3 * n + 3, ?_⟩
  have h := main_trans n
  rw [show 3 * n + 3 + 2 = 3 * n + 5 from by ring,
      show 2 * (3 * n + 3) + 2 = 6 * n + 8 from by ring]
  exact h

end Sz22_2003_unofficial_955
