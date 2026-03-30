import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #717: [35/6, 4/55, 1331/2, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  3
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_717

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 3))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r2_chain_a : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem middle_phase : ∀ b, ∀ c d e,
    ⟨2, b, c, d, e + c + b⟩ [fm]⊢* ⟨2 * c + b + 2, 0, 0, d + b, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c d e
  match b with
  | 0 =>
    simp only [Nat.add_zero]
    apply stepStar_trans (r2_chain_a c 2 d e)
    rw [show 2 + 2 * c = 2 * c + 2 from by ring]; finish
  | 1 =>
    rw [show e + c + 1 = (e + c) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (r2_chain_a (c + 1) 1 (d + 1) e)
    rw [show 1 + 2 * (c + 1) = 2 * c + 1 + 2 from by ring]; finish
  | b' + 2 =>
    rw [show e + c + (b' + 2) = (e + c + b') + 1 + 1 from by ring]
    step fm; step fm
    rw [show e + c + b' + 1 = (e + c + b') + 1 from by ring]
    step fm
    have key := ih b' (by omega) (c + 1) (d + 2) e
    rw [show e + (c + 1) + b' = e + c + b' + 1 from by ring] at key
    apply stepStar_trans key
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 3, 0, 0, n + 1, n ^ 2 + 4 * n⟩ [fm]⊢⁺
    ⟨n + 4, 0, 0, n + 2, n ^ 2 + 6 * n + 5⟩ := by
  rw [show n + 3 = 0 + (n + 3) from by ring]
  apply step_stepStar_stepPlus
  · rw [show 0 + (n + 3) = (0 + (n + 2)) + 1 from by ring]
    show fm ⟨(0 + (n + 2)) + 1, 0, 0, n + 1, n ^ 2 + 4 * n⟩ =
      some ⟨0 + (n + 2), 0, 0, n + 1, n ^ 2 + 4 * n + 3⟩
    simp [fm]
  apply stepStar_trans (r3_chain (n + 2) 0 (n + 1) (n ^ 2 + 4 * n + 3))
  rw [show n ^ 2 + 4 * n + 3 + 3 * (n + 2) = n ^ 2 + 7 * n + 9 from by ring]
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r4_chain (n + 1) 0 0 (n ^ 2 + 7 * n + 9))
  rw [show 0 + (n + 1) = n + 1 from by ring]
  rw [show n ^ 2 + 7 * n + 9 = (n ^ 2 + 7 * n + 8) + 1 from by ring]
  step fm
  rw [show n ^ 2 + 7 * n + 8 = (n ^ 2 + 7 * n + 7) + 1 from by ring]
  step fm
  rw [show n ^ 2 + 7 * n + 7 = (n ^ 2 + 6 * n + 5) + 0 + (n + 2) from by ring]
  apply stepStar_trans (middle_phase (n + 2) 0 0 (n ^ 2 + 6 * n + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n + 3, 0, 0, n + 1, n ^ 2 + 4 * n⟩)
  · intro c ⟨n, hq⟩; subst hq
    refine ⟨⟨n + 4, 0, 0, n + 2, n ^ 2 + 6 * n + 5⟩, ⟨n + 1, by ring_nf⟩, main_trans n⟩
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_717
