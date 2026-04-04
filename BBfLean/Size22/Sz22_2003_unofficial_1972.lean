import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1972: [99/35, 25/22, 12/5, 7/3, 5/2]

Vector representation:
```
 0  2 -1 -1  1
-1  0  2  0 -1
 2  1 -1  0  0
 0 -1  0  1  0
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1972

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem b_to_d : ∀ k d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r3_chain : ∀ k c, ∀ a b, ⟨a, b, k + c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, b + k, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c a b
  · simp; exists 0
  · rw [show (k + 1) + c = k + c + 1 from by ring]; step fm
    apply stepStar_trans (ih c (a + 2) (b + 1)); ring_nf; finish

theorem tail_drain : ∀ n, ∀ A B C E, 2 * A + E = n →
    ⟨A, B, C + 1, 0, E⟩ [fm]⊢* ⟨A + 3 * E + 2 * (C + 1), B + 2 * E + (C + 1), 0, 0, 0⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih; intro A B C E hn
  rcases E with _ | _ | E
  · rw [show A + 3 * 0 + 2 * (C + 1) = A + 2 * (C + 1) from by ring,
        show B + 2 * 0 + (C + 1) = B + (C + 1) from by ring,
        show C + 1 = (C + 1) + 0 from by ring]
    exact r3_chain (C + 1) 0 A B
  · rcases A with _ | A
    · step fm; step fm
      show ⟨1, B + 1, C + 2, 0, 0⟩ [fm]⊢* _
      rw [show C + 2 = (C + 2) + 0 from by ring]
      apply stepStar_trans (r3_chain (C + 2) 0 1 (B + 1)); ring_nf; finish
    · step fm
      show ⟨A, B, C + 2 + 1, 0, 0⟩ [fm]⊢* _
      rw [show A + 1 + 3 * 1 + 2 * (C + 1) = A + 3 * 0 + 2 * (C + 2 + 1) from by ring,
          show B + 2 * 1 + (C + 1) = B + 2 * 0 + (C + 2 + 1) from by ring]
      exact ih (2 * A) (by omega) A B (C + 2) 0 (by omega)
  · rcases A with _ | A
    · step fm; step fm; step fm
      show ⟨0, B + 1, C + 3 + 1, 0, E⟩ [fm]⊢* _
      rw [show 0 + 3 * (E + 2) + 2 * (C + 1) = 0 + 3 * E + 2 * (C + 3 + 1) from by ring,
          show B + 2 * (E + 2) + (C + 1) = (B + 1) + 2 * E + (C + 3 + 1) from by ring]
      exact ih E (by omega) 0 (B + 1) (C + 3) E (by omega)
    · step fm
      show ⟨A, B, C + 2 + 1, 0, E + 1⟩ [fm]⊢* _
      rw [show A + 1 + 3 * (E + 2) + 2 * (C + 1) = A + 3 * (E + 1) + 2 * (C + 2 + 1) from by ring,
          show B + 2 * (E + 2) + (C + 1) = B + 2 * (E + 1) + (C + 2 + 1) from by ring]
      exact ih (2 * A + (E + 1)) (by omega) A B (C + 2) (E + 1) (by omega)

theorem full_drain : ∀ D, ∀ A B E, D ≤ 2 * A + 1 →
    ⟨A, B, 2, D, E⟩ [fm]⊢* ⟨A + D + 3 * E + 4, B + 3 * D + 2 * E + 2, 0, 0, 0⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ihD; intro A B E hDA
  rcases D with _ | _ | D
  · show ⟨A, B, 1 + 1, 0, E⟩ [fm]⊢* _
    apply stepStar_trans (tail_drain (2 * A + E) A B 1 E rfl)
    ring_nf; finish
  · step fm
    show ⟨A, B + 2, 0 + 1, 0, E + 1⟩ [fm]⊢* _
    apply stepStar_trans (tail_drain (2 * A + (E + 1)) A (B + 2) 0 (E + 1) rfl)
    ring_nf; finish
  · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    rw [show (D + 2 : ℕ) = D + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ihD D (by omega) A' (B + 4) (E + 1) (by omega))
    ring_nf; finish

theorem main_trans (a d : ℕ) (hd : d ≤ 2 * a) :
    ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + d + 4, 0, 0, 3 * d + 4, 0⟩ := by
  rw [show d + 1 = d + 0 + 1 from by ring, show a + 2 = a + 1 + 1 from by ring]
  step fm; step fm; step fm
  -- Now at (a, 2, 2, d, 0). full_drain needs d ≤ 2a+1, which follows from d ≤ 2a.
  apply stepStar_trans (full_drain d a 2 0 (by omega))
  -- Result: (a+d+4, 3d+4, 0, 0, 0). Apply b_to_d.
  rw [show a + d + 3 * 0 + 4 = a + d + 4 from by ring,
      show 2 + 3 * d + 2 * 0 + 2 = 3 * d + 4 from by ring,
      show (3 * d + 4 : ℕ) = 0 + (3 * d + 4) from by ring]
  exact b_to_d (3 * d + 4) 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 4, 0⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d + 1, 0⟩ ∧ d ≤ 2 * a)
  · intro c ⟨a, d, hq, hd⟩; subst hq
    exact ⟨⟨a + d + 4, 0, 0, 3 * d + 4, 0⟩,
      ⟨a + d + 2, 3 * d + 3, rfl, by omega⟩, main_trans a d hd⟩
  · exact ⟨2, 3, rfl, by omega⟩
