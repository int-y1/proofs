import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #931: [4/15, 33/14, 25/2, 7/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_931

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem main_trans (n c : ℕ) :
    ⟨n + 2, 0, c, 0, n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, c + n + 1, 0, n + 3⟩ := by
  -- Phase 1 (first R3 step): (n+2, 0, c, 0, n+2) → (n+1, 0, c+2, 0, n+2)
  apply step_stepStar_stepPlus
  · show fm ⟨n + 2, 0, c, 0, n + 2⟩ = some ⟨n + 1, 0, c + 2, 0, n + 2⟩
    unfold fm; simp only
  -- Phase 1 (remaining R3 drain): (n+1, 0, c+2, 0, n+2) ⊢* (0, 0, c+2*(n+2), 0, n+2)
  have h1 : ⟨n + 1, 0, c + 2, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, c + 2 * (n + 2), 0, n + 2⟩ := by
    have := r3_drain (n + 1) (c + 2) (n + 2)
    rw [show c + 2 + 2 * (n + 1) = c + 2 * (n + 2) from by ring] at this
    exact this
  -- Phase 2: R4 drain: (0, 0, c+2*(n+2), 0, n+2) ⊢* (0, 0, c+2*(n+2), n+2, 0)
  have h2 : ⟨0, 0, c + 2 * (n + 2), 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, c + 2 * (n + 2), n + 2, 0⟩ := by
    have := r4_drain (n + 2) (c + 2 * (n + 2)) 0
    rw [show 0 + (n + 2) = n + 2 from by ring] at this
    exact this
  -- Phase 3: R5 kick: (0, 0, c+2*(n+2), n+2, 0) → (1, 0, c+2*n+3, n+2, 1)
  have h3 : ⟨0, 0, c + 2 * (n + 2), n + 2, 0⟩ [fm]⊢*
      ⟨1, 0, c + 2 * n + 3, n + 2, 1⟩ := by
    rw [show c + 2 * (n + 2) = (c + 2 * n + 3) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0, 0, (c + 2 * n + 3) + 1, n + 2, 0⟩ = some ⟨1, 0, c + 2 * n + 3, n + 2, 1⟩
    unfold fm; simp only
  -- Phase 4: R2/R1 chain: (1, 0, c+2*n+3, n+2, 1) ⊢* (n+3, 0, c+n+1, 0, n+3)
  have h4 : ⟨1, 0, c + 2 * n + 3, n + 2, 1⟩ [fm]⊢*
      ⟨n + 3, 0, c + n + 1, 0, n + 3⟩ := by
    have := r2r1_chain (n + 2) 0 (c + n + 1) 0
    simp only [Nat.zero_add] at this
    rw [show (c + n + 1) + (n + 2) = c + 2 * n + 3 from by ring,
        show n + 2 + 1 = n + 3 from by ring] at this
    exact this
  -- Compose all phases
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n + 2, 0, c, 0, n + 2⟩) ⟨0, 1⟩
  intro ⟨n, c⟩
  refine ⟨⟨n + 1, c + n + 1⟩, ?_⟩
  show ⟨n + 2, 0, c, 0, n + 2⟩ [fm]⊢⁺ ⟨(n + 1) + 2, 0, c + n + 1, 0, (n + 1) + 2⟩
  rw [show (n + 1) + 2 = n + 3 from by ring]
  exact main_trans n c

end Sz22_2003_unofficial_931
