import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #939: [4/15, 33/14, 25/2, 7/11, 63/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  2 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_939

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

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

theorem main_trans (n c : ℕ) :
    ⟨0, 0, c + n + 5, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * n + 12, 0, n + 2⟩ := by
  -- Phase 1: R4 drain
  have h1 : ⟨0, 0, c + n + 5, 0, n + 1⟩ [fm]⊢*
      ⟨0, 0, c + n + 5, n + 1, 0⟩ := by
    have h := r4_drain (n + 1) (c + n + 5) 0
    ring_nf at h ⊢; exact h
  -- Phase 2: R5 + R1 + R1 + R2 + R1 (5 steps) then R2R1 chain
  have h2 : ⟨0, 0, c + n + 5, n + 1, 0⟩ [fm]⊢⁺
      ⟨n + 6, 0, c, 0, n + 2⟩ := by
    rw [show c + n + 5 = (c + n + 2 + 1 + 1) + 1 from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, (c + n + 2 + 1 + 1) + 1, n + 1, 0⟩ =
          some ⟨0, 2, c + n + 2 + 1 + 1, (n + 1) + 1, 0⟩
      unfold fm; simp only
    rw [show (n : ℕ) + 1 + 1 = n + 2 from by ring,
        show c + n + 2 + 1 + 1 = (c + n + 2 + 1) + 1 from by ring]
    step fm
    rw [show c + n + 2 + 1 = (c + n + 2) + 1 from by ring]
    step fm
    rw [show (4 : ℕ) = 3 + 1 from rfl,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm
    rw [show c + n + 2 = (c + n + 1) + 1 from by ring]
    step fm
    rw [show (5 : ℕ) = 4 + 1 from rfl,
        show c + n + 1 = c + (n + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    have h := r2r1_chain (n + 1) 4 c 0
    rw [show 4 + (n + 1) + 1 = n + 6 from by ring,
        show 0 + (n + 1) + 1 = n + 2 from by ring] at h
    exact h
  -- Phase 3: R3 drain
  have h3 : ⟨n + 6, 0, c, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, c + 2 * n + 12, 0, n + 2⟩ := by
    have h := r3_drain (n + 6) c (n + 2)
    rw [show c + 2 * (n + 6) = c + 2 * n + 12 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus h1 h2)
    h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 8, 0, 1⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨0, 0, c + n + 5, 0, n + 1⟩) ⟨0, 3⟩
  intro ⟨n, c⟩
  refine ⟨⟨n + 1, c + n + 6⟩, ?_⟩
  show ⟨0, 0, c + n + 5, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, (c + n + 6) + (n + 1) + 5, 0, (n + 1) + 1⟩
  rw [show (c + n + 6) + (n + 1) + 5 = c + 2 * n + 12 from by ring,
      show (n : ℕ) + 1 + 1 = n + 2 from by ring]
  exact main_trans n c
