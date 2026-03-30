import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #941: [4/15, 33/14, 25/2, 7/11, 98/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_941

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
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

theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + e + 3, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * e + 6, 0, e + 2⟩ := by
  -- Phase 1: R4 drain e to d: (0,0,c+e+3,0,e) -> (0,0,c+e+3,e,0)
  have h1 : ⟨0, 0, c + e + 3, 0, e⟩ [fm]⊢* ⟨0, 0, c + e + 3, e, 0⟩ := by
    have := r4_drain e (c + e + 3) 0
    rw [show 0 + e = e from by ring] at this
    exact this
  -- Phase 2: R5: (0,0,c+e+3,e,0) -> (1,0,c+e+2,e+2,0)
  rw [show c + e + 3 = (c + e + 2) + 1 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (c + e + 2) + 1, e, 0⟩ = some ⟨1, 0, c + e + 2, e + 2, 0⟩
    unfold fm; simp only
  -- Phase 3: R2/R1 chain: (1,0,c+e+2,e+2,0) -> (e+3,0,c,0,e+2)
  have h3 : ⟨1, 0, c + e + 2, e + 2, 0⟩ [fm]⊢* ⟨e + 3, 0, c, 0, e + 2⟩ := by
    have := r2r1_chain (e + 2) 0 c 0
    rw [show 0 + (e + 2) + 1 = e + 3 from by ring,
        show 0 + (e + 2) = e + 2 from by ring,
        show 0 + 1 = 1 from by ring] at this
    exact this
  apply stepStar_trans h3
  -- Phase 4: R3 drain: (e+3,0,c,0,e+2) -> (0,0,c+2*(e+3),0,e+2)
  have h4 : ⟨e + 3, 0, c, 0, e + 2⟩ [fm]⊢* ⟨0, 0, c + 2 * (e + 3), 0, e + 2⟩ :=
    r3_drain (e + 3) c (e + 2)
  apply stepStar_trans h4
  rw [show c + 2 * (e + 3) = c + 2 * e + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 2⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + e + 3, 0, e⟩) ⟨0, 2⟩
  intro ⟨c, e⟩
  refine ⟨⟨c + e + 1, e + 2⟩, ?_⟩
  show ⟨0, 0, c + e + 3, 0, e⟩ [fm]⊢⁺ ⟨0, 0, (c + e + 1) + (e + 2) + 3, 0, e + 2⟩
  rw [show (c + e + 1) + (e + 2) + 3 = c + 2 * e + 6 from by ring]
  exact main_trans c e

end Sz22_2003_unofficial_941
