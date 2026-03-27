import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #155: [1/45, 35/2, 182/55, 33/7, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  1  0  0
 1  0 -1  1 -1  1
 0  1  0 -1  1  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_155

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 chain: d → b, e
theorem r4_chain : ∀ k, ∀ b d e f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro b d e f; exists 0
  | succ k ih =>
    intro b d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R5+R1 drain pair: removes 3 from b and 1 from f
theorem drain_pair : ∀ b e f,
    ⟨0, b + 3, 0, 0, e, f + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, 0, e, f⟩ := by
  intro b e f
  step fm; step fm
  ring_nf; finish

-- Iterated drain pairs
theorem drain_pairs : ∀ k, ∀ b e f,
    ⟨0, b + 3 * k, 0, 0, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, 0, e, f⟩ := by
  intro k; induction k with
  | zero => intro b e f; exists 0
  | succ k ih =>
    intro b e f
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    apply stepStar_trans (drain_pair _ _ _)
    exact ih _ _ _

-- R3+R2 chain: c,e → d,f
theorem r3r2_chain : ∀ k, ∀ d e f,
    ⟨0, 0, 1, d, e + k, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, 1, d + 2 * k, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: one full cycle
theorem main_trans (d g : ℕ) :
    ⟨0, 0, 1, 3 * d + 1, 0, d + g⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 1, 3 * (2 * d + 1) + 1, 0, (2 * d + 1) + (d + g + 1)⟩ := by
  -- Phase 1: Head (5 steps)
  -- (0, 0, 1, 3d+1, 0, d+g) → (0, 0, 0, 3d+1, 1, d+g+1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 1, 3 * d + 1, 0, d + g⟩ = some ⟨0, 1, 1, 3 * d, 1, d + g⟩
    rw [show 3 * d + 1 = (3 * d) + 1 from by ring]; rfl
  step fm
  rw [show 3 * d + 1 = (3 * d) + 1 from by ring]
  step fm
  rw [show 3 * d + 2 = (3 * d + 1) + 1 from by ring]
  step fm; step fm
  -- Phase 2: R4 chain (3d+1 steps)
  -- (0, 0, 0, 3d+1, 1, d+g+1) → (0, 3d+1, 0, 0, 3d+2, d+g+1)
  apply stepStar_trans
  · have h := r4_chain (3 * d + 1) 0 0 1 (d + g + 1)
    simp only [(by ring : 0 + (3 * d + 1) = 3 * d + 1),
               (by ring : 1 + (3 * d + 1) = 3 * d + 2)] at h
    exact h
  -- Phase 3: Drain pairs (d pairs)
  -- (0, 3d+1, 0, 0, 3d+2, d+g+1) → (0, 1, 0, 0, 3d+2, g+1)
  apply stepStar_trans
  · have h := drain_pairs d 1 (3 * d + 2) (g + 1)
    simp only [(by ring : 1 + 3 * d = 3 * d + 1),
               (by ring : (g + 1) + d = d + g + 1)] at h
    exact h
  -- Phase 4: Final R5 (1 step)
  -- (0, 1, 0, 0, 3d+2, g+1) → (0, 0, 1, 0, 3d+2, g)
  apply stepStar_trans
  · show ⟨0, 1, 0, 0, 3 * d + 2, g + 1⟩ [fm]⊢* ⟨0, 0, 1, 0, 3 * d + 2, g⟩
    rw [show (1 : ℕ) = 0 + 1 from by ring, show g + 1 = g + 1 from rfl]
    step fm; finish
  -- Phase 5: R3+R2 chain (3d+2 pairs)
  -- (0, 0, 1, 0, 3d+2, g) → (0, 0, 1, 6d+4, 0, g+3d+2)
  have h := r3r2_chain (3 * d + 2) 0 0 g
  simp only [(by ring : 0 + (3 * d + 2) = 3 * d + 2),
             (by ring : 0 + 2 * (3 * d + 2) = 6 * d + 4),
             (by ring : g + (3 * d + 2) = g + 3 * d + 2)] at h
  rw [show 3 * (2 * d + 1) + 1 = 6 * d + 4 from by ring,
      show (2 * d + 1) + (d + g + 1) = g + 3 * d + 2 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0,0) ⊢ (0,0,1,1,0,0) = C(0,0)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨0, 0, 1, 3 * d + 1, 0, d + g⟩) ⟨0, 0⟩
  intro ⟨d, g⟩
  exact ⟨⟨2 * d + 1, d + g + 1⟩, main_trans d g⟩

end Sz22_2003_unofficial_155
