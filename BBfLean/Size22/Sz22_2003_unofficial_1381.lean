import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1381: [63/10, 5/33, 28/3, 11/7, 21/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 2 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1381

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: (a, 0, 0, d+k, e) ⊢* (a, 0, 0, d, e+k).
theorem d_to_e : ∀ k d e, (⟨a, 0, 0, d + k, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- R2/R1 chain: (j, k+1, 0, d, j+e) ⊢* (0, j+k+1, 0, j+d, e).
theorem r2r1_chain : ∀ j, ∀ k d e,
    (⟨j, k + 1, 0, d, j + e⟩ : Q) [fm]⊢* ⟨0, j + k + 1, 0, j + d, e⟩ := by
  intro j; induction' j with j ih
  · intro k d e; ring_nf; finish
  · intro k d e
    rw [show j + 1 + e = (j + e) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (k + 1) (d + 1) e); ring_nf; finish

-- R2 drain: (0, b+k, c, d, k) ⊢* (0, b, c+k, d, 0).
theorem r2_drain : ∀ k, ∀ b c d, (⟨0, b + k, c, d, k⟩ : Q) [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c d; ring_nf; finish
  · intro b c d
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (c + 1) d); ring_nf; finish

-- Pure R3 drain: (a, k, 0, d, 0) ⊢* (a+2k, 0, 0, d+k, 0).
theorem r3_drain : ∀ k, ∀ a d, (⟨a, k, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; ring_nf; finish
  · intro a d; step fm
    apply stepStar_trans (ih (a + 2) (d + 1)); ring_nf; finish

-- R3/R1 phase: (0, B+1, C, D, 0) ⊢* (2*B+3*C+2, 0, 0, D+B+3*C+1, 0).
theorem r3r1_phase : ∀ C, ∀ B D,
    (⟨0, B + 1, C, D, 0⟩ : Q) [fm]⊢* ⟨2 * B + 3 * C + 2, 0, 0, D + B + 3 * C + 1, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih
  rcases C with _ | _ | C
  · -- C = 0: pure R3 drain.
    intro B D
    have := r3_drain (B + 1) 0 D
    rw [show 0 + 2 * (B + 1) = 2 * B + 3 * 0 + 2 from by ring,
        show D + (B + 1) = D + B + 3 * 0 + 1 from by ring] at this
    exact this
  · -- C = 1: R3, R1, then R3 drain.
    intro B D
    step fm; step fm
    apply stepStar_trans (r3_drain (B + 2) 1 (D + 2)); ring_nf; finish
  · -- C + 2: R3, R1, R1, then recurse with (B+3, C, D+3).
    intro B D
    rw [show C + 2 = (C + 1) + 1 from rfl]
    step fm; step fm; step fm
    rw [show B + 2 + 2 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih C (by omega) (B + 3) (D + 3)); ring_nf; finish

-- Main transition.
theorem main_trans (a n : ℕ) (ha : a ≥ n + 2) :
    (⟨a, 0, 0, a + n, 0⟩ : Q) [fm]⊢⁺ ⟨2 * a + n + 1, 0, 0, 2 * a + 2 * n + 2, 0⟩ := by
  -- Phase 1: d_to_e.
  have h1 : (⟨a, 0, 0, a + n, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, a + n⟩ := by
    have := d_to_e (a + n) 0 0 (a := a)
    simp at this; exact this
  -- Phase 2: R5 then r2r1_chain.
  have h2 : (⟨a, 0, 0, 0, a + n⟩ : Q) [fm]⊢⁺ ⟨0, a, 0, a, n + 1⟩ := by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [show a' + 1 + n = a' + (n + 1) from by ring]
    step fm
    exact r2r1_chain a' 0 1 (n + 1)
  -- Phase 3: r2_drain.
  have h3 : (⟨0, a, 0, a, n + 1⟩ : Q) [fm]⊢* ⟨0, a - n - 1, n + 1, a, 0⟩ := by
    have := r2_drain (n + 1) (a - n - 1) 0 a
    rw [show a - n - 1 + (n + 1) = a from by omega,
        show 0 + (n + 1) = n + 1 from by ring] at this; exact this
  -- Phase 4: r3r1_phase.
  have h4 : (⟨0, a - n - 1, n + 1, a, 0⟩ : Q) [fm]⊢*
      ⟨2 * a + n + 1, 0, 0, 2 * a + 2 * n + 2, 0⟩ := by
    have := r3r1_phase (n + 1) (a - n - 2) a
    rw [show a - n - 2 + 1 = a - n - 1 from by omega,
        show 2 * (a - n - 2) + 3 * (n + 1) + 2 = 2 * a + n + 1 from by omega,
        show a + (a - n - 2) + 3 * (n + 1) + 1 = 2 * a + 2 * n + 2 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a n, q = ⟨a, 0, 0, a + n, 0⟩ ∧ a ≥ n + 2)
  · intro q ⟨a, n, hq, ha⟩
    refine ⟨⟨2 * a + n + 1, 0, 0, 2 * a + 2 * n + 2, 0⟩,
      ⟨2 * a + n + 1, n + 1, ?_, by omega⟩,
      hq ▸ main_trans a n ha⟩
    ring_nf
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1381
