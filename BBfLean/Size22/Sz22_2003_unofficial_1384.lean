import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1384: [63/10, 5/33, 4/3, 121/7, 21/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 2 -1  0  0  0
 0  0  0 -1  2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1384

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: each d gives 2 e.
theorem d_to_e : ∀ k, ∀ d e, (⟨a, 0, 0, d + k, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro d e; ring_nf; finish
  · intro d e; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih d (e + 2)); ring_nf; finish

-- R2/R1 chain.
theorem r2r1_chain : ∀ j, ∀ k d e,
    (⟨j, k + 1, 0, d, j + e⟩ : Q) [fm]⊢* ⟨0, j + k + 1, 0, j + d, e⟩ := by
  intro j; induction' j with j ih
  · intro k d e; ring_nf; finish
  · intro k d e
    rw [show j + 1 + e = (j + e) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (k + 1) (d + 1) e); ring_nf; finish

-- R2 drain.
theorem r2_drain : ∀ k, ∀ b c d, (⟨0, b + k, c, d, k⟩ : Q) [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c d; ring_nf; finish
  · intro b c d
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d); ring_nf; finish

-- R3 drain (d unchanged).
theorem r3_drain : ∀ k, ∀ a d, (⟨a, k, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; ring_nf; finish
  · intro a d; step fm
    apply stepStar_trans (ih (a + 2) d); ring_nf; finish

-- R3/R1 phase by strong induction on C.
theorem r3r1_phase : ∀ C, ∀ B D,
    (⟨0, B + 1, C + 1, D, 0⟩ : Q) [fm]⊢* ⟨2 * B + 3 * C + 5, 0, 0, D + C + 1, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro B D
  rcases C with _ | C
  · step fm; step fm
    apply stepStar_trans (r3_drain (B + 2) 1 (D + 1)); ring_nf; finish
  · rw [show C + 1 + 1 = C + 2 from by ring]
    step fm; step fm; step fm
    rcases C with _ | C'
    · rw [show B + 2 + 2 = B + 4 from by ring, show D + 1 + 1 = D + 2 from by ring]
      apply stepStar_trans (r3_drain (B + 4) 0 (D + 2)); ring_nf; finish
    · rw [show B + 2 + 2 = (B + 3) + 1 from by ring,
          show D + 1 + 1 = D + 2 from by ring]
      apply stepStar_trans (ih C' (by omega) (B + 3) (D + 2)); ring_nf; finish

-- Main transition using parameters (n, p) where state = (2n+p+2, 0, 0, n+p+1, 0).
-- Transition: (n, p) → (2n+p+1, p+1).
theorem main_trans (n p : ℕ) :
    (⟨2 * n + p + 2, 0, 0, n + p + 1, 0⟩ : Q) [fm]⊢⁺
      ⟨4 * n + 3 * p + 5, 0, 0, 2 * n + 2 * p + 3, 0⟩ := by
  -- Phase 1: d_to_e.
  have h1 : (⟨2 * n + p + 2, 0, 0, n + p + 1, 0⟩ : Q) [fm]⊢*
      ⟨2 * n + p + 2, 0, 0, 0, 2 * n + 2 * p + 2⟩ := by
    rw [show n + p + 1 = 0 + (n + p + 1) from by ring]
    apply stepStar_trans (d_to_e (n + p + 1) 0 0 (a := 2 * n + p + 2)); ring_nf; finish
  -- Phase 2: R5 then r2r1_chain.
  have h2 : (⟨2 * n + p + 2, 0, 0, 0, 2 * n + 2 * p + 2⟩ : Q) [fm]⊢⁺
      ⟨0, 2 * n + p + 2, 0, 2 * n + p + 2, p + 1⟩ := by
    rw [show 2 * n + p + 2 = (2 * n + p + 1) + 1 from by ring,
        show 2 * n + 2 * p + 2 = (2 * n + p + 1) + (p + 1) from by ring]
    step fm
    apply stepStar_trans (r2r1_chain (2 * n + p + 1) 0 1 (p + 1)); ring_nf; finish
  -- Phase 3: r2_drain.
  have h3 : (⟨0, 2 * n + p + 2, 0, 2 * n + p + 2, p + 1⟩ : Q) [fm]⊢*
      ⟨0, 2 * n + 1, p + 1, 2 * n + p + 2, 0⟩ := by
    have := r2_drain (p + 1) (2 * n + 1) 0 (2 * n + p + 2)
    ring_nf at this ⊢; exact this
  -- Phase 4: r3r1_phase.
  have h4 : (⟨0, 2 * n + 1, p + 1, 2 * n + p + 2, 0⟩ : Q) [fm]⊢*
      ⟨4 * n + 3 * p + 5, 0, 0, 2 * n + 2 * p + 3, 0⟩ := by
    apply stepStar_trans (r3r1_phase p (2 * n) (2 * n + p + 2)); ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, p⟩ ↦ ⟨2 * n + p + 2, 0, 0, n + p + 1, 0⟩) ⟨0, 0⟩
  intro ⟨n, p⟩
  refine ⟨⟨2 * n + p + 1, p + 1⟩, ?_⟩
  show (⟨2 * n + p + 2, 0, 0, n + p + 1, 0⟩ : Q) [fm]⊢⁺
    ⟨2 * (2 * n + p + 1) + (p + 1) + 2, 0, 0, (2 * n + p + 1) + (p + 1) + 1, 0⟩
  have h := main_trans n p
  rw [show 4 * n + 3 * p + 5 = 2 * (2 * n + p + 1) + (p + 1) + 2 from by ring,
      show 2 * n + 2 * p + 3 = (2 * n + p + 1) + (p + 1) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1384
