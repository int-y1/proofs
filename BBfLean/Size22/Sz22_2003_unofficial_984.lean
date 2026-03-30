import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #984: [4/15, 33/14, 65/2, 7/11, 28/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 2  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_984

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | _ => none

theorem r4_drain : ∀ k c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c d f; ring_nf; finish
  | succ k ih =>
    intro c d f; step fm
    apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

theorem r2r1_chain : ∀ k a c d e f,
    ⟨a + 1, (0 : ℕ), c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a c d e f; ring_nf; finish
  | succ k ih =>
    intro a c d e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f); ring_nf; finish

theorem r3_drain : ∀ k c e f,
    ⟨k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro c e f; ring_nf; finish
  | succ k ih =>
    intro c e f; step fm
    apply stepStar_trans (ih (c + 1) e (f + 1)); ring_nf; finish

theorem main_trans (n m : ℕ) :
    ⟨(0 : ℕ), 0, 2 * n + 1, 0, n, m + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 3, 0, n + 1, m + n + 3⟩ := by
  rcases n with _ | n
  · -- n = 0
    step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish
  · -- n ≥ 1
    -- Phase 1: R4 drain e to d
    have h1 : ⟨(0 : ℕ), 0, 2 * (n + 1) + 1, 0, n + 1, m + 1⟩ [fm]⊢*
              ⟨0, 0, 2 * (n + 1) + 1, n + 1, 0, m + 1⟩ := by
      have := r4_drain (n + 1) (2 * (n + 1) + 1) 0 (m + 1)
      simp only [show 0 + (n + 1) = n + 1 from by omega] at this
      exact this
    -- Phase 2: R5 fires once
    have h2 : ⟨(0 : ℕ), 0, 2 * (n + 1) + 1, n + 1, 0, m + 1⟩ [fm]⊢⁺
              ⟨2, 0, 2 * (n + 1) + 1, n + 2, 0, m⟩ := by
      apply step_stepPlus
      show fm ⟨0, 0, 2 * (n + 1) + 1, n + 1, 0, m + 1⟩ = some ⟨2, 0, 2 * (n + 1) + 1, n + 2, 0, m⟩
      unfold fm; simp only
    -- Phase 3: R2R1 chain draining d
    have h3 : ⟨2, (0 : ℕ), 2 * (n + 1) + 1, n + 2, 0, m⟩ [fm]⊢*
              ⟨n + 4, 0, n + 1, 0, n + 2, m⟩ := by
      have := r2r1_chain (n + 2) 1 (n + 1) 0 0 m
      simp only [show (n + 1) + (n + 2) = 2 * (n + 1) + 1 from by ring,
                  show 1 + (n + 2) + 1 = n + 4 from by omega,
                  show 0 + (n + 2) = n + 2 from by omega] at this
      exact this
    -- Phase 4: R3 drain a to c and f
    have h4 : ⟨n + 4, (0 : ℕ), n + 1, 0, n + 2, m⟩ [fm]⊢*
              ⟨0, 0, 2 * n + 5, 0, n + 2, m + n + 4⟩ := by
      have := r3_drain (n + 4) (n + 1) (n + 2) m
      simp only [show (n + 1) + (n + 4) = 2 * n + 5 from by ring,
                  show m + (n + 4) = m + n + 4 from by ring] at this
      exact this
    -- Compose
    show ⟨(0 : ℕ), 0, 2 * (n + 1) + 1, 0, n + 1, m + 1⟩ [fm]⊢⁺
         ⟨0, 0, 2 * n + 5, 0, n + 2, m + n + 4⟩
    exact stepStar_stepPlus_stepPlus h1
      (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, m⟩ ↦ ⟨0, 0, 2 * n + 1, 0, n, m + 1⟩) ⟨0, 0⟩
  intro ⟨n, m⟩
  exact ⟨⟨n + 1, m + n + 2⟩, main_trans n m⟩

end Sz22_2003_unofficial_984
