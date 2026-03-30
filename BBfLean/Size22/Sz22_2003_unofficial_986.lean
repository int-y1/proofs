import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #986: [4/15, 33/14, 65/2, 7/11, 363/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_986

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | _ => none

-- R4 chain: drain e into d
theorem r4_chain : ∀ k, ∀ c d f, ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c d f; ring_nf; finish
  | succ k ih =>
    intro c d f; step fm
    apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

-- R3 chain: drain a into c and f
theorem r3_chain : ∀ k, ∀ c e f, ⟨k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro c e f; ring_nf; finish
  | succ k ih =>
    intro c e f; step fm
    apply stepStar_trans (ih (c + 1) e (f + 1)); ring_nf; finish

-- R2R1 chain: alternating R2 then R1
theorem r2r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, (0 : ℕ), c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a c d e f; ring_nf; finish
  | succ k ih =>
    intro a c d e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f); ring_nf; finish

-- R2 chain: drain d using R2 only
theorem r2_chain : ∀ k, ∀ a b e f,
    ⟨a + k, b, (0 : ℕ), k, e, f⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a b e f; ring_nf; finish
  | succ k ih =>
    intro a b e f
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1) f); ring_nf; finish

-- R3R1 chain: alternating R3 then R1
theorem r3r1_chain : ∀ k, ∀ a b e f,
    ⟨a + 1, b + k, (0 : ℕ), 0, e, f⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro a b e f; ring_nf; finish
  | succ k ih =>
    intro a b e f
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) b e (f + 1)); ring_nf; finish

-- Main transition: C(n,f) ⊢⁺ C(n+1, f+2*(n+1))
-- C(n,f) = (0, 0, n+1, 0, 2*n, f+1)
theorem main_trans (n f : ℕ) :
    ⟨(0 : ℕ), 0, n + 1, 0, 2 * n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, 2 * (n + 1), f + 2 * (n + 1)⟩ := by
  rcases n with _ | n
  · -- n = 0: R5, R1, R3, R3
    step fm; step fm; step fm; step fm; ring_nf; finish
  · -- n ≥ 1
    show ⟨(0 : ℕ), 0, n + 2, 0, 2 * n + 2, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 0, 2 * n + 4, f + 2 * n + 4⟩
    -- Phase 1: R4 chain: drain e into d
    have h1 : ⟨(0 : ℕ), 0, n + 2, 0, 2 * n + 2, f + 1⟩ [fm]⊢*
              ⟨0, 0, n + 2, 2 * n + 2, 0, f + 1⟩ := by
      have := r4_chain (2 * n + 2) (n + 2) 0 (f + 1)
      rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring] at this; exact this
    -- Phase 2: R5
    have h2 : ⟨(0 : ℕ), 0, n + 2, 2 * n + 2, 0, f + 1⟩ [fm]⊢⁺
              ⟨0, 1, n + 2, 2 * n + 2, 2, f⟩ := by
      step fm; finish
    -- Phase 3: R1
    have h3 : ⟨(0 : ℕ), 1, n + 2, 2 * n + 2, 2, f⟩ [fm]⊢*
              ⟨2, 0, n + 1, 2 * n + 2, 2, f⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm; finish
    -- Phase 4: R2R1 chain (n+1 rounds)
    have h4 : ⟨2, (0 : ℕ), n + 1, 2 * n + 2, 2, f⟩ [fm]⊢*
              ⟨n + 3, 0, 0, n + 1, n + 3, f⟩ := by
      have := r2r1_chain (n + 1) 1 0 (n + 1) 2 f
      simp only [] at this
      convert this using 2; ring_nf
    -- Phase 5: R2 chain (n+1 rounds)
    have h5 : ⟨n + 3, (0 : ℕ), 0, n + 1, n + 3, f⟩ [fm]⊢*
              ⟨2, n + 1, 0, 0, 2 * n + 4, f⟩ := by
      have := r2_chain (n + 1) 2 0 (n + 3) f
      simp only [] at this
      convert this using 2; ring_nf
    -- Phase 6: R3R1 chain (n+1 rounds)
    have h6 : ⟨2, n + 1, (0 : ℕ), 0, 2 * n + 4, f⟩ [fm]⊢*
              ⟨n + 3, 0, 0, 0, 2 * n + 4, f + n + 1⟩ := by
      have := r3r1_chain (n + 1) 1 0 (2 * n + 4) f
      simp only [] at this
      convert this using 2; ring_nf
    -- Phase 7: R3 chain (n+3 rounds)
    have h7 : ⟨n + 3, (0 : ℕ), 0, 0, 2 * n + 4, f + n + 1⟩ [fm]⊢*
              ⟨0, 0, n + 3, 0, 2 * n + 4, f + 2 * n + 4⟩ := by
      have := r3_chain (n + 3) 0 (2 * n + 4) (f + n + 1)
      simp only [] at this
      convert this using 2; ring_nf
    -- Compose
    exact stepStar_stepPlus_stepPlus h1
      (stepPlus_stepStar_stepPlus h2
        (stepStar_trans h3
          (stepStar_trans h4
            (stepStar_trans h5
              (stepStar_trans h6 h7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, n + 1, 0, 2 * n, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + 2 * n + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, n + 1, 0, 2 * n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 1 + 1, 0, 2 * (n + 1), f + 2 * n + 1 + 1⟩
  rw [show n + 1 + 1 = n + 2 from by ring,
      show f + 2 * n + 1 + 1 = f + 2 * (n + 1) from by ring]
  exact main_trans n f

end Sz22_2003_unofficial_986
