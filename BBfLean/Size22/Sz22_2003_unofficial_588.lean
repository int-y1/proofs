import BBfLean.FM

/-!
# sz22_2003_unofficial #588: [35/6, 121/2, 28/55, 3/7, 10/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states are `(0, 0, 0, d, e)` with `d ≥ 1`. The transition
`(0, 0, 0, d, e) →⁺ (0, 0, 0, 2d+1, e+d+4)` is decomposed into
R4 chain, opening steps, R1/R1/R3 chain, two R2 steps, and R3/R2/R2 chain.
-/

namespace Sz22_2003_unofficial_588

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b; rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    -- Goal: (0, b+1, 0, d+k, e) →* (0, b+(k+1), 0, d, e)
    have h := ih (b + 1)
    -- h: (0, b+1, 0, d+k, e) →* (0, (b+1)+k, 0, d, e)
    rw [show (b + 1) + k = b + (k + 1) from by omega] at h
    exact h

-- R1,R1,R3 chain: (2, 2*j, c, d, e+j) →* (2, 0, c+j, d+3*j, e)
theorem r1r1r3_chain : ∀ j, ∀ c d e, ⟨2, 2 * j, c, d, e + j⟩ [fm]⊢*
    ⟨2, 0, c + j, d + 3 * j, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by omega,
        show e + (j + 1) = (e + j) + 1 from by omega]
    step fm; step fm; step fm
    -- Goal: (2, 2*j, c+1, d+1+1+1, e+j) →* (2, 0, c+(j+1), d+3*(j+1), e)
    have h := ih (c + 1) (d + 1 + 1 + 1) e
    -- h: (2, 2*j, c+1, d+1+1+1, e+j) →* (2, 0, (c+1)+j, (d+1+1+1)+3*j, e)
    rw [show (c + 1) + j = c + (j + 1) from by omega,
        show (d + 1 + 1 + 1) + 3 * j = d + 3 * (j + 1) from by omega] at h
    exact h

-- R3,R2,R2 chain: (0, 0, c+j, d, e+1) →* (0, 0, c, d+j, e+3*j+1)
theorem r3r2r2_chain : ∀ j, ∀ c d e, ⟨0, 0, c + j, d, e + 1⟩ [fm]⊢*
    ⟨0, 0, c, d + j, e + 3 * j + 1⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show c + (j + 1) = (c + j) + 1 from by omega]
    step fm; step fm; step fm
    -- Goal: (0, 0, c+j, d+1, e+2+2) →* (0, 0, c, d+(j+1), e+3*(j+1)+1)
    rw [show e + 2 + 2 = (e + 3) + 1 from by omega]
    have h := ih c (d + 1) (e + 3)
    -- h: (0, 0, c+j, d+1, (e+3)+1) →* (0, 0, c, (d+1)+j, (e+3)+3*j+1)
    rw [show (d + 1) + j = d + (j + 1) from by omega,
        show (e + 3) + 3 * j + 1 = e + 3 * (j + 1) + 1 from by omega] at h
    exact h

-- Main transition: (0, 0, 0, 2k+1, 2k+3+m) →⁺ (0, 0, 0, 4k+3, 4k+8+m)
theorem main_trans : ⟨0, 0, 0, 2 * k + 1, 2 * k + 3 + m⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * k + 3, 4 * k + 8 + m⟩ := by
  -- Phase 1: R4 chain → (0, 2k+1, 0, 0, 2k+3+m)
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by omega]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * k + 1) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5, R1, R3 → (2, 2*k, 1, 2, 2*k+1+m)
  rw [show 2 * k + 3 + m = (2 * k + 2 + m) + 1 from by omega]
  step fm
  -- After R5: (1, 2*k+1, 1, 0, 2*k+2+m)
  rw [show 2 * k + 1 = (2 * k) + 1 from by omega]
  step fm
  -- After R1: (0, 2*k, 2, 1, 2*k+2+m)
  rw [show 2 * k + 2 + m = (2 * k + 1 + m) + 1 from by omega]
  step fm
  -- After R3: (2, 2*k, 1, 2, 2*k+1+m)
  -- Phase 3: R1,R1,R3 chain → (2, 0, k+1, 3k+2, k+1+m)
  rw [show 2 * k + 1 + m = (k + 1 + m) + k from by omega]
  have h3 := r1r1r3_chain k 1 2 (k + 1 + m)
  rw [show 1 + k = k + 1 from by omega, show 2 + 3 * k = 3 * k + 2 from by omega] at h3
  apply stepStar_trans h3
  -- Phase 4: R2,R2 → (0, 0, k+1, 3k+2, k+5+m)
  step fm; step fm
  -- Phase 5: R3,R2,R2 chain → (0, 0, 0, 4k+3, 4k+8+m)
  rw [show k + 1 + m + 4 = (k + 4 + m) + 1 from by omega]
  have h5 := r3r2r2_chain (k + 1) 0 (3 * k + 2) (k + 4 + m)
  rw [show 0 + (k + 1) = k + 1 from by omega] at h5
  rw [show (3 * k + 2) + (k + 1) = 4 * k + 3 from by omega,
      show (k + 4 + m) + 3 * (k + 1) + 1 = 4 * k + 8 + m from by omega] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 6⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, m⟩ ↦ ⟨0, 0, 0, 2 * k + 1, 2 * k + 3 + m⟩) ⟨0, 3⟩
  intro ⟨k, m⟩
  refine ⟨⟨2 * k + 1, m + 3⟩, ?_⟩
  show ⟨0, 0, 0, 2 * k + 1, 2 * k + 3 + m⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * (2 * k + 1) + 1, 2 * (2 * k + 1) + 3 + (m + 3)⟩
  rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by omega,
      show 2 * (2 * k + 1) + 3 + (m + 3) = 4 * k + 8 + m from by omega]
  exact main_trans
