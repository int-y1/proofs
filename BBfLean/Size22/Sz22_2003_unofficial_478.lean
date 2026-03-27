import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #478: [28/15, 3/22, 1225/2, 11/7, 2/11]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  2  0
 0  0  0 -1  1
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_478

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: d → e
theorem d_to_e {c : ℕ} : ∀ k d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e; rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- R3 chain: a → 0, c += 2a, d += 2a
theorem r3_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; simp; exists 0
  | succ k ih =>
    intro c d; show ⟨k + 1, 0, c, d, 0⟩ [fm]⊢* _; step fm
    apply stepStar_trans (ih (c + 2) (d + 2)); ring_nf; finish

-- R2 drain: a, e → b (when c = 0)
theorem r2_drain : ∀ k A B D E, ⟨A + k, B, 0, D, E + k⟩ [fm]⊢* ⟨A, B + k, 0, D, E⟩ := by
  intro k; induction k with
  | zero => intro A B D E; exists 0
  | succ k ih =>
    intro A B D E
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    show ⟨(A + k) + 1, B, 0, D, (E + k) + 1⟩ [fm]⊢* _; step fm
    apply stepStar_trans (ih A (B + 1) D E); ring_nf; finish

-- Interleaved R1, R2 chain
theorem r1r2_chain : ∀ k A D E,
    ⟨A, 1, k + 1, D, E + k⟩ [fm]⊢* ⟨A + k + 2, 0, 0, D + k + 1, E⟩ := by
  intro k; induction k with
  | zero =>
    intro A D E
    show ⟨A, 0 + 1, 0 + 1, D, E⟩ [fm]⊢* ⟨A + 2, 0, 0, D + 1, E⟩
    step fm; finish
  | succ k ih =>
    intro A D E
    -- State: (A, 1, k+2, D, E+k+1)
    -- R1: b=1≥1, c=k+2≥1 → (A+2, 0, k+1, D+1, E+k+1)
    -- R2: a=A+2≥1, e=E+k+1≥1 → (A+1, 1, k+1, D+1, E+k)
    rw [show E + (k + 1) = E + k + 1 from by ring]
    show ⟨A, 0 + 1, (k + 1) + 1, D, (E + k) + 1⟩ [fm]⊢* _; step fm
    -- After R1: (A+2, 0, k+1, D+1, E+k+1)
    -- Need to show R2 fires. The show must match the pattern (a+1, b, c, d, e+1).
    rw [show E + k + 1 = (E + k) + 1 from by ring]
    show ⟨(A + 1) + 1, 0, k + 1, D + 1, (E + k) + 1⟩ [fm]⊢* _; step fm
    -- After R2: (A+1, 1, k+1, D+1, E+k)
    apply stepStar_trans (ih (A + 1) (D + 1) E); ring_nf; finish

-- R3, R1, R1 chain: k triples consuming 2k from b
theorem r3r1r1_chain : ∀ k A B D,
    ⟨A + 1, B + 2 * k, 0, D, 0⟩ [fm]⊢* ⟨A + 3 * k + 1, B, 0, D + 4 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro A B D; simp; exists 0
  | succ k ih =>
    intro A B D
    -- State: (A+1, B+2k+2, 0, D, 0)
    -- R1: b=B+2k+2≥1 but c=0, so R1 doesn't fire.
    -- R2: e=0, doesn't fire.
    -- R3: a=A+1≥1, fires → (A, B+2k+2, 2, D+2, 0)
    rw [show B + 2 * (k + 1) = B + 2 * k + 2 from by ring]
    show ⟨A + 1, B + 2 * k + 2, 0, D, 0⟩ [fm]⊢* _
    -- For R3 to fire: pattern (a+1, b, c, d, e) with R1/R2 not matching.
    -- a+1 = A+1, b = B+2k+2, c = 0, d = D, e = 0.
    -- R1: needs c+1, c=0 so no. R2: needs e+1, e=0 so no. R3: a+1 pattern matches.
    show ⟨(A) + 1, B + 2 * k + 2, 0, D, 0⟩ [fm]⊢* _; step fm
    -- After R3: (A, B+2k+2, 2, D+2, 0)
    -- R1: b=B+2k+2≥1, c=2≥1 → (A+2, B+2k+1, 1, D+3, 0)
    show ⟨A, (B + 2 * k + 1) + 1, (1) + 1, D + 2, 0⟩ [fm]⊢* _; step fm
    -- R1: b=B+2k+1≥1, c=1≥1 → (A+4, B+2k, 0, D+4, 0)
    show ⟨A + 2, (B + 2 * k) + 1, (0) + 1, D + 3, 0⟩ [fm]⊢* _; step fm
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) B (D + 4)); ring_nf; finish

-- Combined phases 1-4: (0, 0, C, C+J+1, 0) ⊢⁺ (C+1-J, J, 0, C, 0)
theorem phases_1_to_4 (C J : ℕ) (hC : C ≥ 1) (hJ1 : J ≥ 1) (hJ2 : J ≤ C) :
    ⟨0, 0, C, C + J + 1, 0⟩ [fm]⊢⁺ ⟨C + 1 - J, J, 0, C, 0⟩ := by
  -- Phase 1: d_to_e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, C, 0, C + J + 1⟩)
  · have h := @d_to_e C (C + J + 1) 0 0; simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, C, 0, C + J⟩)
  · show fm ⟨0, 0, C, 0, (C + J) + 1⟩ = some ⟨0 + 1, 0, C, 0, C + J⟩
    simp [fm]
  -- R2
  apply stepStar_trans (c₂ := ⟨0, 1, C, 0, C + J - 1⟩)
  · rw [show C + J = (C + J - 1) + 1 from by omega]
    show ⟨(0) + 1, 0, C, 0, (C + J - 1) + 1⟩ [fm]⊢* _; step fm; finish
  -- Phase 3: r1r2_chain
  apply stepStar_trans (c₂ := ⟨C + 1, 0, 0, C, J⟩)
  · have h := r1r2_chain (C - 1) 0 0 J
    rw [show (0 : ℕ) + (C - 1) + 2 = C + 1 from by omega,
        show (0 : ℕ) + (C - 1) + 1 = C from by omega,
        show J + (C - 1) = C + J - 1 from by omega,
        show (C - 1 : ℕ) + 1 = C from by omega] at h; exact h
  -- Phase 4: r2_drain
  -- (C+1, 0, 0, C, J) →* (C+1-J, J, 0, C, 0)
  have h := r2_drain J (C + 1 - J) 0 C 0
  simp only [Nat.zero_add] at h
  rw [show C + 1 - J + J = C + 1 from by omega] at h; exact h

-- Even case: D - C - 1 = 2K, so D = C + 2K + 1
theorem main_even (C K : ℕ) (hC : C ≥ 1) (hK : K ≥ 1) (hCK : 2 * K ≤ C) :
    ⟨0, 0, C, C + 2 * K + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * C + 2 * K + 2, 3 * C + 6 * K + 2, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (phases_1_to_4 C (2 * K) hC (by omega) (by omega))
  -- State: (C+1-2K, 2K, 0, C, 0)
  -- r3r1r1_chain with K rounds: A+1 = C+1-2K, so A = C-2K. B = 0.
  apply stepStar_trans (c₂ := ⟨C + K + 1, 0, 0, C + 4 * K, 0⟩)
  · have h := r3r1r1_chain K (C - 2 * K) 0 C
    rw [show C - 2 * K + 1 = C + 1 - 2 * K from by omega,
        show (0 : ℕ) + 2 * K = 2 * K from by ring,
        show C - 2 * K + 3 * K + 1 = C + K + 1 from by omega] at h; exact h
  have h := r3_chain (C + K + 1) 0 (C + 4 * K)
  rw [show 0 + 2 * (C + K + 1) = 2 * C + 2 * K + 2 from by ring,
      show C + 4 * K + 2 * (C + K + 1) = 3 * C + 6 * K + 2 from by ring] at h; exact h

-- Odd case: D - C - 1 = 2K + 1, so D = C + 2K + 2
theorem main_odd (C K : ℕ) (hC : C ≥ 1) (hCK : 2 * K + 1 ≤ C) :
    ⟨0, 0, C, C + 2 * K + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * C + 2 * K + 3, 3 * C + 6 * K + 5, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (phases_1_to_4 C (2 * K + 1) hC (by omega) hCK)
  -- State: (C-2K, 2K+1, 0, C, 0)
  -- r3r1r1_chain with K rounds leaving b = 1
  apply stepStar_trans (c₂ := ⟨C + K, 1, 0, C + 4 * K, 0⟩)
  · have h := r3r1r1_chain K (C - 2 * K - 1) 1 C
    rw [show C - 2 * K - 1 + 1 = C + 1 - (2 * K + 1) from by omega,
        show (1 : ℕ) + 2 * K = 2 * K + 1 from by ring,
        show C - 2 * K - 1 + 3 * K + 1 = C + K from by omega] at h; exact h
  -- State: (C+K, 1, 0, C+4K, 0). R3 then R1.
  apply stepStar_trans (c₂ := ⟨C + K - 1, 1, 2, C + 4 * K + 2, 0⟩)
  · -- R3: (C+K, 1, 0, C+4K, 0) → (C+K-1, 1, 2, C+4K+2, 0)
    -- Pattern: (a+1, b, c, d, e) → (a, b, c+2, d+2, e). Need c=0, b, e don't trigger R1/R2.
    -- R1: b=1≥1 but c=0: no. R2: e=0: no. R3: a=C+K≥1: yes.
    rw [show C + K = (C + K - 1) + 1 from by omega]
    show ⟨(C + K - 1) + 1, 1, 0, C + 4 * K, 0⟩ [fm]⊢* _; step fm; finish
  -- R1: (C+K-1, 1, 2, C+4K+2, 0) → (C+K+1, 0, 1, C+4K+3, 0)
  apply stepStar_trans (c₂ := ⟨C + K + 1, 0, 1, C + 4 * K + 3, 0⟩)
  · show ⟨C + K - 1, (0) + 1, (1) + 1, C + 4 * K + 2, 0⟩ [fm]⊢* _; step fm
    rw [show C + K - 1 + 2 = C + K + 1 from by omega,
        show C + 4 * K + 2 + 1 = C + 4 * K + 3 from by ring]; finish
  -- r3_chain
  have h := r3_chain (C + K + 1) 1 (C + 4 * K + 3)
  rw [show 1 + 2 * (C + K + 1) = 2 * C + 2 * K + 3 from by ring,
      show C + 4 * K + 3 + 2 * (C + K + 1) = 3 * C + 6 * K + 5 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 11, 14, 0⟩) (by execute fm 27)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ 1 ∧ d ≥ c + 2 ∧ d ≤ 2 * c + 1)
  · intro q ⟨c, d, hq, hc, hd_lo, hd_hi⟩; subst hq
    rcases Nat.even_or_odd (d - c - 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- Even: d - c - 1 = 2K
      have hd_eq : d = c + 2 * K + 1 := by omega
      subst hd_eq
      have hK1 : K ≥ 1 := by omega
      have hCK : 2 * K ≤ c := by omega
      exact ⟨_, ⟨2 * c + 2 * K + 2, 3 * c + 6 * K + 2, rfl, by omega, by omega, by omega⟩,
             main_even c K hc hK1 hCK⟩
    · -- Odd: d - c - 1 = 2K + 1
      have hd_eq : d = c + 2 * K + 2 := by omega
      subst hd_eq
      have hCK : 2 * K + 1 ≤ c := by omega
      exact ⟨_, ⟨2 * c + 2 * K + 3, 3 * c + 6 * K + 5, rfl, by omega, by omega, by omega⟩,
             main_odd c K hc hCK⟩
  · exact ⟨11, 14, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_478
