import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #100: [7/15, 22/3, 27/77, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  3  0 -1 -1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_100

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ∀ k : ℕ, ∀ a c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3+R2×3 chain: (A, 0, 0, k, E+1) →* (A+3k, 0, 0, 0, E+1+2k)
theorem r3r2_chain : ∀ k : ℕ, ∀ A E, ⟨A, 0, 0, k, E+1⟩ [fm]⊢* ⟨A+3*k, 0, 0, 0, E+1+2*k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase B round: 6 steps, c decreases by 4, d increases by 3, A decreases by 1
theorem phase_b_round : ∀ a c d : ℕ,
    ⟨a+c+5, 0, c+4, d, 0⟩ [fm]⊢⁺ ⟨a+c+4, 0, c, d+3, 0⟩ := by
  intro a c d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Phase BD: strong induction on c.
-- From ⟨a+c+1, 0, c, d, 0⟩ reach ⟨a+3*c+3*d+1, 0, 0, 0, e'⟩
-- with c+2*d+2 ≤ e' ≤ 2*c+2*d+2.
theorem phase_bd : ∀ c : ℕ, ∀ a d,
    ∃ e', ⟨a+c+1, 0, c, d, 0⟩ [fm]⊢⁺ ⟨a+3*c+3*d+1, 0, 0, 0, e'⟩
      ∧ e' ≥ c + 2*d + 2 ∧ e' ≤ 2*c + 2*d + 2 := by
  intro c; induction' c using Nat.strongRecOn with c ih
  rcases c with _ | _ | _ | _ | c
  · -- c = 0: e' = 2+2d
    intro a d
    refine ⟨2 + 2*d, ?_, by omega, by omega⟩
    step fm; step fm
    apply stepStar_trans (r3r2_chain d _ _)
    ring_nf; finish
  · -- c = 1: e' = 3+2d
    intro a d
    refine ⟨3 + 2*d, ?_, by omega, by omega⟩
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (r3r2_chain d _ _)
    ring_nf; finish
  · -- c = 2: e' = 4+2d
    intro a d
    refine ⟨4 + 2*d, ?_, by omega, by omega⟩
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (r3r2_chain (d+1) _ _)
    ring_nf; finish
  · -- c = 3: e' = 5+2d
    intro a d
    refine ⟨5 + 2*d, ?_, by omega, by omega⟩
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (r3r2_chain (d+2) _ _)
    ring_nf; finish
  · -- c + 4: use IH with c, d+3
    intro a d
    have ih_c := ih c (by omega) (a+3) (d+3)
    obtain ⟨e', he', hlo, hhi⟩ := ih_c
    refine ⟨e', ?_, by omega, by omega⟩
    apply stepPlus_trans
    · have hb := phase_b_round a c d
      convert hb using 2
    · convert he' using 2; first | ring_nf

-- Full transition from canonical form
-- ⟨a+e+1, 0, 0, 0, e⟩ →⁺ ⟨a+3*e+1, 0, 0, 0, e'⟩
-- with e+2 ≤ e' ≤ 2*e+2
theorem full_trans : ∀ e : ℕ, ∀ a,
    ∃ e', ⟨a+e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+3*e+1, 0, 0, 0, e'⟩
      ∧ e' ≥ e + 2 ∧ e' ≤ 2*e + 2 := by
  intro e a
  obtain ⟨e', he', hlo, hhi⟩ := phase_bd e a 0
  refine ⟨e', ?_, by omega, by omega⟩
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_c e (a+e+1) 0 0
    simp only [Nat.zero_add] at h
    exact h
  · convert he' using 2

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1,0,0,0,0) reaches (5,0,0,0,4) in 14 steps.
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 4⟩) (by execute fm 14)
  -- Invariant: (A, 0, 0, 0, e) with A ≥ e+1 and e ≥ 4.
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A e, q = ⟨A, 0, 0, 0, e⟩ ∧ A ≥ e + 1 ∧ e ≥ 4)
  · intro c ⟨A, e, hq, hA, he⟩; subst hq
    -- Decompose A = a + e + 1 where a = A - e - 1.
    obtain ⟨a, rfl⟩ : ∃ a, A = a + e + 1 := ⟨A - e - 1, by omega⟩
    obtain ⟨e', h1, hlo, hhi⟩ := full_trans e a
    refine ⟨⟨a + 3*e + 1, 0, 0, 0, e'⟩, ⟨a + 3*e + 1, e', rfl, ?_, ?_⟩, h1⟩
    · omega  -- a+3e+1 ≥ e'+1, since a+3e+1 ≥ 3e+1 ≥ 2e+3 ≥ e'+1 (for e ≥ 2)
    · omega  -- e' ≥ 4, since e' ≥ e+2 ≥ 6
  · exact ⟨5, 4, rfl, by omega, by omega⟩

end Sz21_140_unofficial_100
