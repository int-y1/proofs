import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1260: [5/6, 8/105, 847/2, 3/11, 5/3]

Vector representation:
```
-1 -1  1  0  0
 3 -1 -1 -1  0
-1  0  0  1  2
 0  1  0  0 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1260

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b (requires a=0, c=0)
theorem e_to_b : ∀ k, ∀ b d, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R3 repeated: drain a, gaining d and e (requires b=0)
theorem a_drain : ∀ k, ∀ c d e, ⟨k, (0 : ℕ), c, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) (e + 2))
    ring_nf; finish

-- R1 repeated: drain a and b equally, producing c (requires e=0)
theorem r1_chain : ∀ k, ∀ b c d, ⟨k, b + k, c, d, (0 : ℕ)⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- R2+R1x3 chain: each round consumes 4 from b and 1 from d, adds 2 to c
theorem r2r1x3_chain : ∀ k, ∀ b c d, ⟨(0 : ℕ), b + 4 * k, c + 1, d + k + 1, (0 : ℕ)⟩ [fm]⊢*
    ⟨0, b, c + 2 * k + 1, d + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring,
        show c + 2 * (k + 1) + 1 = (c + 2) + 2 * k + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) d)
    ring_nf; finish

-- c-drain: R4+R2+R3x3 repeated, each round consuming 1 from c
theorem c_drain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e + 1⟩ [fm]⊢*
    ⟨0, 0, c, d + 2 * k + 1, e + 5 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 * (k + 1) + 1 = (d + 2) + 2 * k + 1 from by ring,
        show e + 5 * (k + 1) + 1 = (e + 5) + 5 * k + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih c (d + 2) (e + 5))
    ring_nf; finish

-- Odd transition: (0,0,0,2m+1,4m+2) ->+ (0,0,0,5m+3,10m+6)
theorem transition_odd (m : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, 4 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * m + 3, 10 * m + 6⟩ := by
  -- Phase 1: e_to_b
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m + 1, 4 * m + 2⟩ [fm]⊢*
      ⟨0, 4 * m + 2, 0, 2 * m + 1, 0⟩ := by
    have := e_to_b (4 * m + 2) 0 (2 * m + 1)
    convert this using 2; ring_nf
  -- Phase 2: R5
  have h2 : ⟨(0 : ℕ), 4 * m + 2, 0, 2 * m + 1, 0⟩ [fm]⊢⁺
      ⟨0, 4 * m + 1, 1, 2 * m + 1, 0⟩ := by
    step fm; finish
  -- Phase 3: r2r1x3_chain m rounds
  have h3 : ⟨(0 : ℕ), 4 * m + 1, 1, 2 * m + 1, 0⟩ [fm]⊢*
      ⟨0, 1, 2 * m + 1, m + 1, 0⟩ := by
    have := r2r1x3_chain m 1 0 m
    convert this using 2; ring_nf
  -- Phase 4: R2 -> (3, 0, 2m, m, 0)
  have h4 : ⟨(0 : ℕ), 1, 2 * m + 1, m + 1, 0⟩ [fm]⊢
      ⟨3, 0, 2 * m, m, 0⟩ := by
    simp [fm]
  -- Phase 5: a_drain 3
  have h5 : ⟨(3 : ℕ), 0, 2 * m, m, 0⟩ [fm]⊢*
      ⟨0, 0, 2 * m, m + 3, 6⟩ := by
    have := a_drain 3 (2 * m) m 0
    convert this using 2
  -- Phase 6: c_drain 2m rounds
  have h6 : ⟨(0 : ℕ), 0, 2 * m, m + 3, 6⟩ [fm]⊢*
      ⟨0, 0, 0, 5 * m + 3, 10 * m + 6⟩ := by
    have := c_drain (2 * m) 0 (m + 2) 5
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans (step_stepStar h4)
          (stepStar_trans h5 h6))))

-- Even transition: (0,0,0,2m+2,4m+4) ->+ (0,0,0,5m+6,10m+12)
theorem transition_even (m : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 2, 4 * m + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * m + 6, 10 * m + 12⟩ := by
  -- Phase 1: e_to_b
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m + 2, 4 * m + 4⟩ [fm]⊢*
      ⟨0, 4 * m + 4, 0, 2 * m + 2, 0⟩ := by
    have := e_to_b (4 * m + 4) 0 (2 * m + 2)
    convert this using 2; ring_nf
  -- Phase 2: R5
  have h2 : ⟨(0 : ℕ), 4 * m + 4, 0, 2 * m + 2, 0⟩ [fm]⊢⁺
      ⟨0, 4 * m + 3, 1, 2 * m + 2, 0⟩ := by
    step fm; finish
  -- Phase 3: r2r1x3_chain m rounds
  have h3 : ⟨(0 : ℕ), 4 * m + 3, 1, 2 * m + 2, 0⟩ [fm]⊢*
      ⟨0, 3, 2 * m + 1, m + 2, 0⟩ := by
    have := r2r1x3_chain m 3 0 (m + 1)
    convert this using 2; ring_nf
  -- Phase 4-6: R2 + R1x2 + R3 (4 explicit steps)
  -- (0, 3, 2m+1, m+2, 0) -> (3, 2, 2m, m+1, 0) -> (2, 1, 2m+1, m+1, 0)
  -- -> (1, 0, 2m+2, m+1, 0) -> (0, 0, 2m+2, m+2, 2)
  have h4 : ⟨(0 : ℕ), 3, 2 * m + 1, m + 2, 0⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 2, m + 2, 2⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show 2 * m + 1 = (2 * m) + 1 from by ring,
        show m + 2 = (m + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm; ring_nf; finish
  -- Phase 7: c_drain (2m+2) rounds
  have h5 : ⟨(0 : ℕ), 0, 2 * m + 2, m + 2, 2⟩ [fm]⊢*
      ⟨0, 0, 0, 5 * m + 6, 10 * m + 12⟩ := by
    have := c_drain (2 * m + 2) 0 (m + 1) 1
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, d ≥ 1 ∧ q = ⟨0, 0, 0, d, 2 * d⟩)
  · intro q ⟨d, hd, hq⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm
      subst hm
      rcases m with _ | m
      · omega
      · refine ⟨⟨0, 0, 0, 5 * m + 6, 2 * (5 * m + 6)⟩, ⟨5 * m + 6, by omega, rfl⟩, ?_⟩
        have := transition_even m
        convert this using 2; ring_nf
    · subst hm
      refine ⟨⟨0, 0, 0, 5 * m + 3, 2 * (5 * m + 3)⟩, ⟨5 * m + 3, by omega, rfl⟩, ?_⟩
      have := transition_odd m
      convert this using 2; ring_nf
  · exact ⟨1, by omega, rfl⟩

end Sz22_2003_unofficial_1260
