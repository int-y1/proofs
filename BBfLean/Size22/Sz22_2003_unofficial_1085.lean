import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1085: [5/6, 2/35, 41503/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 1  0 -1 -1  0
-1  0  0  3  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1085

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 drain: move d to b
theorem r4_drain : ∀ k b d e,
    ⟨(0 : ℕ), b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; simp; exists 0
  | succ k ih =>
    intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3 chain: drain a, building d and e
theorem r3_chain : ∀ a d e,
    ⟨a, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * a, e + 2 * a⟩ := by
  intro a; induction a with
  | zero => intro d e; simp; exists 0
  | succ a ih =>
    intro d e
    step fm
    apply stepStar_trans (ih (d + 3) (e + 2))
    ring_nf; finish

-- Spiral: from (0, 2k+1, c, 0, e+k+1), reach (1, 0, c+k, 0, e)
theorem spiral : ∀ k c e,
    ⟨(0 : ℕ), 2 * k + 1, c, (0 : ℕ), e + k + 1⟩ [fm]⊢* ⟨1, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero =>
    intro c e
    step fm; step fm; step fm
    ring_nf; finish
  | succ k ih =>
    intro c e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm -- R5
    step fm -- R1
    step fm -- R2
    step fm -- R1
    show ⟨0, 2 * k + 1, c + 1, 0, e + k + 1⟩ [fm]⊢* ⟨1, 0, c + (k + 1), 0, e⟩
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (c + 1) e

-- General R2/R3 process: (a, 0, c, 3, e) →* (0, 0, 0, 3+3a+2c, e+2a+2c)
theorem general_process : ∀ c a e,
    ⟨a, (0 : ℕ), c, (3 : ℕ), e⟩ [fm]⊢* ⟨0, 0, 0, 3 + 3 * a + 2 * c, e + 2 * a + 2 * c⟩ := by
  intro c; induction' c using Nat.strongRecOn with c IH; intro a e
  match c with
  | 0 =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact r3_chain a 3 e
  | 1 =>
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show 3 + 3 * a + 2 * 1 = 2 + 3 * (a + 1) from by ring,
        show e + 2 * a + 2 * 1 = e + 2 * (a + 1) from by ring]
    exact r3_chain (a + 1) 2 e
  | 2 =>
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
        show (3 : ℕ) = 1 + 1 + 1 from by ring]
    step fm; step fm
    rw [show 3 + 3 * a + 2 * 2 = 1 + 3 * (a + 2) from by ring,
        show e + 2 * a + 2 * 2 = e + 2 * (a + 2) from by ring]
    exact r3_chain (a + 2) 1 e
  | 3 =>
    rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    show ⟨a + 3, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 3 + 3 * a + 2 * 3, e + 2 * a + 2 * 3⟩
    rw [show 3 + 3 * a + 2 * 3 = 0 + 3 * (a + 3) from by ring,
        show e + 2 * a + 2 * 3 = e + 2 * (a + 3) from by ring]
    exact r3_chain (a + 3) 0 e
  | (c' + 4) =>
    rw [show (c' : ℕ) + 4 = (c' + 1) + 1 + 1 + 1 from by ring,
        show (3 : ℕ) = 0 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm -- 3 R2 steps
    step fm -- R3
    show ⟨a + 2, 0, c' + 1, 3, e + 2⟩ [fm]⊢*
      ⟨0, 0, 0, 3 + 3 * a + 2 * (c' + 4), e + 2 * a + 2 * (c' + 4)⟩
    rw [show 3 + 3 * a + 2 * (c' + 4) = 3 + 3 * (a + 2) + 2 * (c' + 1) from by ring,
        show e + 2 * a + 2 * (c' + 4) = (e + 2) + 2 * (a + 2) + 2 * (c' + 1) from by ring]
    exact IH (c' + 1) (by omega) (a + 2) (e + 2)

-- Full transition: (0,0,0,2k+3,e) →⁺ (0,0,0,2k+5,e+k+2) when e ≥ k+2
theorem full_transition (k e : ℕ) (he : e ≥ k + 2) :
    ⟨(0 : ℕ), 0, 0, 2 * k + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 5, e + k + 2⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + k + 2 := ⟨e - k - 2, by omega⟩
  -- Phase 1: R4 drain (first step gives stepPlus)
  rw [show 2 * k + 3 = 0 + (2 * k + 3) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (2 * k + 3), e' + k + 2⟩ =
        some ⟨0, 1, 0, 0 + (2 * k + 3) - 1, e' + k + 2⟩
    simp [fm]
  rw [show 0 + (2 * k + 3) - 1 = (2 * k + 2) from by omega,
      show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * k + 2) 1 0 (e' + k + 2))
  rw [show 1 + (2 * k + 2) = 2 * (k + 1) + 1 from by ring]
  -- Phase 2: Spiral
  apply stepStar_trans (spiral (k + 1) 0 e')
  rw [show 0 + (k + 1) = k + 1 from by ring]
  -- Phase 3: R3 on (1, 0, k+1, 0, e')
  step fm
  -- Phase 4: General process
  show ⟨0, (0 : ℕ), k + 1, 3, e' + 2⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 5, e' + k + 2 + k + 2⟩
  rw [show 2 * k + 5 = 3 + 3 * 0 + 2 * (k + 1) from by ring,
      show e' + k + 2 + k + 2 = (e' + 2) + 2 * 0 + 2 * (k + 1) from by ring]
  exact general_process (k + 1) 0 (e' + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k e, q = ⟨0, 0, 0, 2 * k + 3, e⟩ ∧ e ≥ k + 2)
  · intro c ⟨k, e, hq, he⟩; subst hq
    exact ⟨⟨0, 0, 0, 2 * k + 5, e + k + 2⟩,
      ⟨k + 1, e + k + 2, rfl, by omega⟩,
      full_transition k e he⟩
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1085
