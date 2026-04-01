import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1507: [7/15, 9/77, 50/7, 11/25, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1  0  2 -1  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1507

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 repeated (b=0, e=0): a+1, c+2, d-1 per step.
theorem r3_chain : ∀ k, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 2))
    ring_nf; finish

-- R4 repeated (b=0, d=0): c-2, e+1 per step.
theorem r4_chain : ∀ k, ⟨a, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

-- R5+R2 alternation: a-1, b+3, e-1 per pair.
theorem r5r2_drain : ∀ k, ⟨a + k, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 3))
    ring_nf; finish

-- R3+R1+R1 spiral: a+1, b-2, d+1 per round.
theorem spiral : ∀ k, ⟨a, b + 2 * k, 0, d + 1, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

-- R2 repeated (c=0): b+2, d-1, e-1 per step.
theorem r2_chain : ∀ k, ⟨a, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- Specialized R5R2 drain with e_param=0.
theorem r5r2_drain' (e : ℕ) : ⟨a + e, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + 3 * e, 0, 0, 0⟩ := by
  have h := r5r2_drain e (a := a) (b := b) (e := 0)
  rw [show 0 + e = e from by ring] at h; exact h

-- From (a+1, 0, 0, d+1, 0): R3 chain + R4 chain + R5R2 drain + R5+R3+R1x2.
theorem zeros_to_spiral_state :
    ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 1, 3 * d + 2, 0, 2, 0⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_trans (r3_chain (d + 1) (a := a + 1) (c := 0) (d := 0))
  rw [show a + 1 + (d + 1) = a + d + 2 from by ring,
      show 0 + 2 * (d + 1) = 0 + 2 * (d + 1) from rfl]
  apply stepStar_trans (r4_chain (d + 1) (a := a + d + 2) (c := 0) (e := 0))
  rw [show a + d + 2 = (a + 1) + (d + 1) from by ring,
      show 0 + (d + 1) = 0 + (d + 1) from rfl]
  apply stepStar_trans (r5r2_drain (d + 1) (a := a + 1) (b := 0) (e := 0))
  rw [show 0 + 3 * (d + 1) = 3 * d + 3 from by ring,
      show a + 1 = a + 1 from rfl]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Even b transition: (a, 2K+2, 0, 2, 0) ⊢⁺ (a+K+1, 3K+8, 0, 2, 0).
theorem even_spiral_trans (K : ℕ) :
    ⟨a, 2 * K + 2, 0, 2, 0⟩ [fm]⊢⁺ ⟨a + K + 1, 3 * K + 8, 0, 2, 0⟩ := by
  rw [show 2 * K + 2 = 2 + 2 * K from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact spiral K (a := a) (b := 2) (d := 1)
  rw [show 1 + K + 1 = K + 2 from by ring,
      show K + 2 = (K + 1) + 1 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show K + 3 = (K + 2) + 1 from by ring,
      show a + K + 1 = (a + K) + 1 from by ring]
  apply stepStar_trans (zeros_to_spiral_state (a := a + K) (d := K + 2))
  ring_nf; finish

-- Odd b transition: (a, 2K+1, 0, 2, 0) ⊢⁺ (a+2K+2, 0, 0, 2, K+2).
theorem odd_spiral_trans (K : ℕ) :
    ⟨a, 2 * K + 1, 0, 2, 0⟩ [fm]⊢⁺ ⟨a + 2 * K + 2, 0, 0, 2, K + 2⟩ := by
  rw [show 2 * K + 1 = 1 + 2 * K from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact spiral K (a := a) (b := 1) (d := 1)
  rw [show 1 + K + 1 = K + 2 from by ring,
      show K + 2 = (K + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  rw [show K + 2 = 0 + (K + 2) from by ring]
  apply stepStar_trans (r3_chain (K + 2) (a := a + K + 1) (c := 1) (d := 0))
  rw [show a + K + 1 + (K + 2) = a + 2 * K + 3 from by ring,
      show 1 + 2 * (K + 2) = 1 + 2 * (K + 2) from rfl]
  apply stepStar_trans (r4_chain (K + 2) (a := a + 2 * K + 3) (c := 1) (e := 0))
  rw [show a + 2 * K + 3 = (a + 2 * K + 2) + 1 from by ring,
      show 0 + (K + 2) = K + 2 from by ring]
  step fm; step fm
  ring_nf; finish

-- Drain for e ≥ 2: R2x2 + R5R2 drain + R5+R3+R1x2.
theorem drain_e_ge2_star (e : ℕ) :
    ⟨F + e + 1, 0, 0, 2, e + 2⟩ [fm]⊢* ⟨F + 1, 3 * e + 3, 0, 2, 0⟩ := by
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2_chain 2 (a := F + e + 1) (b := 0) (d := 0) (e := e))
  rw [show 0 + 2 * 2 = 4 from by ring,
      show F + e + 1 = (F + 1) + e from by ring]
  apply stepStar_trans (r5r2_drain' e (a := F + 1) (b := 4))
  rw [show 4 + 3 * e = 3 * e + 4 from by ring,
      show 0 + 2 = 2 from by ring]
  step fm; step fm; step fm; step fm
  ring_nf; finish

theorem drain_e_ge2 (e : ℕ) :
    ⟨F + e + 1, 0, 0, 2, e + 2⟩ [fm]⊢⁺ ⟨F + 1, 3 * e + 3, 0, 2, 0⟩ :=
  stepStar_stepPlus (drain_e_ge2_star e) (by simp [Q])

-- Drain for e = 1.
theorem drain_e1 : ⟨a + 2, 0, 0, 2, 1⟩ [fm]⊢⁺ ⟨a + 3, 5, 0, 2, 0⟩ := by
  execute fm 16

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 2, 4⟩)
  · execute fm 41
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦
      (∃ a b, q = ⟨a, b, 0, 2, 0⟩ ∧ a ≥ 1 ∧ b ≥ 1) ∨
      (∃ a e, q = ⟨a, 0, 0, 2, e⟩ ∧ e ≥ 1 ∧ a ≥ e + 1))
  · intro q hP
    rcases hP with ⟨a, b, rfl, ha, hb⟩ | ⟨a, e, rfl, he, hae⟩
    · -- (a, b, 0, 2, 0) with a ≥ 1, b ≥ 1.
      rcases Nat.even_or_odd b with ⟨K, hK⟩ | ⟨K, hK⟩
      · -- b even: b = 2K, K ≥ 1.
        rw [show K + K = 2 * K from by ring] at hK; subst hK
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        refine ⟨⟨a + K' + 1, 3 * K' + 8, 0, 2, 0⟩,
          Or.inl ⟨a + K' + 1, 3 * K' + 8, rfl, by omega, by omega⟩, ?_⟩
        rw [show 2 * (K' + 1) = 2 * K' + 2 from by ring]
        exact even_spiral_trans K'
      · -- b odd: b = 2K+1.
        subst hK
        refine ⟨⟨a + 2 * K + 2, 0, 0, 2, K + 2⟩,
          Or.inr ⟨a + 2 * K + 2, K + 2, rfl, by omega, by omega⟩, ?_⟩
        exact odd_spiral_trans K
    · -- (a, 0, 0, 2, e) with e ≥ 1, a ≥ e+1.
      rcases (show e = 1 ∨ e ≥ 2 from by omega) with rfl | he2
      · -- e = 1, a ≥ 2.
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
        refine ⟨⟨a' + 3, 5, 0, 2, 0⟩,
          Or.inl ⟨a' + 3, 5, rfl, by omega, by omega⟩, ?_⟩
        exact drain_e1
      · -- e ≥ 2.
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
        obtain ⟨F, rfl⟩ : ∃ F, a = F + e' + 1 := ⟨a - e' - 1, by omega⟩
        refine ⟨⟨F + 1, 3 * e' + 3, 0, 2, 0⟩, ?_, drain_e_ge2 e' (F := F)⟩
        exact Or.inl ⟨F + 1, 3 * e' + 3, rfl, by omega, by omega⟩
  · exact Or.inr ⟨8, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1507
