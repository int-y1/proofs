import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #418: [27/10, 22/21, 343/2, 5/11, 3/7]

Vector representation:
```
-1  3 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_418

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 loop: e → c
theorem r4_loop : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 loop: a → d
theorem r3_loop : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d + 3 * k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2+R1 loop: processes c and d in pairs
theorem r21_loop : ∀ k b d e,
    ⟨0, b + 1, k, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 1 + 2 * k, 0, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 2) d (e + 1))
    ring_nf; finish

-- R2 burst: b,d → a,e
theorem r2_burst : ∀ k a b d e,
    ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + k, b, (0 : ℕ), d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Mixing lemma: (A+1, B, 0, 0, F) ⊢* (0, 0, 0, 3A+3+2B, F+B)
theorem mixing : ∀ k a e,
    ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 3 * a + 3 + 2 * k, e + k⟩ := by
  intro k; induction k using Nat.strongRecOn with
  | _ k IH => match k with
    | 0 =>
      intro a e
      have h := r3_loop (a + 1) 0 0 e
      simp only [Nat.zero_add] at h
      rw [show 3 * a + 3 + 2 * 0 = 3 * (a + 1) from by ring,
          show e + 0 = e from Nat.add_zero e]; exact h
    | 1 =>
      intro a e
      apply stepStar_trans (c₂ := ⟨a + 1, 0, 0, 2, e + 1⟩)
      · rw [show a + 1 = a + 1 from rfl, show (1 : ℕ) = 0 + 1 from by ring]
        step fm
        rw [show (3 : ℕ) = 2 + 1 from by ring]
        step fm; finish
      have h := r3_loop (a + 1) 0 2 (e + 1)
      simp only [Nat.zero_add] at h
      rw [show 3 * a + 3 + 2 * 1 = 2 + 3 * (a + 1) from by ring,
          show e + 1 = e + 1 from rfl]
      exact h
    | 2 =>
      intro a e
      apply stepStar_trans (c₂ := ⟨a + 2, 0, 0, 1, e + 2⟩)
      · apply stepStar_trans (c₂ := ⟨a, 2, 0, 3, e⟩)
        · rw [show a + 1 = a + 1 from rfl, show (2 : ℕ) = 0 + 2 from by ring]
          step fm; finish
        have h1 := r2_burst 2 a 0 1 e
        simp only [Nat.zero_add] at h1; exact h1
      have h := r3_loop (a + 2) 0 1 (e + 2)
      simp only [Nat.zero_add] at h
      rw [show 3 * a + 3 + 2 * 2 = 1 + 3 * (a + 2) from by ring,
          show e + 2 = e + 2 from rfl]
      exact h
    | k + 3 =>
      intro a e
      apply stepStar_trans (c₂ := ⟨a + 3, k, 0, 0, e + 3⟩)
      · apply stepStar_trans (c₂ := ⟨a, k + 3, 0, 3, e⟩)
        · rw [show a + 1 = a + 1 from rfl, show k + 3 = 0 + (k + 3) from by ring]
          step fm; finish
        have h1 := r2_burst 3 a k 0 e
        simp only [Nat.zero_add] at h1; exact h1
      have h2 := IH k (by omega) (a + 2) (e + 3)
      rw [show 3 * a + 3 + 2 * (k + 3) = 3 * (a + 2) + 3 + 2 * k from by ring,
          show e + (k + 3) = e + 3 + k from by ring]
      exact h2

-- Main transition: (0, 0, 0, D+E+2, E) ⊢⁺ (0, 0, 0, D+4*E+3, 3*E+1)
theorem main_trans (D E : ℕ) :
    ⟨0, 0, 0, D + E + 2, E⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D + 4 * E + 3, 3 * E + 1⟩ := by
  -- Phase 1: R4 loop + R5 + R21 loop
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, E, D + E + 2, 0⟩)
  · have h := r4_loop E 0 (D + E + 2) 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, E, D + E + 1, 0⟩)
  · rw [show D + E + 2 = (D + E + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2 * E + 1, 0, D + 1, E⟩)
  · have h := r21_loop E 0 (D + 1) 0
    simp only [Nat.zero_add] at h
    rw [show D + E + 1 = (D + 1) + E from by ring,
        show 2 * E + 1 = 1 + 2 * E from by ring]; exact h
  -- Phase 2: R2 burst + mixing/R3, split on D vs 2E
  rcases (show D + 1 ≤ 2 * E + 1 ∨ D + 1 ≥ 2 * E + 2 from by omega) with h | h
  · -- Case D ≤ 2E: R2 burst of D+1, then mixing
    obtain ⟨G, hG⟩ : ∃ G, D + G = 2 * E := by exact ⟨2 * E - D, by omega⟩
    apply stepStar_trans (c₂ := ⟨D + 1, G, 0, 0, E + D + 1⟩)
    · have h2 := r2_burst (D + 1) 0 G 0 E
      simp only [Nat.zero_add] at h2
      rw [show G + (D + 1) = 2 * E + 1 from by omega] at h2; exact h2
    have h2 := mixing G D (E + D + 1)
    rw [show 3 * D + 3 + 2 * G = D + 4 * E + 3 from by omega,
        show E + D + 1 + G = 3 * E + 1 from by omega] at h2
    exact h2
  · -- Case D ≥ 2E+1: R2 burst of 2E+1, then R3 loop
    obtain ⟨G, hG⟩ : ∃ G, 2 * E + G + 1 = D := by exact ⟨D - (2 * E + 1), by omega⟩
    apply stepStar_trans (c₂ := ⟨2 * E + 1, 0, 0, G + 1, 3 * E + 1⟩)
    · have h2 := r2_burst (2 * E + 1) 0 0 (G + 1) E
      simp only [Nat.zero_add] at h2
      rw [show G + 1 + (2 * E + 1) = D + 1 from by omega,
          show E + (2 * E + 1) = 3 * E + 1 from by omega] at h2
      exact h2
    have h2 := r3_loop (2 * E + 1) 0 (G + 1) (3 * E + 1)
    simp only [Nat.zero_add] at h2
    rw [show G + 1 + 3 * (2 * E + 1) = D + 4 * E + 3 from by omega] at h2
    exact h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun c ↦ ∃ D E, c = ⟨0, 0, 0, D + E + 2, E⟩)
  · intro c ⟨D, E, hc⟩
    refine ⟨⟨0, 0, 0, D + 4 * E + 3, 3 * E + 1⟩,
           ⟨D + E, 3 * E + 1, ?_⟩, hc ▸ main_trans D E⟩
    show (0, 0, 0, D + 4 * E + 3, 3 * E + 1) = (0, 0, 0, D + E + (3 * E + 1) + 2, 3 * E + 1)
    congr 1; ring_nf
  · exact ⟨1, 0, rfl⟩

end Sz22_2003_unofficial_418
