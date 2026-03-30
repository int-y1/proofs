import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #835: [35/6, 9/55, 8/5, 11/7, 35/2]

Vector representation:
```
-1 -1  1  1  0
 0  2 -1  0 -1
 3  0 -1  0  0
 0  0  0 -1  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_835

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ a d, ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 3) d); ring_nf; finish

theorem r2_drain : ∀ k, ∀ b c d, ⟨0, b, c + k, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 2) c d); ring_nf; finish

theorem r1_chain : ∀ k, ∀ a b c d e, ⟨a + k, b + k, c, d, e⟩ [fm]⊢* ⟨a, b, c + k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a b (c + 1) (d + 1) e); ring_nf; finish

theorem gen_interleave : ∀ B, ∀ C D, ⟨3, B, C, D, 0⟩ [fm]⊢* ⟨3 + 2 * B + 3 * C, 0, 0, D + B, 0⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D
  rcases B with _ | _ | _ | B
  · show ⟨3, 0, C, D, 0⟩ [fm]⊢* ⟨3 + 3 * C, 0, 0, D, 0⟩
    exact r3_drain C 3 D
  · show ⟨3, 1, C, D, 0⟩ [fm]⊢* ⟨5 + 3 * C, 0, 0, D + 1, 0⟩
    step fm -- R1: (2, 0, C+1, D+1, 0)
    rw [show 5 + 3 * C = 2 + 3 * (C + 1) from by ring]
    exact r3_drain (C + 1) 2 (D + 1)
  · show ⟨3, 2, C, D, 0⟩ [fm]⊢* ⟨7 + 3 * C, 0, 0, D + 2, 0⟩
    step fm -- R1: (2, 1, C+1, D+1, 0)
    step fm -- R1: (1, 0, C+2, D+2, 0)
    rw [show 7 + 3 * C = 1 + 3 * (C + 2) from by ring]
    exact r3_drain (C + 2) 1 (D + 2)
  · show ⟨3, B + 1 + 1 + 1, C, D, 0⟩ [fm]⊢*
      ⟨3 + 2 * (B + 1 + 1 + 1) + 3 * C, 0, 0, D + (B + 1 + 1 + 1), 0⟩
    step fm -- R1: (2, B+2, C+1, D+1, 0)
    step fm -- R1: (1, B+1, C+2, D+2, 0)
    step fm -- R1: (0, B, C+3, D+3, 0)
    rw [show C + 3 = C + 2 + 1 from by ring]
    step fm -- R3: (3, B, C+2, D+3, 0)
    rw [show 3 + 2 * (B + 1 + 1 + 1) + 3 * C = 3 + 2 * B + 3 * (C + 2) from by ring,
        show D + (B + 1 + 1 + 1) = D + 3 + B from by ring]
    exact ih B (by omega) (C + 2) (D + 3)

theorem process : ∀ E, ∀ A C D, C ≥ 1 → A + C ≥ E + 2 →
    ⟨A, 0, C, D, E⟩ [fm]⊢* ⟨A + 3 * C + E, 0, 0, D + 2 * E, 0⟩ := by
  intro E; induction' E with E ih <;> intro A C D hC hAC
  · show ⟨A, 0, C, D, 0⟩ [fm]⊢* ⟨A + 3 * C, 0, 0, D, 0⟩
    exact r3_drain C A D
  · rcases (show A ≥ 2 ∨ A = 1 ∨ A = 0 from by omega) with hA2 | rfl | rfl
    · -- A >= 2
      obtain ⟨c', rfl⟩ : ∃ c', C = c' + 1 := ⟨C - 1, by omega⟩
      obtain ⟨a', rfl⟩ : ∃ a', A = a' + 2 := ⟨A - 2, by omega⟩
      step fm -- R2: (a'+2, 2, c', D, E)
      step fm -- R1: (a'+1, 1, c'+1, D+1, E)
      step fm -- R1: (a', 0, c'+2, D+2, E)
      rw [show a' + 2 + 3 * (c' + 1) + (E + 1) = a' + 3 * (c' + 2) + E from by ring,
          show D + 2 * (E + 1) = D + 2 + 2 * E from by ring]
      exact ih a' (c' + 2) (D + 2) (by omega) (by omega)
    · -- A = 1
      obtain ⟨c', rfl⟩ : ∃ c', C = c' + 1 := ⟨C - 1, by omega⟩
      step fm -- R2: (1, 2, c', D, E)
      step fm -- R1: (0, 1, c'+1, D+1, E)
      rcases E with _ | E
      · -- E = 0
        rw [show 1 + 3 * (c' + 1) + (0 + 1) = 5 + 3 * c' from by ring,
            show D + 2 * (0 + 1) = D + 2 from by ring]
        step fm; step fm
        rw [show 5 + 3 * c' = 2 + 3 * (c' + 1) from by ring]
        exact r3_drain (c' + 1) 2 (D + 2)
      · -- E + 1
        show ⟨0, 1, c' + 1, D + 1, E + 1⟩ [fm]⊢*
          ⟨1 + 3 * (c' + 1) + (E + 2), 0, 0, D + 2 * (E + 2), 0⟩
        -- R2 drain (E+1) times
        have h_drain : ⟨0, 1, c' + 1, D + 1, E + 1⟩ [fm]⊢*
            ⟨0, 1 + 2 * (E + 1), c' - E, D + 1, 0⟩ := by
          rw [show c' + 1 = (c' - E) + (E + 1) from by omega]
          exact r2_drain (E + 1) 1 (c' - E) (D + 1)
        apply stepStar_trans h_drain
        rw [show c' - E = (c' - E - 1) + 1 from by omega]
        step fm -- R3: (3, 1+2*(E+1), c'-E-1, D+1, 0)
        rw [show 1 + 3 * (c' + 1) + (E + 2) = 3 + 2 * (1 + 2 * (E + 1)) + 3 * (c' - E - 1)
              from by omega,
            show D + 2 * (E + 2) = D + 1 + (1 + 2 * (E + 1)) from by omega]
        exact gen_interleave (1 + 2 * (E + 1)) (c' - E - 1) (D + 1)
    · -- A = 0
      obtain ⟨c', rfl⟩ : ∃ c', C = c' + 1 := ⟨C - 1, by omega⟩
      -- R2 drain (E+1) times
      have h_drain : ⟨0, 0, c' + 1, D, E + 1⟩ [fm]⊢*
          ⟨0, 2 * (E + 1), c' - E, D, 0⟩ := by
        rw [show c' + 1 = (c' - E) + (E + 1) from by omega,
            show 2 * (E + 1) = 0 + 2 * (E + 1) from by ring]
        exact r2_drain (E + 1) 0 (c' - E) D
      apply stepStar_trans h_drain
      rw [show c' - E = (c' - E - 1) + 1 from by omega]
      step fm -- R3: (3, 2*(E+1), c'-E-1, D, 0)
      rw [show 0 + 3 * (c' + 1) + (E + 1) = 3 + 2 * (2 * (E + 1)) + 3 * (c' - E - 1)
            from by omega,
          show D + 2 * (E + 1) = D + 2 * (E + 1) from rfl]
      exact gen_interleave (2 * (E + 1)) (c' - E - 1) D

theorem main_trans : ∀ D a, D ≥ 1 → a ≥ D + 2 →
    ⟨a, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨a + D + 2, 0, 0, 2 * D + 1, 0⟩ := by
  intro D a hD ha
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have h1 : ⟨a' + 1, 0, 0, D, 0⟩ [fm]⊢* ⟨a' + 1, 0, 0, 0, D⟩ := by
    rw [show D = 0 + D from by ring]; exact d_to_e D (a' + 1) 0 0
  have h2 : ⟨a' + 1, 0, 0, 0, D⟩ [fm]⊢ ⟨a', 0, 1, 1, D⟩ := by simp [fm]
  have h3 := process D a' 1 1 (by omega) (by omega)
  apply stepStar_stepPlus_stepPlus h1
  apply step_stepStar_stepPlus h2
  show ⟨a', 0, 1, 1, D⟩ [fm]⊢* ⟨a' + 1 + D + 2, 0, 0, 2 * D + 1, 0⟩
  rw [show a' + 1 + D + 2 = a' + 3 * 1 + D from by ring,
      show 2 * D + 1 = 1 + 2 * D from by ring]
  exact h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a D, q = ⟨a, 0, 0, D, 0⟩ ∧ D ≥ 1 ∧ a ≥ D + 2)
  · intro c ⟨a, D, hq, hD, ha⟩; subst hq
    exact ⟨⟨a + D + 2, 0, 0, 2 * D + 1, 0⟩,
      ⟨a + D + 2, 2 * D + 1, rfl, by omega, by omega⟩,
      main_trans D a hD ha⟩
  · exact ⟨3, 1, rfl, by omega, by omega⟩
