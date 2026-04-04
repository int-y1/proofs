import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1724: [8/15, 3/14, 55/2, 7/5, 10/11]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1724

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a (c + 1) (e + 1))
  rw [show c + 1 + k = c + (k + 1) from by ring,
      show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r4_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]; step fm
  apply stepStar_trans (ih (d + 1) e)
  rw [show d + 1 + k = d + (k + 1) from by ring]; finish

theorem d_drain_round_0 : ∀ D E, ⟨0, 0, 0, D + 4, E + 1⟩ [fm]⊢* ⟨0, 3, 0, D, E⟩ := by
  intro D E
  step fm
  rw [show D + 4 = (D + 3) + 1 from by ring]
  step fm; step fm
  rw [show D + 3 = (D + 2) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show D + 2 = (D + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show D + 1 = D + 1 from rfl]; step fm; finish

theorem d_drain_round_pos : ∀ B D E,
    ⟨0, B + 1, 0, D + 4, E + 1⟩ [fm]⊢* ⟨0, B + 4, 0, D, E⟩ := by
  intro B D E
  step fm
  rw [show B + 1 = B + 1 from rfl]; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring, show D + 4 = (D + 3) + 1 from by ring]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring, show D + 3 = (D + 2) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show D + 2 = (D + 1) + 1 from by ring]
  step fm
  rw [show D + 1 = D + 1 from rfl]; step fm; finish

theorem d_drain_loop : ∀ k, ∀ B D E,
    ⟨0, B + 1, 0, D + 4 * k, E + k⟩ [fm]⊢* ⟨0, B + 3 * k + 1, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · simp; exists 0
  rw [show D + 4 * (k + 1) = (D + 4 * k) + 4 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (d_drain_round_pos B (D + 4 * k) (E + k))
  rw [show B + 4 = (B + 3) + 1 from by ring]
  apply stepStar_trans (ih (B + 3) D E)
  rw [show B + 3 + 3 * k + 1 = B + 3 * (k + 1) + 1 from by ring]; finish

theorem r3r1_chain : ∀ k, ∀ a e,
    ⟨a + 2, k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 4, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; finish
  rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
  step fm
  rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
  step fm
  rw [show a + 4 = (a + 2) + 2 from by ring]
  apply stepStar_trans (ih (a + 2) (e + 1))
  rw [show a + 2 + 2 * k + 4 = a + 2 * (k + 1) + 4 from by ring,
      show e + 1 + k + 1 = e + (k + 1) + 1 from by ring]; finish

theorem exit_r1 : ∀ B F, ⟨0, B + 1, 0, 1, F + 1⟩ [fm]⊢* ⟨2 * B + 5, 0, 0, 0, F + B + 1⟩ := by
  intro B F
  step fm
  rw [show B + 1 = B + 1 from rfl]; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring]; step fm
  rw [show (3 : ℕ) = 1 + 2 from by ring, show B + 1 = B + 1 from rfl]
  apply stepStar_trans (r3r1_chain B 1 F)
  rw [show 1 + 2 * B + 4 = 2 * B + 5 from by ring]; finish

theorem exit_r2 : ∀ B F, ⟨0, B + 1, 0, 2, F + 1⟩ [fm]⊢* ⟨2 * B + 6, 0, 0, 0, F + B + 2⟩ := by
  intro B F
  step fm
  rw [show B + 1 = B + 1 from rfl]; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]; step fm
  rw [show B + 2 = (B + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]; step fm
  rw [show B + 1 = B + 1 from rfl]; step fm
  rw [show (4 : ℕ) = 2 + 2 from by ring, show B + 1 = B + 1 from rfl]
  apply stepStar_trans (r3r1_chain B 2 (F + 1))
  rw [show 2 + 2 * B + 4 = 2 * B + 6 from by ring,
      show F + 1 + B + 1 = F + B + 2 from by ring]; finish

theorem exit_r3 : ∀ B F, ⟨0, B + 1, 0, 3, F + 1⟩ [fm]⊢* ⟨2 * B + 7, 0, 0, 0, F + B + 3⟩ := by
  intro B F
  step fm
  rw [show B + 1 = B + 1 from rfl]; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
  step fm
  rw [show B + 3 = (B + 2) + 1 from by ring]; step fm
  rw [show (3 : ℕ) = 1 + 2 from by ring, show B + 2 = (B + 1) + 1 from by ring]
  apply stepStar_trans (r3r1_chain (B + 1) 1 (F + 1))
  rw [show 1 + 2 * (B + 1) + 4 = 2 * B + 7 from by ring,
      show F + 1 + (B + 1) + 1 = F + B + 3 from by ring]; finish

theorem exit_r0 : ∀ B F, ⟨0, B + 2, 0, 0, F + 1⟩ [fm]⊢* ⟨2 * B + 6, 0, 0, 0, F + B + 1⟩ := by
  intro B F
  step fm
  rw [show B + 2 = (B + 1) + 1 from by ring]; step fm
  rw [show (4 : ℕ) = 2 + 2 from by ring, show B + 1 = B + 1 from rfl]
  apply stepStar_trans (r3r1_chain B 2 F)
  rw [show 2 + 2 * B + 4 = 2 * B + 6 from by ring]; finish

theorem phases12 (D : ℕ) (E : ℕ) :
    ⟨D + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 1, E + D + 1⟩ := by
  apply step_stepStar_stepPlus
  · show (⟨D + 1, 0, 0, 0, E⟩ : Q) [fm]⊢ ⟨D, 0, 1, 0, E + 1⟩; simp [fm]
  have h1 := r3_chain D 0 1 (E + 1)
  simp at h1
  have h2 := r4_chain (D + 1) 0 (E + D + 1)
  simp at h2
  apply stepStar_trans h1
  rw [show 1 + D = D + 1 from by ring,
      show E + 1 + D = E + D + 1 from by ring]
  exact h2

theorem trans_mod1 (M E : ℕ) :
    ⟨4 * M + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨6 * M + 3, 0, 0, 0, E + 6 * M⟩ := by
  rcases M with _ | M
  · simp; execute fm 5
  · have p12 : ⟨4 * (M + 1) + 1, 0, 0, 0, E⟩ [fm]⊢⁺
        ⟨0, 0, 0, 4 * M + 5, E + 4 * M + 5⟩ := by
      rw [show 4 * (M + 1) + 1 = (4 * M + 4) + 1 from by ring,
          show E + 4 * M + 5 = E + (4 * M + 4) + 1 from by ring]
      exact phases12 (4 * M + 4) E
    have p3 : ⟨(0 : ℕ), 0, 0, 4 * M + 5, E + 4 * M + 5⟩ [fm]⊢*
        ⟨0, 3, 0, 4 * M + 1, E + 4 * M + 4⟩ := by
      rw [show 4 * M + 5 = (4 * M + 1) + 4 from by ring,
          show E + 4 * M + 5 = (E + 4 * M + 4) + 1 from by ring]
      exact d_drain_round_0 (4 * M + 1) (E + 4 * M + 4)
    have p4 : ⟨(0 : ℕ), 3, 0, 4 * M + 1, E + 4 * M + 4⟩ [fm]⊢*
        ⟨0, 3 * M + 3, 0, 1, E + 3 * M + 4⟩ := by
      have h := d_drain_loop M 2 1 (E + 3 * M + 4)
      convert h using 2; all_goals ring_nf
    have p5 : ⟨(0 : ℕ), 3 * M + 3, 0, 1, E + 3 * M + 4⟩ [fm]⊢*
        ⟨6 * M + 9, 0, 0, 0, E + 6 * M + 6⟩ := by
      rw [show 3 * M + 3 = (3 * M + 2) + 1 from by ring,
          show E + 3 * M + 4 = (E + 3 * M + 3) + 1 from by ring]
      have h := exit_r1 (3 * M + 2) (E + 3 * M + 3)
      rw [show 2 * (3 * M + 2) + 5 = 6 * M + 9 from by ring,
          show E + 3 * M + 3 + (3 * M + 2) + 1 = E + 6 * M + 6 from by ring] at h
      exact h
    rw [show 6 * (M + 1) + 3 = 6 * M + 9 from by ring,
        show E + 6 * (M + 1) = E + 6 * M + 6 from by ring]
    exact stepPlus_stepStar_stepPlus p12
      (stepStar_trans p3 (stepStar_trans p4 p5))

theorem trans_mod2 (M E : ℕ) :
    ⟨4 * M + 2, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨6 * M + 4, 0, 0, 0, E + 6 * M + 2⟩ := by
  rcases M with _ | M
  · simp; execute fm 10
  · have p12 : ⟨4 * (M + 1) + 2, 0, 0, 0, E⟩ [fm]⊢⁺
        ⟨0, 0, 0, 4 * M + 6, E + 4 * M + 6⟩ := by
      rw [show 4 * (M + 1) + 2 = (4 * M + 5) + 1 from by ring,
          show E + 4 * M + 6 = E + (4 * M + 5) + 1 from by ring]
      exact phases12 (4 * M + 5) E
    have p3 : ⟨(0 : ℕ), 0, 0, 4 * M + 6, E + 4 * M + 6⟩ [fm]⊢*
        ⟨0, 3, 0, 4 * M + 2, E + 4 * M + 5⟩ := by
      rw [show 4 * M + 6 = (4 * M + 2) + 4 from by ring,
          show E + 4 * M + 6 = (E + 4 * M + 5) + 1 from by ring]
      exact d_drain_round_0 (4 * M + 2) (E + 4 * M + 5)
    have p4 : ⟨(0 : ℕ), 3, 0, 4 * M + 2, E + 4 * M + 5⟩ [fm]⊢*
        ⟨0, 3 * M + 3, 0, 2, E + 3 * M + 5⟩ := by
      have h := d_drain_loop M 2 2 (E + 3 * M + 5)
      convert h using 2; all_goals ring_nf
    have p5 : ⟨(0 : ℕ), 3 * M + 3, 0, 2, E + 3 * M + 5⟩ [fm]⊢*
        ⟨6 * M + 10, 0, 0, 0, E + 6 * M + 8⟩ := by
      rw [show 3 * M + 3 = (3 * M + 2) + 1 from by ring,
          show E + 3 * M + 5 = (E + 3 * M + 4) + 1 from by ring]
      have h := exit_r2 (3 * M + 2) (E + 3 * M + 4)
      rw [show 2 * (3 * M + 2) + 6 = 6 * M + 10 from by ring,
          show E + 3 * M + 4 + (3 * M + 2) + 2 = E + 6 * M + 8 from by ring] at h
      exact h
    rw [show 6 * (M + 1) + 4 = 6 * M + 10 from by ring,
        show E + 6 * (M + 1) + 2 = E + 6 * M + 8 from by ring]
    exact stepPlus_stepStar_stepPlus p12
      (stepStar_trans p3 (stepStar_trans p4 p5))

theorem trans_mod3 (M E : ℕ) :
    ⟨4 * M + 3, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨6 * M + 5, 0, 0, 0, E + 6 * M + 4⟩ := by
  rcases M with _ | M
  · simp; execute fm 15
  · have p12 : ⟨4 * (M + 1) + 3, 0, 0, 0, E⟩ [fm]⊢⁺
        ⟨0, 0, 0, 4 * M + 7, E + 4 * M + 7⟩ := by
      rw [show 4 * (M + 1) + 3 = (4 * M + 6) + 1 from by ring,
          show E + 4 * M + 7 = E + (4 * M + 6) + 1 from by ring]
      exact phases12 (4 * M + 6) E
    have p3 : ⟨(0 : ℕ), 0, 0, 4 * M + 7, E + 4 * M + 7⟩ [fm]⊢*
        ⟨0, 3, 0, 4 * M + 3, E + 4 * M + 6⟩ := by
      rw [show 4 * M + 7 = (4 * M + 3) + 4 from by ring,
          show E + 4 * M + 7 = (E + 4 * M + 6) + 1 from by ring]
      exact d_drain_round_0 (4 * M + 3) (E + 4 * M + 6)
    have p4 : ⟨(0 : ℕ), 3, 0, 4 * M + 3, E + 4 * M + 6⟩ [fm]⊢*
        ⟨0, 3 * M + 3, 0, 3, E + 3 * M + 6⟩ := by
      have h := d_drain_loop M 2 3 (E + 3 * M + 6)
      convert h using 2; all_goals ring_nf
    have p5 : ⟨(0 : ℕ), 3 * M + 3, 0, 3, E + 3 * M + 6⟩ [fm]⊢*
        ⟨6 * M + 11, 0, 0, 0, E + 6 * M + 10⟩ := by
      rw [show 3 * M + 3 = (3 * M + 2) + 1 from by ring,
          show E + 3 * M + 6 = (E + 3 * M + 5) + 1 from by ring]
      have h := exit_r3 (3 * M + 2) (E + 3 * M + 5)
      rw [show 2 * (3 * M + 2) + 7 = 6 * M + 11 from by ring,
          show E + 3 * M + 5 + (3 * M + 2) + 3 = E + 6 * M + 10 from by ring] at h
      exact h
    rw [show 6 * (M + 1) + 5 = 6 * M + 11 from by ring,
        show E + 6 * (M + 1) + 4 = E + 6 * M + 10 from by ring]
    exact stepPlus_stepStar_stepPlus p12
      (stepStar_trans p3 (stepStar_trans p4 p5))

theorem trans_mod0 (M E : ℕ) :
    ⟨4 * (M + 1), 0, 0, 0, E⟩ [fm]⊢⁺ ⟨6 * M + 8, 0, 0, 0, E + 6 * M + 4⟩ := by
  have p12 : ⟨4 * (M + 1), 0, 0, 0, E⟩ [fm]⊢⁺
      ⟨0, 0, 0, 4 * M + 4, E + 4 * M + 4⟩ := by
    rw [show 4 * (M + 1) = (4 * M + 3) + 1 from by ring,
        show E + 4 * M + 4 = E + (4 * M + 3) + 1 from by ring]
    exact phases12 (4 * M + 3) E
  have p3 : ⟨(0 : ℕ), 0, 0, 4 * M + 4, E + 4 * M + 4⟩ [fm]⊢*
      ⟨0, 3, 0, 4 * M, E + 4 * M + 3⟩ := by
    rw [show 4 * M + 4 = (4 * M) + 4 from by ring,
        show E + 4 * M + 4 = (E + 4 * M + 3) + 1 from by ring]
    exact d_drain_round_0 (4 * M) (E + 4 * M + 3)
  have p4 : ⟨(0 : ℕ), 3, 0, 4 * M, E + 4 * M + 3⟩ [fm]⊢*
      ⟨0, 3 * M + 3, 0, 0, E + 3 * M + 3⟩ := by
    have h := d_drain_loop M 2 0 (E + 3 * M + 3)
    convert h using 2; all_goals ring_nf
  have p5 : ⟨(0 : ℕ), 3 * M + 3, 0, 0, E + 3 * M + 3⟩ [fm]⊢*
      ⟨6 * M + 8, 0, 0, 0, E + 6 * M + 4⟩ := by
    rw [show 3 * M + 3 = (3 * M + 1) + 2 from by ring,
        show E + 3 * M + 3 = (E + 3 * M + 2) + 1 from by ring]
    have h := exit_r0 (3 * M + 1) (E + 3 * M + 2)
    rw [show 2 * (3 * M + 1) + 6 = 6 * M + 8 from by ring,
        show E + 3 * M + 2 + (3 * M + 1) + 1 = E + 6 * M + 4 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p12
    (stepStar_trans p3 (stepStar_trans p4 p5))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = (⟨A + 1, 0, 0, 0, E⟩ : Q))
  · intro c ⟨A, E, hc⟩; subst hc
    set M := (A + 1) / 4
    have hmod : (A + 1) % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : A + 1 = 4 * M + (A + 1) % 4 := (Nat.div_add_mod (A + 1) 4).symm
    interval_cases ((A + 1) % 4)
    · -- r = 0
      have hpos : M ≥ 1 := by omega
      have hA : A + 1 = 4 * (M - 1 + 1) := by omega
      exact ⟨⟨6 * (M - 1) + 8, 0, 0, 0, E + 6 * (M - 1) + 4⟩,
        ⟨6 * (M - 1) + 7, E + 6 * (M - 1) + 4, rfl⟩,
        hA ▸ trans_mod0 (M - 1) E⟩
    · -- r = 1
      have hA : A + 1 = 4 * M + 1 := by omega
      exact ⟨⟨6 * M + 3, 0, 0, 0, E + 6 * M⟩,
        ⟨6 * M + 2, E + 6 * M, rfl⟩,
        hA ▸ trans_mod1 M E⟩
    · -- r = 2
      have hA : A + 1 = 4 * M + 2 := by omega
      exact ⟨⟨6 * M + 4, 0, 0, 0, E + 6 * M + 2⟩,
        ⟨6 * M + 3, E + 6 * M + 2, rfl⟩,
        hA ▸ trans_mod2 M E⟩
    · -- r = 3
      have hA : A + 1 = 4 * M + 3 := by omega
      exact ⟨⟨6 * M + 5, 0, 0, 0, E + 6 * M + 4⟩,
        ⟨6 * M + 4, E + 6 * M + 4, rfl⟩,
        hA ▸ trans_mod3 M E⟩
  · show ∃ A E, c₀ = (⟨A + 1, 0, 0, 0, E⟩ : Q)
    exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1724
