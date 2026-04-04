import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1722: [8/15, 3/14, 275/2, 7/5, 10/11]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1722

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ A C E,
    ⟨A + k, 0, C, 0, E⟩ [fm]⊢* ⟨A, 0, C + 2 * k, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih A (C + 2) (E + 1))
  rw [show C + 2 + 2 * k = C + 2 * (k + 1) from by ring,
      show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r4_chain : ∀ k, ∀ D E,
    ⟨0, 0, k, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · exists 0
  rw [show k + 1 = k + 1 from rfl]; step fm
  apply stepStar_trans (ih (D + 1) E)
  rw [show D + 1 + k = D + (k + 1) from by ring]; finish

theorem r2_chain : ∀ k, ∀ A B D E,
    ⟨A + k, B, 0, D + k, E⟩ [fm]⊢* ⟨A, B + k, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih A (B + 1) D E)
  rw [show B + 1 + k = B + (k + 1) from by ring]; finish

theorem main_loop_step (B D E : ℕ) :
    ⟨4, B, 0, D + 4, E + 1⟩ [fm]⊢* ⟨4, B + 3, 0, D, E⟩ := by
  have h1 : ⟨4, B, 0, D + 4, E + 1⟩ [fm]⊢* ⟨0, B + 4, 0, D, E + 1⟩ := by
    rw [show (4 : ℕ) = 0 + 4 from by ring]; exact r2_chain 4 0 B D (E + 1)
  apply stepStar_trans h1
  apply stepStar_trans
    (step_stepStar (show fm ⟨0, B + 4, 0, D, E + 1⟩ = some ⟨1, B + 4, 1, D, E⟩ from by simp [fm]))
  rw [show B + 4 = (B + 3) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, (B + 3) + 1, 0 + 1, D, E⟩ = some ⟨4, B + 3, 0, D, E⟩ from by simp [fm]))
  exists 0

theorem main_loop : ∀ k, ∀ B R E,
    ⟨4, B, 0, 4 * k + R, k + E⟩ [fm]⊢* ⟨4, B + 3 * k, 0, R, E⟩ := by
  intro k; induction' k with k ih <;> intro B R E
  · simp; exists 0
  rw [show 4 * (k + 1) + R = (4 * k + R) + 4 from by ring,
      show (k + 1) + E = (k + E) + 1 from by ring]
  apply stepStar_trans (main_loop_step B (4 * k + R) (k + E))
  apply stepStar_trans (ih (B + 3) R E)
  rw [show B + 3 + 3 * k = B + 3 * (k + 1) from by ring]; finish

theorem b_drain_full : ∀ B, ∀ A F,
    ∃ D' E', (⟨A + 1, B, 0, 0, F⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D' + 1, E' + 1⟩)
      ∧ 4 * (E' + 1) ≥ D' + 2 := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro A F
  rcases B with _ | _ | B
  · refine ⟨2 * A + 1, F + A, ?_, by omega⟩
    rw [show A + 1 = A + 1 from rfl]; step fm
    have h1 := r3_chain A 0 2 (F + 1); simp only [Nat.zero_add] at h1
    apply stepStar_trans h1
    rw [show 2 + 2 * A = 2 * (A + 1) from by ring, show F + 1 + A = F + A + 1 from by ring]
    have h2 := r4_chain (2 * (A + 1)) 0 (F + A + 1)
    rw [show 0 + 2 * (A + 1) = 2 * A + 1 + 1 from by ring] at h2; exact h2
  · refine ⟨2 * A + 6, F + A + 3, ?_, by omega⟩
    rw [show A + 1 = A + 1 from rfl, show (1 : ℕ) = 0 + 1 from by ring]; step fm
    apply stepStar_trans
      (step_stepStar (show fm ⟨A, 0 + 1, 2, 0, F + 1⟩ = some ⟨A + 3, 0, 1, 0, F + 1⟩ from by simp [fm]))
    rw [show A + 3 = (A + 2) + 1 from by ring]; step fm
    have h2 := r3_chain (A + 2) 0 3 (F + 2); simp only [Nat.zero_add] at h2
    apply stepStar_trans h2
    rw [show 3 + 2 * (A + 2) = 2 * A + 7 from by ring, show F + 2 + (A + 2) = F + A + 4 from by ring]
    have h3 := r4_chain (2 * A + 7) 0 (F + A + 4)
    rw [show 0 + (2 * A + 7) = 2 * A + 6 + 1 from by ring,
        show F + A + 4 = F + A + 3 + 1 from by ring] at h3; exact h3
  · obtain ⟨D', E', hsteps, hinv⟩ := ih B (by omega) (A + 5) (F + 1)
    refine ⟨D', E', ?_, hinv⟩
    rw [show B + 2 = B + 1 + 1 from by ring, show A + 1 = A + 1 from rfl]; step fm
    apply stepStar_trans
      (step_stepStar (show fm ⟨A, B + 1 + 1, 2, 0, F + 1⟩ = some ⟨A + 3, B + 1, 1, 0, F + 1⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show fm ⟨A + 3, B + 1, 1, 0, F + 1⟩ = some ⟨A + 6, B, 0, 0, F + 1⟩ from by simp [fm]))
    rw [show A + 6 = (A + 5) + 1 from by ring]
    exact stepPlus_stepStar hsteps

theorem case_D1 (E : ℕ) :
    ⟨0, 0, 0, 1, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 6, E + 3⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; step fm; step fm
  have h1 := r3_chain 3 0 0 E; simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 2 * 3 = 6 from by ring]; exact r4_chain 6 0 (E + 3)

theorem case_D2 (E : ℕ) :
    ⟨0, 0, 0, 2, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 9, E + 5⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  have h1 := r3_chain 4 0 1 (E + 1); simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + 2 * 4 = 9 from by ring, show E + 1 + 4 = E + 5 from by ring]
  exact r4_chain 9 0 (E + 5)

theorem case_D3 (E : ℕ) :
    ⟨0, 0, 0, 3, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 12, E + 7⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  have h1 := r3_chain 6 0 0 (E + 1); simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 2 * 6 = 12 from by ring, show E + 1 + 6 = E + 7 from by ring]
  exact r4_chain 12 0 (E + 7)

theorem opening_D4 (D E : ℕ) :
    ⟨0, 0, 0, D + 4, E + 2⟩ [fm]⊢⁺ ⟨(4 : ℕ), 2, 0, D, E⟩ := by
  rw [show D + 4 = (D + 3) + 1 from by ring, show E + 2 = (E + 1) + 1 from by ring]
  step fm; step fm; step fm
  have h1 : ⟨3, 0, 0, D + 3, E + 1⟩ [fm]⊢* ⟨0, 3, 0, D, E + 1⟩ := by
    rw [show (3 : ℕ) = 0 + 3 from by ring]; exact r2_chain 3 0 0 D (E + 1)
  apply stepStar_trans h1
  apply stepStar_trans
    (step_stepStar (show fm ⟨0, 3, 0, D, E + 1⟩ = some ⟨1, 3, 1, D, E⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, 3, 1, D, E⟩ = some ⟨4, 2, 0, D, E⟩ from by simp [fm]))
  exists 0

theorem case_D_ge4 (D E : ℕ) (hE : E ≥ D / 4) :
    ∃ D' E', (⟨0, 0, 0, D + 4, E + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D' + 1, E' + 1⟩)
      ∧ 4 * (E' + 1) ≥ D' + 2 := by
  have hopen := opening_D4 D E
  set q := D / 4; set r := D % 4
  have hr : r < 4 := Nat.mod_lt D (by omega)
  have hqr : 4 * q + r = D := Nat.div_add_mod D 4
  have hEq : E ≥ q := hE
  have hloop := main_loop q 2 r (E - q)
  rw [show q + (E - q) = E from by omega] at hloop
  rw [← hqr] at hopen ⊢
  -- After loop: (4, 2+3q, 0, r, E-q). Drain remaining r via R2, then b drain.
  -- r <= 3, so R2 x r: (4-r, 2+3q+r, 0, 0, E-q). Then b_drain_full.
  have hr3 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  -- For each r, drain remaining d then do b_drain_full
  have drain_r : ∀ rv, rv ≤ 3 → ⟨4, 2 + 3 * q, 0, rv, E - q⟩ [fm]⊢*
      ⟨4 - rv, 2 + 3 * q + rv, 0, 0, E - q⟩ := by
    intro rv hrv
    rcases rv with _ | _ | _ | _ | rv
    · simp; exists 0
    · rw [show (4 : ℕ) = 3 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
      exact r2_chain 1 3 (2 + 3 * q) 0 (E - q)
    · rw [show (4 : ℕ) = 2 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
      exact r2_chain 2 2 (2 + 3 * q) 0 (E - q)
    · rw [show (4 : ℕ) = 1 + 3 from by ring, show (3 : ℕ) = 0 + 3 from by ring]
      exact r2_chain 3 1 (2 + 3 * q) 0 (E - q)
    · omega
  have hdr := drain_r r (by omega)
  have ha : 4 - r ≥ 1 := by omega
  rw [show 4 - r = (4 - r - 1) + 1 from by omega] at hdr
  obtain ⟨D', E', hbdrain, hinv⟩ := b_drain_full (2 + 3 * q + r) (4 - r - 1) (E - q)
  exact ⟨D', E', stepPlus_stepStar_stepPlus hopen
    (stepStar_trans hloop (stepStar_trans hdr (stepPlus_stepStar hbdrain))), hinv⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = (⟨0, 0, 0, D + 1, E + 1⟩ : Q) ∧ 4 * (E + 1) ≥ D + 2)
  · intro q ⟨D, E, hq, hinv⟩; subst hq
    rcases D with _ | _ | _ | D
    · exact ⟨_, ⟨5, E + 2, by simp [Q], by omega⟩, case_D1 E⟩
    · exact ⟨_, ⟨8, E + 4, by simp [Q], by omega⟩, case_D2 E⟩
    · exact ⟨_, ⟨11, E + 6, by simp [Q], by omega⟩, case_D3 E⟩
    · rcases E with _ | E'
      · omega
      · have hE' : E' ≥ D / 4 := by omega
        obtain ⟨D', E'', hsteps, hinv'⟩ := case_D_ge4 D E' hE'
        refine ⟨⟨0, 0, 0, D' + 1, E'' + 1⟩, ⟨D', E'', rfl, hinv'⟩, ?_⟩
        rw [show D + 3 + 1 = D + 4 from by ring, show E' + 1 + 1 = E' + 2 from by ring]
        exact hsteps
  · exact ⟨1, 0, by simp [Q], by omega⟩

end Sz22_2003_unofficial_1722
