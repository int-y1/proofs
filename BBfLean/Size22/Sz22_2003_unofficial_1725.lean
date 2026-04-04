import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1725: [8/15, 3/14, 55/2, 7/5, 50/11]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1725

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

theorem r3_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a (c + 1) (e + 1))
  rw [show c + 1 + k = c + (k + 1) from by ring,
      show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r4_chain : ∀ k d e, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]; step fm
  apply stepStar_trans (ih (d + 1) e)
  rw [show d + 1 + k = d + (k + 1) from by ring]; finish

theorem r2_chain : ∀ k A B D E, ⟨A + k, B, 0, D + k, E⟩ [fm]⊢* ⟨A, B + k, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih A (B + 1) D E)
  rw [show B + 1 + k = B + (k + 1) from by ring]; finish

theorem r3r1_chain : ∀ k a e,
    ⟨a + 2, k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 4, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; finish
  rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]; step fm
  rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]; step fm
  rw [show a + 4 = (a + 2) + 2 from by ring]
  apply stepStar_trans (ih (a + 2) (e + 1))
  rw [show a + 2 + 2 * k + 4 = a + 2 * (k + 1) + 4 from by ring,
      show e + 1 + k + 1 = e + (k + 1) + 1 from by ring]; finish

theorem drain_step_b0 : ∀ D E, ⟨0, 0, 0, D + 7, E + 1⟩ [fm]⊢* ⟨0, 5, 0, D, E⟩ := by
  intro D E
  rw [show D + 7 = (D + 5) + 2 from by ring]
  step fm
  rw [show D + 5 + 2 = (D + 5 + 1) + 1 from by ring]; step fm; step fm
  rw [show D + 5 + 1 = (D + 5) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm
  rw [show (5 : ℕ) = 0 + 5 from by ring, show D + 5 = D + 5 from rfl]
  exact r2_chain 5 0 0 D E

theorem drain_step_b1 : ∀ D E, ⟨0, 1, 0, D + 7, E + 1⟩ [fm]⊢* ⟨0, 6, 0, D, E⟩ := by
  intro D E
  step fm; step fm
  rw [show D + 7 = (D + 6) + 1 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  step fm; step fm
  rw [show (6 : ℕ) = 0 + 6 from by ring, show D + 6 = D + 6 from rfl]
  exact r2_chain 6 0 0 D E

theorem drain_step_bpos : ∀ B D E,
    ⟨0, B + 2, 0, D + 7, E + 1⟩ [fm]⊢* ⟨0, B + 7, 0, D, E⟩ := by
  intro B D E
  step fm
  rw [show B + 2 = (B + 1) + 1 from by ring]; step fm
  rw [show B + 1 = B + 1 from rfl]; step fm
  rw [show (7 : ℕ) = 0 + 7 from by ring, show D + 7 = D + 7 from rfl]
  apply stepStar_trans (r2_chain 7 0 B D E)
  rw [show B + 7 = B + 7 from rfl]; finish

theorem drain_loop : ∀ k B D E,
    ⟨0, B, 0, D + 7 * k, E + k⟩ [fm]⊢* ⟨0, B + 5 * k, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · simp; exists 0
  rw [show D + 7 * (k + 1) = (D + 7 * k) + 7 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  rcases B with _ | _ | B
  · apply stepStar_trans (drain_step_b0 (D + 7 * k) (E + k))
    rw [show (5 : ℕ) = 0 + 5 from by ring]
    apply stepStar_trans (ih 5 D E)
    rw [show 5 + 5 * k = 0 + 5 * (k + 1) from by ring]; finish
  · apply stepStar_trans (drain_step_b1 (D + 7 * k) (E + k))
    rw [show (6 : ℕ) = 1 + 5 from by ring]
    apply stepStar_trans (ih (1 + 5) D E)
    rw [show 1 + 5 + 5 * k = 1 + 5 * (k + 1) from by ring]; finish
  · apply stepStar_trans (drain_step_bpos B (D + 7 * k) (E + k))
    rw [show B + 7 = (B + 2) + 5 from by ring]
    apply stepStar_trans (ih ((B + 2) + 5) D E)
    rw [show B + 2 + 5 + 5 * k = B + 2 + 5 * (k + 1) from by ring]; finish

theorem r5r1r1 : ∀ B d F,
    ⟨0, B + 3, 0, d, F + 1⟩ [fm]⊢* ⟨7, B + 1, 0, d, F⟩ := by
  intro B d F
  rw [show B + 3 = (B + 2) + 1 from by ring]; step fm
  rw [show B + 2 = (B + 1) + 1 from by ring]; step fm
  rw [show B + 1 = B + 1 from rfl]; step fm; finish

-- Per-d exit lemmas with correct formulas
-- General: (0, B+3, 0, d, F+1) -> (2B+d+9, 0, 0, 0, F+B+d+1)
theorem exit_d0 : ∀ B F,
    ⟨0, B + 3, 0, 0, F + 1⟩ [fm]⊢* ⟨2 * B + 9, 0, 0, 0, F + B + 1⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 0 F)
  rw [show (7 : ℕ) = 5 + 2 from by ring, show B + 1 = B + 1 from rfl]
  apply stepStar_trans (r3r1_chain B 5 F)
  rw [show 5 + 2 * B + 4 = 2 * B + 9 from by ring]; finish

theorem exit_d1 : ∀ B F,
    ⟨0, B + 3, 0, 1, F + 1⟩ [fm]⊢* ⟨2 * B + 10, 0, 0, 0, F + B + 2⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 1 F)
  rw [show (7 : ℕ) = 6 + 1 from by ring]; step fm
  rw [show (6 : ℕ) = 4 + 2 from by ring, show B + 1 + 1 = (B + 1) + 1 from by ring]
  apply stepStar_trans (r3r1_chain (B + 1) 4 F)
  rw [show 4 + 2 * (B + 1) + 4 = 2 * B + 10 from by ring,
      show F + (B + 1) + 1 = F + B + 2 from by ring]; finish

theorem exit_d2 : ∀ B F,
    ⟨0, B + 3, 0, 2, F + 1⟩ [fm]⊢* ⟨2 * B + 11, 0, 0, 0, F + B + 3⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 2 F)
  rw [show (7 : ℕ) = 5 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2_chain 2 5 (B + 1) 0 F)
  rw [show B + 1 + 2 = (B + 2) + 1 from by ring, show (5 : ℕ) = 3 + 2 from by ring]
  apply stepStar_trans (r3r1_chain (B + 2) 3 F)
  rw [show 3 + 2 * (B + 2) + 4 = 2 * B + 11 from by ring,
      show F + (B + 2) + 1 = F + B + 3 from by ring]; finish

theorem exit_d3 : ∀ B F,
    ⟨0, B + 3, 0, 3, F + 1⟩ [fm]⊢* ⟨2 * B + 12, 0, 0, 0, F + B + 4⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 3 F)
  rw [show (7 : ℕ) = 4 + 3 from by ring, show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_trans (r2_chain 3 4 (B + 1) 0 F)
  rw [show B + 1 + 3 = (B + 3) + 1 from by ring, show (4 : ℕ) = 2 + 2 from by ring]
  apply stepStar_trans (r3r1_chain (B + 3) 2 F)
  rw [show 2 + 2 * (B + 3) + 4 = 2 * B + 12 from by ring,
      show F + (B + 3) + 1 = F + B + 4 from by ring]; finish

theorem exit_d4 : ∀ B F,
    ⟨0, B + 3, 0, 4, F + 1⟩ [fm]⊢* ⟨2 * B + 13, 0, 0, 0, F + B + 5⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 4 F)
  rw [show (7 : ℕ) = 3 + 4 from by ring, show (4 : ℕ) = 0 + 4 from by ring]
  apply stepStar_trans (r2_chain 4 3 (B + 1) 0 F)
  rw [show B + 1 + 4 = (B + 4) + 1 from by ring, show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_trans (r3r1_chain (B + 4) 1 F)
  rw [show 1 + 2 * (B + 4) + 4 = 2 * B + 13 from by ring,
      show F + (B + 4) + 1 = F + B + 5 from by ring]; finish

theorem exit_d5 : ∀ B F,
    ⟨0, B + 3, 0, 5, F + 1⟩ [fm]⊢* ⟨2 * B + 14, 0, 0, 0, F + B + 6⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 5 F)
  rw [show (7 : ℕ) = 2 + 5 from by ring, show (5 : ℕ) = 0 + 5 from by ring]
  apply stepStar_trans (r2_chain 5 2 (B + 1) 0 F)
  rw [show B + 1 + 5 = (B + 5) + 1 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r3r1_chain (B + 5) 0 F)
  rw [show 0 + 2 * (B + 5) + 4 = 2 * B + 14 from by ring,
      show F + (B + 5) + 1 = F + B + 6 from by ring]; finish

theorem exit_d6 : ∀ B F,
    ⟨0, B + 3, 0, 6, F + 1⟩ [fm]⊢* ⟨2 * B + 15, 0, 0, 0, F + B + 7⟩ := by
  intro B F
  apply stepStar_trans (r5r1r1 B 6 F)
  rw [show (7 : ℕ) = 1 + 6 from by ring, show (6 : ℕ) = 0 + 6 from by ring]
  apply stepStar_trans (r2_chain 6 1 (B + 1) 0 F)
  rw [show B + 1 + 6 = (B + 6) + 1 from by ring]
  step fm
  rw [show B + 6 + 1 = (B + 6) + 1 from by ring]; step fm
  rw [show (3 : ℕ) = 1 + 2 from by ring, show B + 6 = (B + 5) + 1 from by ring]
  apply stepStar_trans (r3r1_chain (B + 5) 1 (F + 1))
  rw [show 1 + 2 * (B + 5) + 4 = 2 * B + 15 from by ring,
      show F + 1 + (B + 5) + 1 = F + B + 7 from by ring]; finish

theorem exit_phase (d B F : ℕ) (hd : d ≤ 6) :
    ⟨0, B + 3, 0, d, F + 1⟩ [fm]⊢*
    ⟨2 * B + d + 9, 0, 0, 0, F + B + d + 1⟩ := by
  have hd7 : d % 7 < 7 := Nat.mod_lt _ (by omega)
  interval_cases d <;> [exact exit_d0 B F; exact exit_d1 B F; exact exit_d2 B F;
    exact exit_d3 B F; exact exit_d4 B F; exact exit_d5 B F; exact exit_d6 B F]

theorem main_trans (K d E : ℕ) (hd : d ≤ 6) :
    ⟨7 * K + d + 7, 0, 0, 0, E⟩ [fm]⊢⁺
    ⟨10 * K + d + 13, 0, 0, 0, E + 11 * K + 2 * d + 8⟩ := by
  set A := 7 * K + d + 7
  have p1 : ⟨A, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨0, 0, A, 0, E + A⟩ := by
    have h := r3_chain A 0 0 E; simp at h
    exact stepStar_stepPlus h (by simp [Q])
  have p2 : ⟨0, 0, A, 0, E + A⟩ [fm]⊢* ⟨0, 0, 0, A, E + A⟩ := by
    have h := r4_chain A 0 (E + A); simp at h; exact h
  have p3 : ⟨0, 0, 0, A, E + A⟩ [fm]⊢*
      ⟨0, 5 * (K + 1), 0, d, E + 6 * K + d + 6⟩ := by
    have h := drain_loop (K + 1) 0 d (E + 6 * K + d + 6); simp at h
    convert h using 2; simp_all [A]; ring_nf
  have p4 : ⟨0, 5 * (K + 1), 0, d, E + 6 * K + d + 6⟩ [fm]⊢*
      ⟨10 * K + d + 13, 0, 0, 0, E + 11 * K + 2 * d + 8⟩ := by
    rw [show 5 * (K + 1) = (5 * K + 2) + 3 from by ring,
        show E + 6 * K + d + 6 = (E + 6 * K + d + 5) + 1 from by ring]
    have h := exit_phase d (5 * K + 2) (E + 6 * K + d + 5) hd
    convert h using 2; ring_nf
  exact stepPlus_stepStar_stepPlus (stepPlus_stepStar_stepPlus p1 p2)
    (stepStar_trans p3 p4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 4⟩) (by execute fm 23)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = (⟨A + 7, 0, 0, 0, E⟩ : Q))
  · intro c ⟨A, E, hc⟩; subst hc
    set K := A / 7; set d := A % 7
    have hmod : d < 7 := Nat.mod_lt _ (by omega)
    have hdiv : A = 7 * K + d := (Nat.div_add_mod A 7).symm
    refine ⟨⟨10 * K + d + 13, 0, 0, 0, E + 11 * K + 2 * d + 8⟩,
      ⟨10 * K + d + 6, E + 11 * K + 2 * d + 8, by simp [Q]⟩, ?_⟩
    show ⟨A + 7, 0, 0, 0, E⟩ [fm]⊢⁺
         ⟨10 * K + d + 13, 0, 0, 0, E + 11 * K + 2 * d + 8⟩
    have hA : A + 7 = 7 * K + d + 7 := by omega
    rw [hA]
    exact main_trans K d E (by omega)
  · exact ⟨0, 4, rfl⟩

end Sz22_2003_unofficial_1725
