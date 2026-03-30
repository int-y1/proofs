import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1055

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e

theorem r5r1r1_one : ∀ b c e,
    ⟨(0 : ℕ), b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 2, 0, e⟩ := by
  intro b c e; step fm; step fm; step fm; finish

theorem r5r1r1_chain : ∀ k b c e,
    ⟨(0 : ℕ), b + k + k + k + k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + k + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · ring_nf; finish
  · rw [show b + (k + 1) + (k + 1) + (k + 1) + (k + 1) = (b + k + k + k + k) + 4 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (r5r1r1_one (b + k + k + k + k) c (e + k))
    rw [show c + (k + 1) + (k + 1) = (c + 2) + k + k from by ring]
    exact ih b (c + 2) e

theorem r3r2_chain_b0 : ∀ k d e,
    ⟨(0 : ℕ), 0, k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + k + k + 3, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from rfl,
        show d + (k + 1) + (k + 1) + 3 = (d + 2) + k + k + 3 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    step fm; step fm
    exact ih (d + 2) (e + 1)

theorem r3r2_chain_b1 : ∀ k d e,
    ⟨(0 : ℕ), 1, k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 1, 0, d + k + k + 3, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from rfl,
        show d + (k + 1) + (k + 1) + 3 = (d + 2) + k + k + 3 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    step fm; step fm
    exact ih (d + 2) (e + 1)

theorem main_trans_core (k F : ℕ) :
    ⟨(0 : ℕ), 0, 0, 12 * k + 9, F + 3 * k + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 12 * k + 21, F + 12 * k + 16⟩ := by
  -- Phase 1: R4 drain (12k+9): -> (0,12k+9,0,0,F+3k+4)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 0, 0, 12 * k + 9, F + 3 * k + 4⟩ [fm]⊢*
         ⟨0, 12 * k + 9, 0, 0, F + 3 * k + 4⟩
    have h := r4_drain (12 * k + 9) 0 (F + 3 * k + 4)
    convert h using 2; ring_nf
  -- Phase 2: R5R1R1 (3k+2) rounds: -> (0,1,6k+4,0,F+2)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 12 * k + 9, 0, 0, F + 3 * k + 4⟩ [fm]⊢*
         ⟨0, 1, 6 * k + 4, 0, F + 2⟩
    have h := r5r1r1_chain (3 * k + 2) 1 0 (F + 2)
    convert h using 2; ring_nf
  -- Phase 3: R5,R2,R2: -> (0,1,6k+4,6,F+3)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, 6 * k + 4, 0, F + 2⟩ [fm]⊢*
         ⟨0, 1, 6 * k + 4, 6, F + 3⟩
    step fm; step fm; step fm; ring_nf; finish
  -- Phase 4: R3R2b1 (6k+3) rounds: -> (0,1,0,12k+14,F+6k+7)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, 6 * k + 4, 6, F + 3⟩ [fm]⊢*
         ⟨0, 1, 0, 12 * k + 14, F + 6 * k + 7⟩
    have h := r3r2_chain_b1 (6 * k + 3) 5 (F + 3)
    convert h using 2; ring_nf
  -- Phase 5: R4 drain (12k+14): -> (0,12k+15,0,0,F+6k+7)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, 0, 12 * k + 14, F + 6 * k + 7⟩ [fm]⊢*
         ⟨0, 12 * k + 15, 0, 0, F + 6 * k + 7⟩
    have h := r4_drain (12 * k + 14) 1 (F + 6 * k + 7)
    convert h using 2; ring_nf
  -- Phase 6: R5R1R1 (3k+3) rounds: -> (0,3,6k+6,0,F+3k+4)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 12 * k + 15, 0, 0, F + 6 * k + 7⟩ [fm]⊢*
         ⟨0, 3, 6 * k + 6, 0, F + 3 * k + 4⟩
    have h := r5r1r1_chain (3 * k + 3) 3 0 (F + 3 * k + 4)
    convert h using 2; ring_nf
  -- Phase 7: R5,R1,R2: -> (0,1,6k+7,3,F+3k+4)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 3, 6 * k + 6, 0, F + 3 * k + 4⟩ [fm]⊢*
         ⟨0, 1, 6 * k + 7, 3, F + 3 * k + 4⟩
    step fm; step fm; step fm; ring_nf; finish
  -- Phase 8: R3R2b1 (6k+6) rounds: -> (0,1,0,12k+17,F+9k+11)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, 6 * k + 7, 3, F + 3 * k + 4⟩ [fm]⊢*
         ⟨0, 1, 0, 12 * k + 17, F + 9 * k + 11⟩
    have h := r3r2_chain_b1 (6 * k + 6) 2 (F + 3 * k + 4)
    convert h using 2; ring_nf
  -- Phase 9: R4 drain (12k+17): -> (0,12k+18,0,0,F+9k+11)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, 0, 12 * k + 17, F + 9 * k + 11⟩ [fm]⊢*
         ⟨0, 12 * k + 18, 0, 0, F + 9 * k + 11⟩
    have h := r4_drain (12 * k + 17) 1 (F + 9 * k + 11)
    convert h using 2; ring_nf
  -- Phase 10: R5R1R1 (3k+4) rounds: -> (0,2,6k+8,0,F+6k+7)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 12 * k + 18, 0, 0, F + 9 * k + 11⟩ [fm]⊢*
         ⟨0, 2, 6 * k + 8, 0, F + 6 * k + 7⟩
    have h := r5r1r1_chain (3 * k + 4) 2 0 (F + 6 * k + 7)
    convert h using 2; ring_nf
  -- Phase 11: R5,R1,R2: -> (0,0,6k+9,3,F+6k+7)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 2, 6 * k + 8, 0, F + 6 * k + 7⟩ [fm]⊢*
         ⟨0, 0, 6 * k + 9, 3, F + 6 * k + 7⟩
    step fm; step fm; step fm; ring_nf; finish
  -- Phase 12: R3R2b0 (6k+8) rounds: -> (0,0,0,12k+21,F+12k+16)
  apply stepStar_stepPlus
  · show ⟨(0 : ℕ), 0, 6 * k + 9, 3, F + 6 * k + 7⟩ [fm]⊢*
         ⟨0, 0, 0, 12 * k + 21, F + 12 * k + 16⟩
    have h := r3r2_chain_b0 (6 * k + 8) 2 (F + 6 * k + 7)
    convert h using 2; ring_nf
  · intro heq; simp [Q] at heq

private def E : ℕ → ℕ
  | 0 => 4
  | k + 1 => E k + 9 * k + 12

private theorem E_ge (k : ℕ) : E k ≥ 3 * k + 4 := by
  induction k with
  | zero => simp [E]
  | succ k ih => simp [E]; omega

theorem main_trans (k : ℕ) :
    ⟨(0 : ℕ), 0, 0, 12 * k + 9, E k⟩ [fm]⊢⁺ ⟨0, 0, 0, 12 * k + 21, E (k + 1)⟩ := by
  have hE := E_ge k
  have h1 : E k = (E k - 3 * k - 4) + 3 * k + 4 := by omega
  have h2 : E (k + 1) = (E k - 3 * k - 4) + 12 * k + 16 := by simp [E]; omega
  rw [h1, h2]
  exact main_trans_core k (E k - 3 * k - 4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 9, E 0⟩) (by execute fm 26)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, 12 * k + 9, E k⟩) 0
  intro k
  exact ⟨k + 1, main_trans k⟩

end Sz22_2003_unofficial_1055
