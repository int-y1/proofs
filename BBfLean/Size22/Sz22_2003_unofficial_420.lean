import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #420: [27/10, 4/21, 77/2, 5/7, 14/11]

Vector representation:
```
-1  3 -1  0  0
 2 -1  0 -1  0
-1  0  0  1  1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_420

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 chain: j steps. (a+j, 0, 0, d, e) ->* (a, 0, 0, d+j, e+j)
private theorem r3_chain : ∀ j, ∀ a d e,
    ⟨a+j, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+j, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: j steps. (0, 0, c, d+j, e) ->* (0, 0, c+j, d, e)
private theorem r4_chain : ∀ j, ∀ c d e,
    ⟨0, 0, c, d+j, e⟩ [fm]⊢* ⟨0, 0, c+j, d, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Inner loop step: 5 steps. (0, b, c+3, 0, e+1) ->* (0, b+8, c, 0, e)
private theorem inner_loop_step : ∀ b c e,
    ⟨0, b, c+3, 0, e+1⟩ [fm]⊢* ⟨0, b+8, c, 0, e⟩ := by
  intro b c e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Inner loop: k iterations
private theorem inner_loop_iter : ∀ k, ∀ b c e,
    ⟨0, b, c+3*k, 0, e+k⟩ [fm]⊢* ⟨0, b+8*k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (inner_loop_step _ _ _)
  apply stepStar_trans (ih _ _ _)
  rw [show (b + 8) + 8 * k = b + 8 * (k + 1) from by ring]
  finish

-- R3/R2 drain: alternating R3 and R2 steps consume b
private theorem r3r2_drain : ∀ j, ∀ a e,
    ⟨a+1, j, 0, 0, e⟩ [fm]⊢* ⟨a+1+j, 0, 0, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition r=0: (3k+3, 0, 0, 0, e) ⊢⁺ (8k+10, 0, 0, 0, e+10k+8)
private theorem main_r0 (k e : ℕ) :
    ⟨3*k+3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨8*k+10, 0, 0, 0, e+10*k+8⟩ := by
  -- Phase 1+2: R3 then R4
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans
    · have h := r3_chain (3*k+3) 0 0 e
      simp only [(by ring : 0 + (3*k+3) = 3*k+3)] at h; exact h
    have h := r4_chain (3*k+3) 0 0 (e+(3*k+3))
    simp only [(by ring : 0 + (3*k+3) = 3*k+3)] at h; exact h
  -- Phase 3: inner loop
  apply stepStar_stepPlus_stepPlus
  · have h := inner_loop_iter (k+1) 0 0 (e+2*k+2)
    simp only [(by ring : 0 + 3*(k+1) = 3*k+3),
               (by ring : (e+2*k+2) + (k+1) = e+(3*k+3)),
               (by ring : 0 + 8*(k+1) = 8*k+8)] at h; exact h
  -- Phase 4: tail r=0
  apply step_stepStar_stepPlus
  · show fm ⟨0, 8*k+8, 0, 0, (e+2*k+1)+1⟩ = some ⟨1, 8*k+8, 0, 1, e+2*k+1⟩; rfl
  step fm
  have h := r3r2_drain (8*k+7) 2 (e+2*k+1)
  simp only [(by ring : 2+1+(8*k+7) = 8*k+10),
             (by ring : (e+2*k+1)+(8*k+7) = e+10*k+8)] at h; exact h

-- Main transition r=1: (3k+4, 0, 0, 0, e) ⊢⁺ (8k+12, 0, 0, 0, e+10k+12)
private theorem main_r1 (k e : ℕ) :
    ⟨3*k+4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨8*k+12, 0, 0, 0, e+10*k+12⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans
    · have h := r3_chain (3*k+4) 0 0 e
      simp only [(by ring : 0 + (3*k+4) = 3*k+4)] at h; exact h
    have h := r4_chain (3*k+4) 0 0 (e+(3*k+4))
    simp only [(by ring : 0 + (3*k+4) = 3*k+4)] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := inner_loop_iter (k+1) 0 1 (e+2*k+3)
    simp only [(by ring : 1 + 3*(k+1) = 3*k+4),
               (by ring : (e+2*k+3) + (k+1) = e+(3*k+4)),
               (by ring : 0 + 8*(k+1) = 8*k+8)] at h; exact h
  -- tail r=1: R5, R1, R2, drain
  apply step_stepStar_stepPlus
  · show fm ⟨0, 8*k+8, 1, 0, (e+2*k+2)+1⟩ = some ⟨1, 8*k+8, 1, 1, e+2*k+2⟩; rfl
  step fm; step fm
  have h := r3r2_drain (8*k+10) 1 (e+2*k+2)
  simp only [(by ring : 1+1+(8*k+10) = 8*k+12),
             (by ring : (e+2*k+2)+(8*k+10) = e+10*k+12)] at h; exact h

-- Main transition r=2: (3k+5, 0, 0, 0, e) ⊢⁺ (8k+14, 0, 0, 0, e+10k+16)
private theorem main_r2 (k e : ℕ) :
    ⟨3*k+5, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨8*k+14, 0, 0, 0, e+10*k+16⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans
    · have h := r3_chain (3*k+5) 0 0 e
      simp only [(by ring : 0 + (3*k+5) = 3*k+5)] at h; exact h
    have h := r4_chain (3*k+5) 0 0 (e+(3*k+5))
    simp only [(by ring : 0 + (3*k+5) = 3*k+5)] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := inner_loop_iter (k+1) 0 2 (e+2*k+4)
    simp only [(by ring : 2 + 3*(k+1) = 3*k+5),
               (by ring : (e+2*k+4) + (k+1) = e+(3*k+5)),
               (by ring : 0 + 8*(k+1) = 8*k+8)] at h; exact h
  -- tail r=2: R5, R1, R2, R1, R3, R2, drain
  apply step_stepStar_stepPlus
  · show fm ⟨0, 8*k+8, 2, 0, (e+2*k+3)+1⟩ = some ⟨1, 8*k+8, 2, 1, e+2*k+3⟩; rfl
  step fm; step fm; step fm; step fm; step fm
  have h := r3r2_drain (8*k+12) 1 (e+2*k+4)
  simp only [(by ring : 1+1+(8*k+12) = 8*k+14),
             (by ring : (e+2*k+4)+(8*k+12) = e+10*k+16)] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 2⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm) (fun q => ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 3)
  · rintro c ⟨a, e, rfl, ha⟩
    have h3 : a % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : a = 3 * (a / 3) + a % 3 := (Nat.div_add_mod a 3).symm
    interval_cases (a % 3)
    · have hk : a / 3 ≥ 1 := by omega
      set m := a / 3 - 1
      have hak : a = 3 * m + 3 := by omega
      rw [hak]
      exact ⟨_, ⟨8*m+10, e+10*m+8, rfl, by omega⟩, main_r0 m e⟩
    · have hk : a / 3 ≥ 1 := by omega
      set m := a / 3 - 1
      have hak : a = 3 * m + 4 := by omega
      rw [hak]
      exact ⟨_, ⟨8*m+12, e+10*m+12, rfl, by omega⟩, main_r1 m e⟩
    · have hk : a / 3 ≥ 1 := by omega
      set m := a / 3 - 1
      have hak : a = 3 * m + 5 := by omega
      rw [hak]
      exact ⟨_, ⟨8*m+14, e+10*m+16, rfl, by omega⟩, main_r2 m e⟩
  · exact ⟨4, 2, rfl, by omega⟩

end Sz22_2003_unofficial_420
