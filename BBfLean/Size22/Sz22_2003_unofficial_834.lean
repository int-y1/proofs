import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# sz22_2003_unofficial #834: [35/6, 9/55, 8/5, 11/7, 15/2]

Vector representation:
```
-1 -1  1  1  0
 0  2 -1  0 -1
 3  0 -1  0  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_834

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem d_to_e : ∀ k a d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem r3_chain : ∀ k a c d, ⟨a, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 3) c d); ring_nf; finish

theorem r2_a0 : ∀ k b c d, ⟨0, b, c + k, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b c d; simp; exists 0
  | succ k ih =>
    intro b c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) c d); ring_nf; finish

theorem unified_tail : ∀ B C D,
    ⟨0, B, C + 1, D, 0⟩ [fm]⊢* ⟨3 * (C + 1) + 2 * B, 0, 0, D + B, 0⟩ := by
  intro B; induction B using Nat.strongRecOn with
  | _ B ih =>
    intro C D
    match B with
    | 0 =>
      rw [show C + 1 = 0 + (C + 1) from by ring]
      apply stepStar_trans (r3_chain (C + 1) 0 0 D); ring_nf; finish
    | 1 =>
      step fm; step fm
      show ⟨2, 0, C + 1, D + 1, 0⟩ [fm]⊢* _
      rw [show C + 1 = 0 + (C + 1) from by ring]
      apply stepStar_trans (r3_chain (C + 1) 2 0 (D + 1)); ring_nf; finish
    | 2 =>
      step fm; step fm; step fm
      show ⟨1, 0, C + 2, D + 2, 0⟩ [fm]⊢* _
      rw [show C + 2 = 0 + (C + 2) from by ring]
      apply stepStar_trans (r3_chain (C + 2) 1 0 (D + 2)); ring_nf; finish
    | B + 3 =>
      step fm; step fm; step fm; step fm
      show ⟨0, B, (C + 2) + 1, D + 3, 0⟩ [fm]⊢* _
      apply stepStar_trans (ih B (by omega) (C + 2) (D + 3)); ring_nf; finish

theorem tail_bc (B : ℕ) {C : ℕ} (hC : C ≥ 1) (D : ℕ) :
    ⟨0, B, C, D, 0⟩ [fm]⊢* ⟨3 * C + 2 * B, 0, 0, D + B, 0⟩ := by
  obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
  exact unified_tail B C' D

theorem combined_drain : ∀ E a C D, E ≤ C + a →
    ⟨a, 0, C + 1, D, E⟩ [fm]⊢* ⟨a + 3 * (C + 1) + E, 0, 0, D + 2 * E, 0⟩ := by
  intro E; induction E with
  | zero =>
    intro a C D _; simp
    rw [show C + 1 = 0 + (C + 1) from by ring]
    apply stepStar_trans (r3_chain (C + 1) a 0 D); ring_nf; finish
  | succ E ih =>
    intro a C D hle
    match a with
    | 0 =>
      -- (0, 0, C+1, D, E+1). E+1 ≤ C, so C ≥ E+1.
      -- Let C' = C - E - 1 so C + 1 = C' + 1 + (E + 1).
      obtain ⟨C', rfl⟩ : ∃ C', C = C' + E + 1 := ⟨C - E - 1, by omega⟩
      -- Now C + 1 = C' + E + 1 + 1 = (C' + 1) + (E + 1).
      rw [show C' + E + 1 + 1 = (C' + 1) + (E + 1) from by ring]
      apply stepStar_trans (r2_a0 (E + 1) 0 (C' + 1) D)
      -- At (0, 2*(E+1), C'+1, D, 0).
      apply stepStar_trans (unified_tail (0 + 2 * (E + 1)) C' D)
      -- Close the goal
      rw [show 3 * (C' + 1) + 2 * (0 + 2 * (E + 1)) =
              0 + 3 * ((C' + 1) + (E + 1)) + (E + 1) from by ring,
          show D + (0 + 2 * (E + 1)) = D + 2 * (E + 1) from by ring]; finish
    | 1 =>
      -- (1, 0, C+1, D, E+1). R2+R1 → (0, 1, C+1, D+1, E).
      -- E+1 ≤ C+1, so E ≤ C. Let C' = C - E so C = C' + E.
      obtain ⟨C', rfl⟩ : ∃ C', C = C' + E := ⟨C - E, by omega⟩
      step fm; step fm
      show ⟨0, 1, C' + E + 1, D + 1, E⟩ [fm]⊢* _
      -- r2_drain E: C' + E + 1 = (C' + 1) + E.
      rw [show C' + E + 1 = (C' + 1) + E from by ring]
      apply stepStar_trans (r2_a0 E 1 (C' + 1) (D + 1))
      -- At (0, 1+2*E, C'+1, D+1, 0).
      apply stepStar_trans (unified_tail (1 + 2 * E) C' (D + 1))
      rw [show 3 * (C' + 1) + 2 * (1 + 2 * E) =
              1 + 3 * ((C' + 1) + E) + (E + 1) from by ring,
          show D + 1 + (1 + 2 * E) = D + 2 * (E + 1) from by ring]; finish
    | a + 2 =>
      -- (a+2, 0, C+1, D, E+1). R2+R1+R1 → (a, 0, C+2, D+2, E).
      step fm; step fm; step fm
      show ⟨a, 0, (C + 1) + 1, D + 2, E⟩ [fm]⊢* _
      apply stepStar_trans (ih a (C + 1) (D + 2) (by omega))
      rw [show a + 3 * ((C + 1) + 1) + E = a + 2 + 3 * (C + 1) + (E + 1) from by ring,
          show D + 2 + 2 * E = D + 2 * (E + 1) from by ring]; finish

theorem full_trans_star (a d : ℕ) :
    ⟨a + d + 2, 0, 0, d, 1⟩ [fm]⊢* ⟨a + 2 * d + 7, 0, 0, 2 * d + 3, 0⟩ := by
  apply stepStar_trans
  · show ⟨a + d + 2, 0, 0, d, 1⟩ [fm]⊢* ⟨a + d + 2, 0, 0, 0, 1 + d⟩
    have h := d_to_e d (a + d + 2) 0 1
    simp at h; exact h
  rw [show 1 + d = d + 1 from by ring]
  step fm; step fm
  show ⟨a + d, 0, 1 + 1, 1, d + 1⟩ [fm]⊢* ⟨a + 2 * d + 7, 0, 0, 2 * d + 3, 0⟩
  have h := combined_drain (d + 1) (a + d) 1 1 (by omega)
  simp only [show a + d + 3 * (1 + 1) + (d + 1) = a + 2 * d + 7 from by ring,
             show 1 + 2 * (d + 1) = 2 * d + 3 from by ring] at h
  exact h

theorem main_trans (a d : ℕ) :
    ⟨a + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 7, 0, 0, 2 * d + 3, 0⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a + d + 2, 0, 0, d, 1⟩)
  · simp [fm]
  exact full_trans_star a d

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 1, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d + 2 ∧ d ≥ 1)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    obtain ⟨e, rfl⟩ : ∃ e, a = e + d + 2 := ⟨a - d - 2, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f, d = f + 1 := ⟨d - 1, by omega⟩
    refine ⟨⟨e + 2 * f + 8, 0, 0, 2 * f + 3, 0⟩,
      ⟨e + 2 * f + 8, 2 * f + 3, rfl, by omega, by omega⟩, ?_⟩
    have h := main_trans (e + 1) f
    convert h using 2; ring_nf
  · exact ⟨5, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_834
