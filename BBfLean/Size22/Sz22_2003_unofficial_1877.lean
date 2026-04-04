import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1877: [9/35, 5/33, 14/3, 121/7, 245/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  2
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1877

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 2))
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

theorem e_reduce_c0 : ⟨a + 1, 0, 0, 0, e + 4⟩ [fm]⊢* ⟨a, 0, 3, 0, e⟩ := by
  execute fm 7

theorem e_reduce_cS : ⟨a + 1, 0, c + 1, 0, e + 4⟩ [fm]⊢* ⟨a, 0, c + 4, 0, e⟩ := by
  execute fm 7

theorem e_reduce : ∀ k c, ⟨a + k, 0, c, 0, e + 4 * k⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 4 * (k + 1) = (e + 4 * k) + 4 from by ring]
    rcases c with _ | c
    · apply stepStar_trans e_reduce_c0
      apply stepStar_trans (ih 3)
      rw [show 3 + 3 * k = 0 + 3 * (k + 1) from by ring]; finish
    · apply stepStar_trans e_reduce_cS
      apply stepStar_trans (ih (c + 4))
      rw [show c + 4 + 3 * k = c + 1 + 3 * (k + 1) from by ring]; finish

theorem r3r1_chain : ∀ c, ∀ a j, ⟨a, j + 4, c, 0, 0⟩ [fm]⊢* ⟨a + c, j + 4 + c, 0, 0, 0⟩ := by
  intro c; induction' c with c ih <;> intro a j
  · exists 0
  · step fm; step fm
    rw [show j + 3 + 2 = (j + 1) + 4 from by ring]
    apply stepStar_trans (ih (a + 1) (j + 1))
    rw [show a + 1 + c = a + (c + 1) from by ring,
        show j + 1 + 4 + c = j + 4 + (c + 1) from by ring]; finish

theorem b_to_d : ∀ b, ∀ a d, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a + b, 0, 0, d + b, 0⟩ := by
  intro b; induction' b with b ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem drain_e0 : ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 4, 0, 0, c + 4, 0⟩ := by
  step fm; step fm; step fm
  -- After R5, R1, R1: (a, 0+4, c, 0, 0)
  apply stepStar_trans (r3r1_chain c a 0)
  rw [show 0 + 4 + c = c + 4 from by ring]
  apply stepStar_trans (b_to_d (c + 4) (a + c) 0)
  ring_nf; finish

theorem drain_e2 : ⟨a + 1, 0, c + 1, 0, 2⟩ [fm]⊢⁺ ⟨a + 2 * c + 6, 0, 0, c + 4, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- After 9 steps: (a+2, 0+4, c, 0, 0)
  apply stepStar_trans (r3r1_chain c (a + 2) 0)
  rw [show a + 2 + c = a + c + 2 from by ring,
      show 0 + 4 + c = c + 4 from by ring]
  apply stepStar_trans (b_to_d (c + 4) (a + c + 2) 0)
  ring_nf; finish

theorem main_even (K : ℕ) :
    ⟨A + K + 2, 0, 0, 2 * K + 2, 0⟩ [fm]⊢⁺ ⟨A + 6 * K + 8, 0, 0, 3 * K + 6, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * K + 2 = 0 + (2 * K + 2) from by ring]
    exact d_to_e (2 * K + 2) 0 0 (a := A + K + 2)
  · rw [show 0 + 2 * (2 * K + 2) = 0 + 4 * (K + 1) from by ring,
        show A + K + 2 = A + 1 + (K + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (e_reduce (K + 1) 0 (a := A + 1) (e := 0))
    rw [show 0 + 3 * (K + 1) = (3 * K + 2) + 1 from by ring]
    show ⟨A + 1, 0, (3 * K + 2) + 1, 0, 0⟩ [fm]⊢⁺ _
    have h := drain_e0 (a := A) (c := 3 * K + 2)
    convert h using 2; ring_nf

theorem main_odd (K : ℕ) :
    ⟨A + K + 2, 0, 0, 2 * K + 3, 0⟩ [fm]⊢⁺ ⟨A + 6 * K + 10, 0, 0, 3 * K + 6, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * K + 3 = 0 + (2 * K + 3) from by ring]
    exact d_to_e (2 * K + 3) 0 0 (a := A + K + 2)
  · rw [show 0 + 2 * (2 * K + 3) = 2 + 4 * (K + 1) from by ring,
        show A + K + 2 = A + 1 + (K + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (e_reduce (K + 1) 0 (a := A + 1) (e := 2))
    rw [show 0 + 3 * (K + 1) = (3 * K + 2) + 1 from by ring]
    show ⟨A + 1, 0, (3 * K + 2) + 1, 0, 2⟩ [fm]⊢⁺ _
    have h := drain_e2 (a := A) (c := 3 * K + 2)
    convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a ≥ d + 1 ∧ d ≥ 2)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      obtain ⟨A, rfl⟩ : ∃ A, a = A + K' + 2 := ⟨a - K' - 2, by omega⟩
      refine ⟨⟨A + 6 * K' + 8, 0, 0, 3 * K' + 6, 0⟩,
        ⟨A + 6 * K' + 8, 3 * K' + 6, rfl, by omega, by omega⟩, ?_⟩
      show ⟨A + K' + 2, 0, 0, 2 * (K' + 1), 0⟩ [fm]⊢⁺ _
      rw [show 2 * (K' + 1) = 2 * K' + 2 from by ring]
      exact main_even K'
    · subst hK
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      obtain ⟨A, rfl⟩ : ∃ A, a = A + K' + 2 := ⟨a - K' - 2, by omega⟩
      refine ⟨⟨A + 6 * K' + 10, 0, 0, 3 * K' + 6, 0⟩,
        ⟨A + 6 * K' + 10, 3 * K' + 6, rfl, by omega, by omega⟩, ?_⟩
      show ⟨A + K' + 2, 0, 0, 2 * (K' + 1) + 1, 0⟩ [fm]⊢⁺ _
      rw [show 2 * (K' + 1) + 1 = 2 * K' + 3 from by ring]
      exact main_odd K'
  · exact ⟨2, 3, rfl, by omega, by omega⟩
