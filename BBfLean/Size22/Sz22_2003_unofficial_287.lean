import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #287: [14/15, 9/22, 125/2, 11/7, 9/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_287

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r2_chain : ∀ k a b d e, ⟨a+k, b, 0, d, e+k⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _ _); ring_nf; finish

theorem tail_cleanup : ∀ b, ∀ a d, ⟨a+1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2*b+3*(a+1), d+b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | _ | _ | b
  · have h := a_to_c (a+1) 0 0 d
    simp only [Nat.zero_add, show (0 : ℕ) + 3 * (a + 1) = 3 * (a + 1) from by ring] at h
    simp only [show 2 * 0 + 3 * (a + 1) = 3 * (a + 1) from by ring, show d + 0 = d from by ring]
    exact h
  · step fm; step fm
    show ⟨a+1, 0, 2, d+1, 0⟩ [fm]⊢* ⟨0, 0, 2+3*(a+1), d+1, 0⟩
    have h := a_to_c (a+1) 0 2 (d+1)
    simp only [Nat.zero_add] at h; exact h
  · step fm; step fm; step fm
    show ⟨a+2, 0, 1, d+2, 0⟩ [fm]⊢* ⟨0, 0, 4+3*(a+1), d+2, 0⟩
    have h := a_to_c (a+2) 0 1 (d+2)
    simp only [Nat.zero_add, show 1 + 3 * (a + 2) = 4 + 3 * (a + 1) from by ring] at h
    exact h
  · step fm; step fm; step fm; step fm
    show ⟨a+3, b, 0, d+3, 0⟩ [fm]⊢* ⟨0, 0, 2*(b+3)+3*(a+1), d+(b+3), 0⟩
    have h := ih b (by omega) (a+2) (d+3)
    simp only [show (a+2)+1 = a+3 from by ring,
               show 2*b+3*((a+2)+1) = 2*(b+3)+3*(a+1) from by ring,
               show (d+3)+b = d+(b+3) from by ring] at h
    exact h

-- Helper: compose r2_chain and tail_cleanup for the c=0 base case
private theorem process_c0 (j d : ℕ) :
    ⟨j+d+3, 0, 0, 2*j+2*d+4, d+1⟩ [fm]⊢* ⟨0, 0, 3*j+4*d+10, 2*j+4*d+6, 0⟩ := by
  have hr := r2_chain (d+1) (j+2) 0 (2*j+2*d+4) 0
  simp only [show 0+2*(d+1) = 2*d+2 from by ring] at hr
  have ht := tail_cleanup (2*d+2) (j+1) (2*j+2*d+4)
  simp only [show (j+1)+1 = j+2 from by ring] at ht
  have h := stepStar_trans hr ht
  convert h using 2 <;> ring_nf

-- Helper: compose R2, R1, r2_chain, tail_cleanup for the c=1 base case
private theorem process_c1 (j d : ℕ) :
    ⟨j+d+2, 0, 1, 2*j+2*d+2, d+1⟩ [fm]⊢* ⟨0, 0, 3*j+4*d+8, 2*j+4*d+4, 0⟩ := by
  rw [show j+d+2 = (j+d+1)+1 from by ring,
      show 2*j+2*d+2 = (2*j+2*d+1)+1 from by ring,
      show (1:ℕ) = 0+1 from by ring]
  step fm  -- R2
  rw [show j+d+1 = (j+d)+1 from by ring,
      show 2*j+2*d+1 = (2*j+2*d)+1 from by ring]
  step fm  -- R1
  have hr := r2_chain d (j+2) 1 (2*j+2*d+3) 0
  simp only [show 1+2*d = 2*d+1 from by ring] at hr
  have ht := tail_cleanup (2*d+1) (j+1) (2*j+2*d+3)
  simp only [show (j+1)+1 = j+2 from by ring] at ht
  have h := stepStar_trans hr ht
  convert h using 2 <;> ring_nf

-- (a+2, 0, c, 2*a+2, d) ->* (0, 0, c+3*a+d+6, 2*a+2*d+2, 0)
-- with a+1 ≥ d
set_option maxRecDepth 512 in
private theorem process : ∀ n, ∀ a c d, c + d ≤ n → c + a ≥ d →
    ⟨a+2, 0, c, 2*a+2, d⟩ [fm]⊢* ⟨0, 0, c+3*a+d+6, 2*a+2*d+2, 0⟩ := by
  intro n; induction' n using Nat.strongRecOn with n IH; intro a c d hle hge
  match d, c with
  | 0, c =>
    have h := a_to_c (a+2) 0 c (2*a+2)
    simp only [Nat.zero_add] at h
    convert h using 2 <;> ring
  | d+1, 0 =>
    -- c=0: a ≥ d+1 (from 0 + a ≥ d+1, i.e., a ≥ d+1)
    obtain ⟨j, rfl⟩ : ∃ j, a = d + 1 + j := ⟨a - d - 1, by omega⟩
    have h := process_c0 j d
    convert h using 2 <;> ring_nf
  | d+1, 1 =>
    -- c=1: 1 + a ≥ d+1, i.e., a ≥ d
    obtain ⟨j, rfl⟩ : ∃ j, a = d + j := ⟨a - d, by omega⟩
    have h := process_c1 j d
    convert h using 2 <;> ring_nf
  | d+1, c+2 =>
    rw [show a+2 = (a+1)+1 from by ring,
        show c+2 = (c+1)+1 from by ring,
        show 2*a+2 = (2*a+1)+1 from by ring]
    step fm; step fm; step fm
    have h := IH (c+d) (by omega) (a+1) c d (by omega) (by omega)
    convert h using 2 <;> ring_nf

theorem main_trans (d m : ℕ) (hm : m ≥ 3) :
    ⟨0, 0, d+m, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*d+m+3, 2*d+2, 0⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e d (d+m'+3) 0 0
    simp only [Nat.zero_add] at h; exact h
  simp only [show d+(m'+3) = (d+m'+2)+1 from by ring,
             show 2*d+(m'+3)+3 = 2*d+m'+6 from by ring]
  step fm
  rw [show d+m'+2 = (d+m'+1)+1 from by ring]
  step fm
  rw [show d+m'+1 = (d+m')+1 from by ring]
  step fm
  have h := process (d+m'+d) 0 (d+m') d (by omega) (by omega)
  convert h using 2 <;> ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d m, q = ⟨0, 0, d + m, d, 0⟩ ∧ m ≥ 3)
  · intro c ⟨d, m, hq, hm⟩; subst hq
    exact ⟨⟨0, 0, 2*d+m+3, 2*d+2, 0⟩,
           ⟨2*d+2, m+1, by ring_nf, by omega⟩,
           main_trans d m hm⟩
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_287
