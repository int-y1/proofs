import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #135: [9/35, 1/33, 50/3, 11/5, 63/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -1  0  1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_135

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R5/R2/R2 drain (even): (a+k, 0, 0, d, 2k) →* (a, 0, 0, d+k, 0)
theorem r5r2r2_drain_gen : ∀ k, ∀ a d, ⟨a+k, 0, 0, d, 2*k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem r5r2r2_drain : ∀ k, ∀ a, ⟨a+k, 0, 0, 0, 2*k⟩ [fm]⊢* ⟨a, 0, 0, k, 0⟩ := by
  intro k a; have h := r5r2r2_drain_gen k a 0; simp at h; exact h

-- R5/R2 drain (odd): (a+k+1, 0, 0, d, 2k+1) →* (a+1, 0, 2, d+k+1, 0)
theorem r5r2_drain_odd_gen : ∀ k, ∀ a d, ⟨a+k+1, 0, 0, d, 2*k+1⟩ [fm]⊢* ⟨a+1, 0, 2, d+k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem r5r2r2_drain_odd : ∀ k, ∀ a, ⟨a+k+1, 0, 0, 0, 2*k+1⟩ [fm]⊢* ⟨a+1, 0, 2, k+1, 0⟩ := by
  intro k a; have h := r5r2_drain_odd_gen k a 0; simp at h; exact h

-- R4 drain: c → e
theorem r4_drain_gen : ∀ c, ∀ a e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+c⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · exists 0
  · step fm; apply stepStar_trans (ih _ _); ring_nf; finish

theorem r4_drain : ∀ c, ∀ a, ⟨a, 0, c, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, c⟩ := by
  intro c a; have h := r4_drain_gen c a 0; simp at h; exact h

-- R3 drain: b → a, c
theorem r3_drain : ∀ b, ∀ a c, ⟨a, b, c, 0, 0⟩ [fm]⊢* ⟨a+b, 0, c+2*b, 0, 0⟩ := by
  intro b; induction' b with b ih <;> intro a c
  · exists 0
  · step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- R3/R1/R1 chain (even d)
theorem r3r1r1_chain : ∀ m, ∀ a b, ⟨a, b+1, 0, 2*m, 0⟩ [fm]⊢* ⟨a+m, b+3*m+1, 0, 0, 0⟩ := by
  intro m; induction' m with m ih <;> intro a b
  · exists 0
  · rw [show 2 * (m + 1) = 2 * m + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- R3/R1/R1 chain (odd d)
theorem r3r1r1_chain_odd : ∀ m, ∀ a b, ⟨a, b+1, 0, 2*m+1, 0⟩ [fm]⊢* ⟨a+m, b+3*m+1, 0, 1, 0⟩ := by
  intro m; induction' m with m ih <;> intro a b
  · exists 0
  · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem d1_tail : ∀ a b, ⟨a, b+1, 0, 1, 0⟩ [fm]⊢* ⟨a+2, b+1, 3, 0, 0⟩ := by
  intro a b; step fm; step fm; step fm; ring_nf; finish

-- Composed finish: even d
private theorem finish_chain_even (B : ℕ) : ∀ m, ∀ a, ⟨a, B+1, 0, 2*m, 0⟩ [fm]⊢*
    ⟨a+m+B+1+3*m, 0, 0, 0, 2*B+2+6*m⟩ := by
  intro m a
  apply stepStar_trans (c₂ := ⟨a + m, B + 3 * m + 1, 0, 0, 0⟩)
  · exact r3r1r1_chain m a B
  apply stepStar_trans (c₂ := ⟨a + m + (B + 3 * m + 1), 0, 0 + 2 * (B + 3 * m + 1), 0, 0⟩)
  · exact r3_drain (B + 3 * m + 1) (a + m) 0
  apply stepStar_trans (c₂ := ⟨a + m + (B + 3 * m + 1), 0, 0, 0, 0 + 2 * (B + 3 * m + 1)⟩)
  · exact r4_drain (0 + 2 * (B + 3 * m + 1)) (a + m + (B + 3 * m + 1))
  ring_nf; finish

-- Composed finish: odd d
private theorem finish_chain_odd (B : ℕ) : ∀ m, ∀ a, ⟨a, B+1, 0, 2*m+1, 0⟩ [fm]⊢*
    ⟨a+m+2+B+1+3*m, 0, 0, 0, 3+2*B+2+6*m⟩ := by
  intro m a
  apply stepStar_trans (c₂ := ⟨a + m, B + 3 * m + 1, 0, 1, 0⟩)
  · exact r3r1r1_chain_odd m a B
  apply stepStar_trans (c₂ := ⟨a + m + 2, B + 3 * m + 1, 3, 0, 0⟩)
  · exact d1_tail (a + m) (B + 3 * m)
  apply stepStar_trans (c₂ := ⟨a + m + 2 + (B + 3 * m + 1), 0, 3 + 2 * (B + 3 * m + 1), 0, 0⟩)
  · exact r3_drain (B + 3 * m + 1) (a + m + 2) 3
  apply stepStar_trans (c₂ := ⟨a + m + 2 + (B + 3 * m + 1), 0, 0, 0, 3 + 2 * (B + 3 * m + 1)⟩)
  · exact r4_drain (3 + 2 * (B + 3 * m + 1)) (a + m + 2 + (B + 3 * m + 1))
  ring_nf; finish

-- D odd expansion
theorem exp_c0_Dodd : ∀ m, ∀ a, ⟨a+1, 0, 0, 2*m+1, 0⟩ [fm]⊢⁺ ⟨a+4*m+6, 0, 0, 0, 6*m+10⟩ := by
  intro m a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 2 * m + 1, 0⟩ = some ⟨a, 2, 0, 2 * m + 2, 0⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a + 1, 5, 0, 2 * m, 0⟩)
  · step fm; step fm; step fm; ring_nf; finish
  have h := finish_chain_even 4 m (a + 1)
  apply stepStar_trans h; ring_nf; finish

-- D even expansion
theorem exp_c0_Deven : ∀ m, ∀ a, ⟨a+1, 0, 0, 2*m+2, 0⟩ [fm]⊢⁺ ⟨a+4*m+8, 0, 0, 0, 6*m+13⟩ := by
  intro m a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 2 * m + 2, 0⟩ = some ⟨a, 2, 0, 2 * m + 3, 0⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a + 1, 5, 0, 2 * m + 1, 0⟩)
  · step fm; step fm; step fm; ring_nf; finish
  have h := finish_chain_odd 4 m (a + 1)
  apply stepStar_trans h; ring_nf; finish

-- Main expansion: (a+1, 0, 0, d+1, 0) →+ (a+2d+6, 0, 0, 0, 3d+10)
theorem main_expansion : ∀ d, ∀ a, ⟨a+1, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨a+2*d+6, 0, 0, 0, 3*d+10⟩ := by
  intro d a
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := exp_c0_Dodd m a
    convert h using 2; ring_nf
  · subst hm
    have h := exp_c0_Deven m a
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring] at h
    convert h using 2; ring_nf

theorem exp_c2_d1 : ∀ a, ⟨a, 0, 2, 1, 0⟩ [fm]⊢* ⟨a+2, 0, 0, 0, 5⟩ := by
  intro a; step fm; step fm; step fm
  apply stepStar_trans (r4_drain 5 (a + 2)); ring_nf; finish

-- c=2, D even
theorem exp_c2_Deven : ∀ m, ∀ a, ⟨a, 0, 2, 2*m+2, 0⟩ [fm]⊢* ⟨a+4*m+4, 0, 0, 0, 6*m+8⟩ := by
  intro m a
  apply stepStar_trans (c₂ := ⟨a, 4, 0, 2 * m, 0⟩)
  · rw [show 2 * m + 2 = (2 * m) + 2 from by ring]; step fm; step fm; ring_nf; finish
  have h := finish_chain_even 3 m a
  apply stepStar_trans h; ring_nf; finish

-- c=2, D odd
theorem exp_c2_Dodd : ∀ m, ∀ a, ⟨a, 0, 2, 2*m+3, 0⟩ [fm]⊢* ⟨a+4*m+6, 0, 0, 0, 6*m+11⟩ := by
  intro m a
  apply stepStar_trans (c₂ := ⟨a, 4, 0, 2 * m + 1, 0⟩)
  · rw [show 2 * m + 3 = (2 * m + 1) + 2 from by ring]; step fm; step fm; ring_nf; finish
  have h := finish_chain_odd 3 m a
  apply stepStar_trans h; ring_nf; finish

-- Full c=2 expansion: (a, 0, 2, d+1, 0) →* (a+2d+2, 0, 0, 0, 3d+5)
theorem exp_c2 : ∀ d, ∀ a, ⟨a, 0, 2, d+1, 0⟩ [fm]⊢* ⟨a+2*d+2, 0, 0, 0, 3*d+5⟩ := by
  intro d a
  rcases d with _ | d'
  · have h := exp_c2_d1 a
    convert h using 2
  · rcases Nat.even_or_odd d' with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have h := exp_c2_Deven m a
      have : m + m + 1 + 1 = 2 * m + 2 := by ring
      rw [this]
      convert h using 2; ring_nf
    · subst hm
      have h := exp_c2_Dodd m a
      have : 2 * m + 1 + 1 + 1 = 2 * m + 3 := by ring
      rw [this]
      convert h using 2; ring_nf

-- Even E transition: drain + c0 expansion
theorem trans_even : ∀ K, ∀ A, ⟨A+K+2, 0, 0, 0, 2*K+2⟩ [fm]⊢⁺ ⟨A+2*K+6, 0, 0, 0, 3*K+10⟩ := by
  intro K A
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A + 1, 0, 0, K + 1, 0⟩)
  · have h := r5r2r2_drain (K + 1) (A + 1)
    rw [show (A + 1) + (K + 1) = A + K + 2 from by ring,
        show 2 * (K + 1) = 2 * K + 2 from by ring] at h; exact h
  have h := main_expansion K A; convert h using 2

-- Odd E transition: drain_odd + c2 expansion
theorem trans_odd : ∀ K, ∀ A, ⟨A+K+1, 0, 0, 0, 2*K+1⟩ [fm]⊢⁺ ⟨A+2*K+3, 0, 0, 0, 3*K+5⟩ := by
  intro K A
  apply stepStar_stepPlus (h₂ := by simp [Q]; omega)
  apply stepStar_trans (c₂ := ⟨A + 1, 0, 2, K + 1, 0⟩)
  · have h := r5r2r2_drain_odd K A
    rw [show A + K + 1 = A + K + 1 from rfl,
        show 2 * K + 1 = 2 * K + 1 from rfl] at h; exact h
  have h := exp_c2 K (A + 1)
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 7⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = ⟨A + 1, 0, 0, 0, E + 1⟩ ∧ 2 * (A + 1) ≥ E + 2)
  · intro q ⟨A, E, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd (E + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · have hK1 : K ≥ 1 := by omega
      obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le hK1
      refine ⟨⟨A + K' + 5, 0, 0, 0, 3 * K' + 10⟩,
              ⟨A + K' + 4, 3 * K' + 9, rfl, by omega⟩, ?_⟩
      have h := trans_even K' (A - K' - 1)
      rw [show A - K' - 1 + K' + 2 = A + 1 from by omega,
          show A - K' - 1 + 2 * K' + 6 = A + K' + 5 from by omega] at h
      have : E + 1 = 2 * K' + 2 := by omega
      rw [this]; exact h
    · refine ⟨⟨A + K + 3, 0, 0, 0, 3 * K + 5⟩,
              ⟨A + K + 2, 3 * K + 4, rfl, by omega⟩, ?_⟩
      have h := trans_odd K (A - K)
      rw [show A - K + K + 1 = A + 1 from by omega,
          show A - K + 2 * K + 3 = A + K + 3 from by omega] at h
      have : E + 1 = 2 * K + 1 := by omega
      rw [this]; exact h
  · exact ⟨3, 6, rfl, by omega⟩

end Sz21_140_unofficial_135
