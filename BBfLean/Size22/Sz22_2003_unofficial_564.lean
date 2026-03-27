import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #564: [35/18, 4/55, 33/2, 3/7, 10/11]

Vector representation:
```
-1 -2  1  1  0
 2  0 -1  0 -1
-1  1  0  0  1
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states: (n+2, 0, 0, 2*n+2, 0) for n >= 0.
Each transition decomposes into: opening chain, R4 drain, R5+R1+R2 pivot,
R1+R1+R2 chain, endgame (mod-4 case split), and closing chain.
-/

namespace Sz22_2003_unofficial_564

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R2 step helpers: match can't reduce when first component is a variable sum
theorem r2_step_b0 (a c d e : ℕ) : ⟨a, 0, c+1, d, e+1⟩ [fm]⊢ ⟨a+2, 0, c, d, e⟩ := by
  rcases a with _ | a <;> rfl

theorem r2_step_b1 (a c d e : ℕ) : ⟨a, 1, c+1, d, e+1⟩ [fm]⊢ ⟨a+2, 1, c, d, e⟩ := by
  rcases a with _ | a <;> rfl

-- Opening chain: k rounds of (R3, R3, R1, R2)
theorem opening_chain : ∀ k a d e, ⟨a+k+2, 0, 0, d, e⟩ [fm]⊢* ⟨a+2, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show a + (k + 1) + 2 = (a + k + 2) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (step_stepStar (r2_step_b0 (a+k) 0 (d+1) (e+1)))
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R4 drain: convert d to b
theorem r4_drain (e : ℕ) : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; apply stepStar_trans (h _ _); ring_nf; finish

-- R5+R1+R2 pivot
theorem r5r1r2_pivot {b e : ℕ} : ⟨0, b+2, 0, 0, e+2⟩ [fm]⊢* ⟨2, b, 1, 1, e⟩ := by
  step fm; step fm; step fm; finish

-- R1,R1,R2 chain: k rounds
theorem r1r1r2_chain : ∀ k c d e,
    ⟨2, (b:ℕ)+4*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R2 drain with b=0
theorem r2_drain_b0 (d : ℕ) : ∀ k a c,
    ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = c + k + 1 from by ring]
  apply stepStar_trans (step_stepStar (r2_step_b0 a (c+k) d k))
  apply stepStar_trans (h _ _); ring_nf; finish

-- R2 drain with b=1
theorem r2_drain_b1 (d : ℕ) : ∀ k a c,
    ⟨a, 1, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 1, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = c + k + 1 from by ring]
  apply stepStar_trans (step_stepStar (r2_step_b1 a (c+k) d k))
  apply stepStar_trans (h _ _); ring_nf; finish

-- b=1 to b=0 conversion: R3, R1, R2
theorem b1_to_b0 {a c d : ℕ} : ⟨a+2, 1, c, d, 0⟩ [fm]⊢* ⟨a+2, 0, c, d+1, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (step_stepStar (r2_step_b0 a c (d+1) 0)); finish

-- Closing chain: each round (R3, R2, R3, R1, R2) converts one c to d
theorem closing_chain : ∀ k a d,
    ⟨a+1, 0, k, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show a + 1 = (a + 0) + 1 from by ring]
  step fm
  apply stepStar_trans (step_stepStar (r2_step_b1 a k d 0))
  step fm; step fm
  apply stepStar_trans (step_stepStar (r2_step_b0 a k (d+1) 0))
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h (a+1) (d+1)); ring_nf; finish

-- n = 4*m: (4m+2, 0, 0, 8m+2, 0) ⊢* (4m+3, 0, 0, 8m+4, 0)
theorem trans_mod0_star (m : ℕ) :
    ⟨4*m+2, 0, 0, 8*m+2, 0⟩ [fm]⊢* ⟨4*m+3, 0, 0, 8*m+4, 0⟩ := by
  rw [show (4:ℕ)*m+2 = 0+(4*m)+2 from by ring]
  apply stepStar_trans (opening_chain (4*m) 0 (8*m+2) 0)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (8:ℕ)*m + 2 + (4*m) = 0 + (12*m + 2) from by ring,
      show (4:ℕ)*m + 1 + 1 = 4*m + 2 from by ring]
  apply stepStar_trans (r4_drain (4*m+2) (12*m+2) 2 0)
  rw [show (0:ℕ)+2+(12*m+2) = (12*m+2)+2 from by ring,
      show (4:ℕ)*m+2 = (4*m)+2 from by ring]
  apply stepStar_trans r5r1r2_pivot
  rw [show (12:ℕ)*m+2 = 2+4*(3*m) from by ring,
      show (4:ℕ)*m = m+(3*m) from by ring]
  apply stepStar_trans (r1r1r2_chain (3*m) 1 1 m)
  step fm
  rw [show 1 + 2 * ((3:ℕ)*m) + 1 = 6*m+2 from by ring,
      show 1 + (3:ℕ)*m + 1 = (2*m+2)+m from by ring]
  apply stepStar_trans (r2_drain_b0 (6*m+2) m 1 (2*m+2))
  rw [show (1:ℕ) + 2*m = (2*m+0)+1 from by ring]
  apply stepStar_trans (closing_chain (2*m+2) (2*m+0) (6*m+2))
  ring_nf; finish

-- n = 4*m+1: (4m+3, 0, 0, 8m+4, 0) ⊢* (4m+4, 0, 0, 8m+6, 0)
theorem trans_mod1_star (m : ℕ) :
    ⟨4*m+3, 0, 0, 8*m+4, 0⟩ [fm]⊢* ⟨4*m+4, 0, 0, 8*m+6, 0⟩ := by
  rw [show (4:ℕ)*m+3 = 0+(4*m+1)+2 from by ring]
  apply stepStar_trans (opening_chain (4*m+1) 0 (8*m+4) 0)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (8:ℕ)*m + 4 + (4*m+1) = 0 + (12*m + 5) from by ring,
      show (4:ℕ)*m + 1 + 1 + 1 = 4*m + 3 from by ring]
  apply stepStar_trans (r4_drain (4*m+3) (12*m+5) 2 0)
  rw [show (0:ℕ)+2+(12*m+5) = (12*m+5)+2 from by ring,
      show (4:ℕ)*m+3 = (4*m+1)+2 from by ring]
  apply stepStar_trans r5r1r2_pivot
  rw [show (12:ℕ)*m+5 = 1+4*(3*m+1) from by ring,
      show (4:ℕ)*m+1 = m+(3*m+1) from by ring]
  apply stepStar_trans (r1r1r2_chain (3*m+1) 1 1 m)
  rw [show 1 + ((3:ℕ)*m+1) = (2*m+2)+m from by ring,
      show 1 + 2*((3:ℕ)*m+1) = 6*m+3 from by ring]
  apply stepStar_trans (r2_drain_b1 (6*m+3) m 2 (2*m+2))
  rw [show (2:ℕ)+2*m = (2*m+0)+2 from by ring,
      show (2:ℕ)*m+0+2 = (2*m+0)+2 from by ring]
  apply stepStar_trans b1_to_b0
  rw [show (2:ℕ)*m+0+2 = (2*m+1)+1 from by ring]
  apply stepStar_trans (closing_chain (2*m+2) (2*m+1) (6*m+4))
  ring_nf; finish

-- n = 4*m+2: (4m+4, 0, 0, 8m+6, 0) ⊢* (4m+5, 0, 0, 8m+8, 0)
theorem trans_mod2_star (m : ℕ) :
    ⟨4*m+4, 0, 0, 8*m+6, 0⟩ [fm]⊢* ⟨4*m+5, 0, 0, 8*m+8, 0⟩ := by
  rw [show (4:ℕ)*m+4 = 0+(4*m+2)+2 from by ring]
  apply stepStar_trans (opening_chain (4*m+2) 0 (8*m+6) 0)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (8:ℕ)*m + 6 + (4*m+2) = 0 + (12*m + 8) from by ring,
      show (4:ℕ)*m + 2 + 1 + 1 = 4*m + 4 from by ring]
  apply stepStar_trans (r4_drain (4*m+4) (12*m+8) 2 0)
  rw [show (0:ℕ)+2+(12*m+8) = (12*m+8)+2 from by ring,
      show (4:ℕ)*m+4 = (4*m+2)+2 from by ring]
  apply stepStar_trans r5r1r2_pivot
  rw [show (12:ℕ)*m+8 = 0+4*(3*m+2) from by ring,
      show (4:ℕ)*m+2 = m+(3*m+2) from by ring]
  apply stepStar_trans (r1r1r2_chain (3*m+2) 1 1 m)
  rw [show 1 + ((3:ℕ)*m+2) = (2*m+3)+m from by ring,
      show 1 + 2*((3:ℕ)*m+2) = 6*m+5 from by ring]
  apply stepStar_trans (r2_drain_b0 (6*m+5) m 2 (2*m+3))
  rw [show (2:ℕ)+2*m = (2*m+1)+1 from by ring]
  apply stepStar_trans (closing_chain (2*m+3) (2*m+1) (6*m+5))
  ring_nf; finish

-- n = 4*m+3: (4m+5, 0, 0, 8m+8, 0) ⊢* (4m+6, 0, 0, 8m+10, 0)
theorem trans_mod3_star (m : ℕ) :
    ⟨4*m+5, 0, 0, 8*m+8, 0⟩ [fm]⊢* ⟨4*m+6, 0, 0, 8*m+10, 0⟩ := by
  rw [show (4:ℕ)*m+5 = 0+(4*m+3)+2 from by ring]
  apply stepStar_trans (opening_chain (4*m+3) 0 (8*m+8) 0)
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show (8:ℕ)*m + 8 + (4*m+3) = 0 + (12*m + 11) from by ring,
      show (4:ℕ)*m + 3 + 1 + 1 = 4*m + 5 from by ring]
  apply stepStar_trans (r4_drain (4*m+5) (12*m+11) 2 0)
  rw [show (0:ℕ)+2+(12*m+11) = (12*m+11)+2 from by ring,
      show (4:ℕ)*m+5 = (4*m+3)+2 from by ring]
  apply stepStar_trans r5r1r2_pivot
  rw [show (12:ℕ)*m+11 = 3+4*(3*m+2) from by ring,
      show (4:ℕ)*m+3 = (m+1)+(3*m+2) from by ring]
  apply stepStar_trans (r1r1r2_chain (3*m+2) 1 1 (m+1))
  rw [show 1 + ((3:ℕ)*m+2) = (2*m+2)+(m+1) from by ring,
      show 1 + 2*((3:ℕ)*m+2) = 6*m+5 from by ring]
  -- State: (2, 3, (2m+2)+(m+1), 6m+5, m+1). R1 fires (a=2>=1, b=3>=2).
  step fm
  -- After R1: (1, 1, (2m+2)+(m+1)+1, 6m+6, m+1)
  rw [show (2:ℕ)*m+2+(m+1)+1 = (2*m+3)+(m+1) from by ring]
  apply stepStar_trans (r2_drain_b1 (6*m+6) (m+1) 1 (2*m+3))
  rw [show (1:ℕ)+2*(m+1) = (2*m+1)+2 from by ring]
  apply stepStar_trans b1_to_b0
  rw [show (2:ℕ)*m+1+2 = (2*m+2)+1 from by ring]
  apply stepStar_trans (closing_chain (2*m+3) (2*m+2) (6*m+7))
  ring_nf; finish

-- Helper to convert ⊢* to ⊢⁺ when states clearly differ
theorem trans_mod0 (m : ℕ) :
    ⟨4*m+2, 0, 0, 8*m+2, 0⟩ [fm]⊢⁺ ⟨4*m+3, 0, 0, 8*m+4, 0⟩ :=
  stepStar_stepPlus (trans_mod0_star m) (by simp [Q])

theorem trans_mod1 (m : ℕ) :
    ⟨4*m+3, 0, 0, 8*m+4, 0⟩ [fm]⊢⁺ ⟨4*m+4, 0, 0, 8*m+6, 0⟩ :=
  stepStar_stepPlus (trans_mod1_star m) (by simp [Q])

theorem trans_mod2 (m : ℕ) :
    ⟨4*m+4, 0, 0, 8*m+6, 0⟩ [fm]⊢⁺ ⟨4*m+5, 0, 0, 8*m+8, 0⟩ :=
  stepStar_stepPlus (trans_mod2_star m) (by simp [Q])

theorem trans_mod3 (m : ℕ) :
    ⟨4*m+5, 0, 0, 8*m+8, 0⟩ [fm]⊢⁺ ⟨4*m+6, 0, 0, 8*m+10, 0⟩ :=
  stepStar_stepPlus (trans_mod3_star m) (by simp [Q])

-- Main transition: dispatch on n mod 4
theorem main_trans (n : ℕ) :
    ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩
    · subst hM; subst hK
      rw [show M+M+(M+M)+2 = 4*M+2 from by ring,
          show 2*(M+M+(M+M))+2 = 8*M+2 from by ring,
          show M+M+(M+M)+3 = 4*M+3 from by ring,
          show 2*(M+M+(M+M))+4 = 8*M+4 from by ring]
      exact trans_mod0 M
    · subst hM; subst hK
      rw [show (2*M+1)+(2*M+1)+2 = 4*M+4 from by ring,
          show 2*((2*M+1)+(2*M+1))+2 = 8*M+6 from by ring,
          show (2*M+1)+(2*M+1)+3 = 4*M+5 from by ring,
          show 2*((2*M+1)+(2*M+1))+4 = 8*M+8 from by ring]
      exact trans_mod2 M
  · rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩
    · subst hM; subst hK
      rw [show 2*(M+M)+1+2 = 4*M+3 from by ring,
          show 2*(2*(M+M)+1)+2 = 8*M+4 from by ring,
          show 2*(M+M)+1+3 = 4*M+4 from by ring,
          show 2*(2*(M+M)+1)+4 = 8*M+6 from by ring]
      exact trans_mod1 M
    · subst hM; subst hK
      rw [show 2*(2*M+1)+1+2 = 4*M+5 from by ring,
          show 2*(2*(2*M+1)+1)+2 = 8*M+8 from by ring,
          show 2*(2*M+1)+1+3 = 4*M+6 from by ring,
          show 2*(2*(2*M+1)+1)+4 = 8*M+10 from by ring]
      exact trans_mod3 M

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_564
