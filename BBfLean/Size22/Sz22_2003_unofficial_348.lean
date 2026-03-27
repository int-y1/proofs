import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #348: [2/15, 1/3, 1/98, 429/2, 35/11, 2/13]

Vector representation:
```
 1 -1 -1  0  0  0
 0 -1  0  0  0  0
-1  0  0 -2  0  0
-1  1  0  0  1  1
 0  0  1  1 -1  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_348

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R4,R1 chain with d=0: (1,0,j,0,e,f) ⊢* (1,0,0,0,e+j,f+j)
theorem r4r1_d0 : ∀ j e f,
    (1, 0, j, 0, e, f) [fm]⊢* (1, 0, 0, 0, e + j, f + j) := by
  intro j; induction j with
  | zero => intro e f; exists 0
  | succ j ih =>
    intro e f
    step fm; step fm
    apply stepStar_trans (ih (e + 1) (f + 1))
    ring_nf; finish

-- R4,R1 chain with d=1: (1,0,j,1,e,f) ⊢* (1,0,0,1,e+j,f+j)
theorem r4r1_d1 : ∀ j e f,
    (1, 0, j, 1, e, f) [fm]⊢* (1, 0, 0, 1, e + j, f + j) := by
  intro j; induction j with
  | zero => intro e f; exists 0
  | succ j ih =>
    intro e f
    step fm; step fm
    apply stepStar_trans (ih (e + 1) (f + 1))
    ring_nf; finish

-- R5 chain: (0,0,c,d,j,f) ⊢* (0,0,c+j,d+j,0,f)
theorem r5_chain : ∀ j c d f,
    (0, 0, c, d, j, f) [fm]⊢* (0, 0, c + j, d + j, 0, f) := by
  intro j; induction j with
  | zero => intro c d f; exists 0
  | succ j ih =>
    intro c d f
    rw [show c + (j + 1) = (c + 1) + j from by ring,
        show d + (j + 1) = (d + 1) + j from by ring]
    step fm
    exact ih (c + 1) (d + 1) f

-- R6,R3 chain: (0,0,c,d+2*j,0,f+j) ⊢* (0,0,c,d,0,f)
theorem r6r3_chain : ∀ j c d f,
    (0, 0, c, d + 2 * j, 0, f + j) [fm]⊢* (0, 0, c, d, 0, f) := by
  intro j; induction j with
  | zero => intro c d f; simp; exists 0
  | succ j ih =>
    intro c d f
    rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring,
        show f + (j + 1) = (f + j) + 1 from by ring]
    step fm; step fm
    exact ih c d f

-- Expand d=0: (0,0,c,0,0,f+1) ⊢* (0,0,0,0,c+1,c+f+1)
theorem expand_d0 (c f : ℕ) :
    (0, 0, c, 0, 0, f + 1) [fm]⊢* (0, 0, 0, 0, c + 1, c + f + 1) := by
  step fm
  apply stepStar_trans (r4r1_d0 c 0 f)
  step fm; step fm
  ring_nf; finish

-- Expand d=1: (0,0,c,1,0,f+1) ⊢* (0,0,0,1,c+1,c+f+1)
theorem expand_d1 (c f : ℕ) :
    (0, 0, c, 1, 0, f + 1) [fm]⊢* (0, 0, 0, 1, c + 1, c + f + 1) := by
  step fm
  apply stepStar_trans (r4r1_d1 c 0 f)
  step fm; step fm
  ring_nf; finish

-- R5 with first step: (0,0,0,d,n+1,f) ⊢* (0,0,n+1,d+n+1,0,f)
theorem r5_full (n d f : ℕ) :
    (0, 0, 0, d, n + 1, f) [fm]⊢* (0, 0, n + 1, d + n + 1, 0, f) := by
  step fm
  have h := r5_chain n 1 (d + 1) f
  rw [show 1 + n = n + 1 from by ring, show d + 1 + n = d + n + 1 from by ring] at h
  exact h

-- Main transition: (0,0,4k+3,0,0,f+1) ⊢⁺ (0,0,4k+7,0,0,f+8k+8)
theorem main_trans (k f : ℕ) :
    (0, 0, 4*k+3, 0, 0, f+1) [fm]⊢⁺ (0, 0, 4*k+7, 0, 0, f+8*k+8) := by
  -- Step 1: expand_d0(4k+3, f) -> (0,0,0,0,4k+4,f+4k+4)
  apply stepStar_stepPlus_stepPlus
  · have h := expand_d0 (4*k+3) f
    rw [show 4*k+3+f+1 = f+4*k+4 from by ring] at h; exact h
  -- At (0,0,0,0,4k+4,f+4k+4)
  -- Step 2: r5_full(4k+3, 0)
  apply step_stepStar_stepPlus
  · show fm (0, 0, 0, 0, (4*k+3)+1, f+4*k+4) = some (0, 0, 1, 1, 4*k+3, f+4*k+4); rfl
  apply stepStar_trans
  · exact r5_chain (4*k+3) 1 1 (f+4*k+4)
  -- At (0,0,1+(4k+3),1+(4k+3),0,f+4k+4); normalize
  rw [show 1+(4*k+3) = 4*k+4 from by ring]
  -- Step 3: r6r3(2k+2)
  apply stepStar_trans
  · have h := r6r3_chain (2*k+2) (4*k+4) 0 (f+2*k+2)
    rw [show 0+2*(2*k+2) = 4*k+4 from by ring, show f+2*k+2+(2*k+2) = f+4*k+4 from by ring] at h
    exact h
  -- At (0,0,4k+4,0,0,f+2k+2)
  -- Step 4: expand_d0(4k+4, f+2k+1)
  apply stepStar_trans
  · have h := expand_d0 (4*k+4) (f+2*k+1)
    rw [show f+2*k+1+1 = f+2*k+2 from by ring,
        show 4*k+4+(f+2*k+1)+1 = f+6*k+6 from by ring] at h; exact h
  -- At (0,0,0,0,(4k+4)+1,f+6k+6)
  rw [show (4*k+4)+1 = 4*k+5 from by ring]
  -- Step 5: r5_full(4k+4, 0)
  apply stepStar_trans
  · have h := r5_full (4*k+4) 0 (f+6*k+6)
    rw [show 0+(4*k+4)+1 = 4*k+5 from by ring] at h; exact h
  -- At (0,0,4k+5,4k+5,0,f+6k+6)
  -- Step 6: r6r3(2k+2) leaves d=1
  apply stepStar_trans
  · have h := r6r3_chain (2*k+2) (4*k+5) 1 (f+4*k+4)
    rw [show 1+2*(2*k+2) = 4*k+5 from by ring, show f+4*k+4+(2*k+2) = f+6*k+6 from by ring] at h
    exact h
  -- At (0,0,4k+5,1,0,f+4k+4)
  -- Step 7: expand_d1(4k+5, f+4k+3)
  apply stepStar_trans
  · have h := expand_d1 (4*k+5) (f+4*k+3)
    rw [show f+4*k+3+1 = f+4*k+4 from by ring,
        show 4*k+5+(f+4*k+3)+1 = f+8*k+9 from by ring] at h; exact h
  -- At (0,0,0,1,(4k+5)+1,f+8k+9)
  rw [show (4*k+5)+1 = 4*k+6 from by ring]
  -- Step 8: r5_full(4k+5, 1)
  apply stepStar_trans
  · have h := r5_full (4*k+5) 1 (f+8*k+9)
    rw [show 1+(4*k+5)+1 = 4*k+7 from by ring] at h; exact h
  -- At (0,0,4k+6,4k+7,0,f+8k+9)
  -- Step 9: r6r3(2k+3) leaves d=1
  apply stepStar_trans
  · have h := r6r3_chain (2*k+3) (4*k+6) 1 (f+6*k+6)
    rw [show 1+2*(2*k+3) = 4*k+7 from by ring, show f+6*k+6+(2*k+3) = f+8*k+9 from by ring] at h
    exact h
  -- At (0,0,4k+6,1,0,f+6k+6)
  -- Step 10: expand_d1(4k+6, f+6k+5)
  apply stepStar_trans
  · have h := expand_d1 (4*k+6) (f+6*k+5)
    rw [show f+6*k+5+1 = f+6*k+6 from by ring,
        show 4*k+6+(f+6*k+5)+1 = f+10*k+12 from by ring] at h; exact h
  -- At (0,0,0,1,(4k+6)+1,f+10k+12)
  rw [show (4*k+6)+1 = 4*k+7 from by ring]
  -- Step 11: r5_full(4k+6, 1)
  apply stepStar_trans
  · have h := r5_full (4*k+6) 1 (f+10*k+12)
    rw [show 1+(4*k+6)+1 = 4*k+8 from by ring] at h; exact h
  -- At (0,0,4k+7,4k+8,0,f+10k+12)
  -- Step 12: r6r3(2k+4) even
  have h := r6r3_chain (2*k+4) (4*k+7) 0 (f+8*k+8)
  rw [show 0+2*(2*k+4) = 4*k+8 from by ring,
      show f+8*k+8+(2*k+4) = f+10*k+12 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (0, 0, 3, 0, 0, 1))
  · execute fm 26
  apply progress_nonhalt (fm := fm) (fun c ↦ ∃ k, c = (0, 0, 4*k+3, 0, 0, 4*k^2+3*k+1))
  · intro c ⟨k, hk⟩
    subst hk
    refine ⟨(0, 0, 4*(k+1)+3, 0, 0, 4*(k+1)^2+3*(k+1)+1), ⟨k+1, rfl⟩, ?_⟩
    have h := main_trans k (4*k^2+3*k)
    conv at h => rw [show (4*k^2+3*k)+1 = 4*k^2+3*k+1 from by ring,
                      show (4*k^2+3*k)+8*k+8 = 4*(k+1)^2+3*(k+1)+1 from by ring]
    conv at h => rw [show 4*k+7 = 4*(k+1)+3 from by ring]
    exact h
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_348
