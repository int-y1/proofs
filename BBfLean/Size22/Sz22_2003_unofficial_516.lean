import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #516: [28/15, 3/22, 65/2, 11/7, 98/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 1  0  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_516

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+2, e, f⟩
  | _ => none

-- R3 repeated: (a+k, 0, c, d, 0, f) →* (a, 0, c+k, d, 0, f+k)
theorem r3_chain (d : ℕ) : ∀ k a c f, (⟨a+k, 0, c, d, 0, f⟩ : Q) [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a c f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: (0, 0, c, d+k, e, f) →* (0, 0, c, d, e+k, f)
theorem r4_chain (c f : ℕ) : ∀ k d e, (⟨0, 0, c, d+k, e, f⟩ : Q) [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2+R1 interleaved: (k+1, 0, j, k+2, e+j, f) →* (k+j+1, 0, 0, k+j+2, e, f)
theorem r2r1_chain (f : ℕ) : ∀ j k e, (⟨k+1, 0, j, k+2, e+j, f⟩ : Q) [fm]⊢* ⟨k+j+1, 0, 0, k+j+2, e, f⟩ := by
  intro j; induction' j with j h <;> intro k e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2 drain: (a+k, b, 0, d, k, f) →* (a, b+k, 0, d, 0, f)
theorem r2_drain (d f : ℕ) : ∀ k a b, (⟨a+k, b, 0, d, k, f⟩ : Q) [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3+R1 chain: (a+1, b+k, 0, d, 0, f) →* (a+k+1, b, 0, d+k, 0, f+k)
theorem r3r1_chain (b : ℕ) : ∀ k a d f, (⟨a+1, b+k, 0, d, 0, f⟩ : Q) [fm]⊢* ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Full cycle: compose all 6 phases
theorem full_cycle (n : ℕ) : (⟨n+3, 0, 0, 2*n+4, 0, n*n+2*n⟩ : Q) [fm]⊢⁺
    ⟨n+4, 0, 0, 2*n+6, 0, n*n+4*n+3⟩ := by
  -- Phase 1: R3 x (n+3): (n+3,0,0,2n+4,0,n²+2n) →* (0,0,n+3,2n+4,0,n²+3n+3)
  have p1 := r3_chain (2*n+4) (n+3) 0 0 (n*n+2*n)
  simp only [Nat.zero_add] at p1
  -- Phase 2: R4 x (2n+4): (0,0,n+3,2n+4,0,n²+3n+3) →* (0,0,n+3,0,2n+4,n²+3n+3)
  have p2 := r4_chain (n+3) (n*n+2*n+(n+3)) (2*n+4) 0 0
  simp only [Nat.zero_add] at p2
  -- Phase 3: R5: (0,0,n+3,0,2n+4,n²+3n+3) →⁺ (1,0,n+3,2,2n+4,n²+3n+2)
  -- note: n²+3n+3 = (n²+3n+2) + 1
  have p3 : (⟨0, 0, n+3, 0, 2*n+4, (n*n+3*n+2)+1⟩ : Q) [fm]⊢⁺ ⟨1, 0, n+3, 2, 2*n+4, n*n+3*n+2⟩ := by
    step fm; finish
  -- Phase 4: R2+R1: (1,0,n+3,2,2n+4,n²+3n+2) →* (n+4,0,0,n+5,n+1,n²+3n+2)
  -- r2r1_chain: (k+1,0,j,k+2,e+j,f) →* (k+j+1,0,0,k+j+2,e,f) with k=0,j=n+3,e=n+1
  have p4 := r2r1_chain (n*n+3*n+2) (n+3) 0 (n+1)
  simp only [Nat.zero_add] at p4
  -- Phase 5: R2 drain: (n+4,0,0,n+5,n+1,n²+3n+2) →* (3,n+1,0,n+5,0,n²+3n+2)
  -- r2_drain: (a+k,b,0,d,k,f) →* (a,b+k,0,d,0,f) with a=3,k=n+1,b=0
  have p5 := r2_drain (n+5) (n*n+3*n+2) (n+1) 3 0
  simp only [Nat.zero_add] at p5
  -- Phase 6: R3+R1: (3,n+1,0,n+5,0,n²+3n+2) →* (n+4,0,0,2n+6,0,n²+4n+3)
  -- r3r1_chain: (a+1,b+k,0,d,0,f) →* (a+k+1,b,0,d+k,0,f+k) with a=2,b=0,k=n+1
  have p6 := r3r1_chain 0 (n+1) 2 (n+5) (n*n+3*n+2)
  simp only [Nat.zero_add] at p6
  -- Compose: p1 (⊢*) + p2 (⊢*) + p3 (⊢⁺) + p4 (⊢*) + p5 (⊢*) + p6 (⊢*)
  -- Rewrite p2 source to match p1 target
  have p12 : (⟨n+3, 0, 0, 2*n+4, 0, n*n+2*n⟩ : Q) [fm]⊢* ⟨0, 0, n+3, 0, 2*n+4, n*n+2*n+(n+3)⟩ :=
    stepStar_trans p1 p2
  -- Chain p12 with p3
  rw [show n*n+2*n+(n+3) = n*n+3*n+2+1 from by ring] at p12
  apply stepStar_stepPlus_stepPlus p12
  apply stepPlus_stepStar_stepPlus p3
  -- Chain p4: need (1,0,n+3,2,(n+1)+(n+3),_) form
  rw [show 2*n+4 = (n+1)+(n+3) from by ring]
  apply stepStar_trans p4
  -- Chain p5: need (3+(n+1),0,0,n+5,n+1,_) form
  rw [show n+3+1 = 3+(n+1) from by ring, show n+3+2 = n+5 from by ring]
  apply stepStar_trans p5
  -- Chain p6: need (2+1,0+(n+1),0,n+5,0,_) form
  rw [show (3 : ℕ) = 2+1 from by ring]
  apply stepStar_trans p6
  -- Close with ring_nf
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 4, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+3, 0, 0, 2*n+4, 0, n*n+2*n⟩) 0
  intro n; refine ⟨n+1, ?_⟩
  have h := full_cycle n
  convert h using 2; all_goals ring_nf

end Sz22_2003_unofficial_516
