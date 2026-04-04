import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1672: [77/15, 9/14, 2/3, 5/11, 1617/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1672

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- R2 drain: c=0, drains d into b. Works because c=0 means R1 doesn't fire.
theorem r2_drain : ∀ k, ∀ a B e,
    ⟨a + k, B, 0, k, e⟩ [fm]⊢* ⟨a, B + 2 * k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a B e; simp; exists 0
  | succ k ih =>
    intro a B e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (B + 2) e)
    ring_nf; finish

-- R3 chain: c=0, d=0, drains b into a
theorem r3_chain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

-- R4 chain: b=0, d=0, drains e into c
theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- One round of R2,R1,R1
theorem r2r1r1_step (a c D E : ℕ) :
    ⟨a + 1, 0, c + 2, D + 1, E⟩ [fm]⊢* ⟨a, 0, c, D + 2, E + 2⟩ := by
  rw [show D + 1 = D + 1 from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show c + 2 = (c + 1) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show c + 1 = c + 1 from rfl]
  step fm
  ring_nf; finish

-- R2R1R1 chain: k rounds
theorem r2r1r1_chain : ∀ k, ∀ a c D E,
    ⟨a + k, 0, c + 2 * k, D + 1, E⟩ [fm]⊢* ⟨a, 0, c, D + k + 1, E + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a c D E; ring_nf; finish
  | succ k ih =>
    intro a c D E
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (r2r1r1_step (a + k) (c + 2 * k) D E)
    apply stepStar_trans (ih a c (D + 1) (E + 2))
    ring_nf; finish

-- R5+R1: (A+1, 0, C+1, 0, 0) -> (A, 0, C, 3, 2)
theorem r5r1_open (A C : ℕ) :
    ⟨A + 1, 0, C + 1, 0, 0⟩ [fm]⊢⁺ ⟨A, 0, C, 3, 2⟩ := by
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show C + 1 = C + 1 from rfl]
  step fm
  ring_nf; finish

-- Tail R2+R1: (a+1, 0, 1, D+1, e) -> (a, 1, 0, D+1, e+1)
theorem tail_r2r1 (a D e : ℕ) :
    ⟨a + 1, 0, 1, D + 1, e⟩ [fm]⊢* ⟨a, 1, 0, D + 1, e + 1⟩ := by
  rw [show D + 1 = D + 1 from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨3 * n + 5, 0, 0, n + 4, 2 * n + 4⟩ [fm]⊢⁺ ⟨3 * n + 8, 0, 0, n + 5, 2 * n + 6⟩ := by
  -- Phase 1: R2 x (n+4)
  have h1 : ⟨3 * n + 5, 0, 0, n + 4, 2 * n + 4⟩ [fm]⊢*
      ⟨2 * n + 1, 2 * n + 8, 0, 0, 2 * n + 4⟩ := by
    have := r2_drain (n + 4) (2 * n + 1) 0 (2 * n + 4)
    rw [show 2 * n + 1 + (n + 4) = 3 * n + 5 from by ring,
        show 0 + 2 * (n + 4) = 2 * n + 8 from by ring] at this; exact this
  -- Phase 2: R3 x (2n+8)
  have h2 : ⟨2 * n + 1, 2 * n + 8, 0, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨4 * n + 9, 0, 0, 0, 2 * n + 4⟩ := by
    have := r3_chain (2 * n + 8) (2 * n + 1) (2 * n + 4)
    rw [show 2 * n + 1 + (2 * n + 8) = 4 * n + 9 from by ring] at this; exact this
  -- Phase 3: R4 x (2n+4)
  have h3 : ⟨4 * n + 9, 0, 0, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨4 * n + 9, 0, 2 * n + 4, 0, 0⟩ := by
    have := r4_chain (2 * n + 4) (4 * n + 9) 0
    rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring] at this; exact this
  -- Phase 4a: R5, R1
  have h4a : ⟨4 * n + 9, 0, 2 * n + 4, 0, 0⟩ [fm]⊢⁺
      ⟨4 * n + 8, 0, 2 * n + 3, 3, 2⟩ := by
    rw [show 4 * n + 9 = (4 * n + 8) + 1 from by ring,
        show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
    exact r5r1_open (4 * n + 8) (2 * n + 3)
  -- Phase 4b: R2R1R1 x (n+1)
  -- From (4n+8, 0, 2n+3, 3, 2) to (3n+7, 0, 1, n+4, 2n+4)
  -- r2r1r1_chain: (a+k, 0, c+2k, D+1, E) -> (a, 0, c, D+k+1, E+2k)
  -- k=n+1, a=3n+7, c=1, D+1=3 so D=2, E=2
  -- Result: (3n+7, 0, 1, 2+(n+1)+1, 2+2(n+1)) = (3n+7, 0, 1, n+4, 2n+4) ✓
  have h4b : ⟨4 * n + 8, 0, 2 * n + 3, 3, 2⟩ [fm]⊢*
      ⟨3 * n + 7, 0, 1, n + 4, 2 * n + 4⟩ := by
    have := r2r1r1_chain (n + 1) (3 * n + 7) 1 2 2
    rw [show 3 * n + 7 + (n + 1) = 4 * n + 8 from by ring,
        show 1 + 2 * (n + 1) = 2 * n + 3 from by ring,
        show 2 + 1 = 3 from by ring,
        show 2 + (n + 1) + 1 = n + 4 from by ring,
        show 2 + 2 * (n + 1) = 2 * n + 4 from by ring] at this; exact this
  -- Phase 4c: R2, R1 (tail for c=1)
  -- (3n+7, 0, 1, n+4, 2n+4) -> (3n+6, 1, 0, n+4, 2n+5)
  -- tail_r2r1: (a+1, 0, 1, D+1, e) -> (a, 1, 0, D+1, e+1)
  -- a+1 = 3n+7, D+1 = n+4, e = 2n+4
  -- a = 3n+6, D = n+3
  have h4c : ⟨3 * n + 7, 0, 1, n + 4, 2 * n + 4⟩ [fm]⊢*
      ⟨3 * n + 6, 1, 0, n + 4, 2 * n + 5⟩ := by
    have := tail_r2r1 (3 * n + 6) (n + 3) (2 * n + 4)
    rw [show 3 * n + 6 + 1 = 3 * n + 7 from by ring,
        show n + 3 + 1 = n + 4 from by ring,
        show n + 3 + 1 = n + 4 from by ring,
        show 2 * n + 4 + 1 = 2 * n + 5 from by ring] at this; exact this
  -- Phase 4d: R2 x (n+4) to drain d (with b=1, c=0)
  -- r2_drain: (a+k, B, 0, k, e) -> (a, B+2k, 0, 0, e)
  -- a+k = 3n+6, B = 1, k = n+4, e = 2n+5
  -- a = 3n+6-(n+4) = 2n+2
  have h4d : ⟨3 * n + 6, 1, 0, n + 4, 2 * n + 5⟩ [fm]⊢*
      ⟨2 * n + 2, 2 * n + 9, 0, 0, 2 * n + 5⟩ := by
    have := r2_drain (n + 4) (2 * n + 2) 1 (2 * n + 5)
    rw [show 2 * n + 2 + (n + 4) = 3 * n + 6 from by ring,
        show 1 + 2 * (n + 4) = 2 * n + 9 from by ring] at this; exact this
  -- Phase 5: R3 x (2n+9)
  have h5 : ⟨2 * n + 2, 2 * n + 9, 0, 0, 2 * n + 5⟩ [fm]⊢*
      ⟨4 * n + 11, 0, 0, 0, 2 * n + 5⟩ := by
    have := r3_chain (2 * n + 9) (2 * n + 2) (2 * n + 5)
    rw [show 2 * n + 2 + (2 * n + 9) = 4 * n + 11 from by ring] at this; exact this
  -- Phase 6: R4 x (2n+5)
  have h6 : ⟨4 * n + 11, 0, 0, 0, 2 * n + 5⟩ [fm]⊢*
      ⟨4 * n + 11, 0, 2 * n + 5, 0, 0⟩ := by
    have := r4_chain (2 * n + 5) (4 * n + 11) 0
    rw [show 0 + (2 * n + 5) = 2 * n + 5 from by ring] at this; exact this
  -- Phase 7a: R5, R1
  have h7a : ⟨4 * n + 11, 0, 2 * n + 5, 0, 0⟩ [fm]⊢⁺
      ⟨4 * n + 10, 0, 2 * n + 4, 3, 2⟩ := by
    rw [show 4 * n + 11 = (4 * n + 10) + 1 from by ring,
        show 2 * n + 5 = (2 * n + 4) + 1 from by ring]
    exact r5r1_open (4 * n + 10) (2 * n + 4)
  -- Phase 7b: R2R1R1 x (n+2)
  -- r2r1r1_chain: (a+k, 0, c+2k, D+1, E) -> (a, 0, c, D+k+1, E+2k)
  -- k=n+2, a=3n+8, c=0, D+1=3 so D=2, E=2
  -- Result: (3n+8, 0, 0, 2+(n+2)+1, 2+2(n+2)) = (3n+8, 0, 0, n+5, 2n+6) ✓
  have h7b : ⟨4 * n + 10, 0, 2 * n + 4, 3, 2⟩ [fm]⊢*
      ⟨3 * n + 8, 0, 0, n + 5, 2 * n + 6⟩ := by
    have := r2r1r1_chain (n + 2) (3 * n + 8) 0 2 2
    rw [show 3 * n + 8 + (n + 2) = 4 * n + 10 from by ring,
        show 0 + 2 * (n + 2) = 2 * n + 4 from by ring,
        show 2 + 1 = 3 from by ring,
        show 2 + (n + 2) + 1 = n + 5 from by ring,
        show 2 + 2 * (n + 2) = 2 * n + 6 from by ring] at this; exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus (stepStar_trans h1 (stepStar_trans h2 h3)) h4a)
    (stepStar_trans h4b (stepStar_trans h4c (stepStar_trans h4d
      (stepStar_trans h5 (stepStar_trans h6
        (stepPlus_stepStar (stepPlus_stepStar_stepPlus h7a h7b)))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 4⟩) (by execute fm 44)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 5, 0, 0, n + 4, 2 * n + 4⟩) 0
  intro n; exact ⟨n + 1, by
    rw [show 3 * (n + 1) + 5 = 3 * n + 8 from by ring,
        show (n + 1) + 4 = n + 5 from by ring,
        show 2 * (n + 1) + 4 = 2 * n + 6 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1672
