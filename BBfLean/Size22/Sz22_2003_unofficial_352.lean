import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# sz22_2003_unofficial #352: [2/15, 1/98, 429/2, 1/3, 35/11, 2/13]

Vector representation:
```
 1 -1 -1  0  0  0
-1  0  0 -2  0  0
-1  1  0  0  1  1
 0 -1  0  0  0  0
 0  0  1  1 -1  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_352

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

private theorem n_le_4nn (n : ℕ) : n ≤ 4 * n * n := by
  rcases n with _ | n <;> [omega; nlinarith [Nat.zero_le n]]

theorem e_to_cd (k c d f : ℕ) : ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c + k, d + k, 0, f⟩ := by
  induction k generalizing c d f with
  | zero => simp; exists 0
  | succ k ih =>
    step fm; apply stepStar_trans (ih (c + 1) (d + 1) f); ring_nf; finish

theorem burn_d (k c f : ℕ) : ⟨0, 0, c, 2 * k, 0, f + k⟩ [fm]⊢* ⟨0, 0, c, 0, 0, f⟩ := by
  induction k generalizing c f with
  | zero => simp; exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; exact ih c f

theorem burn_d_odd (k c f : ℕ) :
    ⟨0, 0, c, 2 * k + 1, 0, f + k⟩ [fm]⊢* ⟨0, 0, c, 1, 0, f⟩ := by
  induction k generalizing c f with
  | zero => simp; exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; exact ih c f

theorem consume_c_d1 (k c e f : ℕ) :
    ⟨0, 1, c + k, 1, e, f⟩ [fm]⊢* ⟨0, 1, c, 1, e + k, f + k⟩ := by
  induction k generalizing c e f with
  | zero => simp; exists 0
  | succ k ih =>
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (e + 1) (f + 1)); ring_nf; finish

theorem consume_c_d0 (k c e f : ℕ) :
    ⟨0, 1, c + k, 0, e, f⟩ [fm]⊢* ⟨0, 1, c, 0, e + k, f + k⟩ := by
  induction k generalizing c e f with
  | zero => simp; exists 0
  | succ k ih =>
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (e + 1) (f + 1)); ring_nf; finish

theorem subcycle_odd (k c g : ℕ) :
    ⟨0, 0, c, 2*k+1, 0, g+1+k⟩ [fm]⊢* ⟨0, 0, 0, 1, c+1, g+c+1⟩ := by
  apply stepStar_trans (burn_d_odd k c (g+1))
  step fm; step fm
  have h := consume_c_d1 c 0 1 (g+1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h; step fm; ring_nf; finish

theorem subcycle_even (k c g : ℕ) :
    ⟨0, 0, c, 2*k, 0, g+1+k⟩ [fm]⊢* ⟨0, 0, 0, 0, c+1, g+c+1⟩ := by
  apply stepStar_trans (burn_d k c (g+1))
  step fm; step fm
  have h := consume_c_d0 c 0 1 (g+1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h; step fm; ring_nf; finish

-- Helper to apply subcycle_odd with rw on the h
private theorem apply_subcycle_odd (c d f g k : ℕ)
    (hd : d = 2*k+1) (hf : f = g+1+k) :
    ⟨0, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, 0, 1, c+1, g+c+1⟩ := by
  rw [hd, hf]; exact subcycle_odd k c g

private theorem apply_subcycle_even (c d f g k : ℕ)
    (hd : d = 2*k) (hf : f = g+1+k) :
    ⟨0, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, 0, 0, c+1, g+c+1⟩ := by
  rw [hd, hf]; exact subcycle_even k c g

-- Phase 1: (0,0,0,0, 4n+1, 4n²+n+1) ⊢* (0,0,0,1, 4n+2, 4n²+3n+2)
theorem phase1 (n : ℕ) :
    ⟨0, 0, 0, 0, 4*n+1, 4*n*n+n+1⟩ [fm]⊢* ⟨0, 0, 0, 1, 4*n+2, 4*n*n+3*n+2⟩ := by
  apply stepStar_trans (e_to_cd (4*n+1) 0 0 (4*n*n+n+1))
  simp only [Nat.zero_add]
  apply stepStar_trans (apply_subcycle_odd (4*n+1) (4*n+1) (4*n*n+n+1) (4*n*n-n) (2*n)
    (by ring) (by have := n_le_4nn n; omega))
  rw [show (4*n+1)+1 = 4*n+2 from by ring,
      show (4*n*n-n)+(4*n+1)+1 = 4*n*n+3*n+2 from by have := n_le_4nn n; omega]
  finish

-- Phase 2: (0,0,0,1, 4n+2, 4n²+3n+2) ⊢* (0,0,0,1, 4n+3, 4n²+5n+3)
theorem phase2 (n : ℕ) :
    ⟨0, 0, 0, 1, 4*n+2, 4*n*n+3*n+2⟩ [fm]⊢* ⟨0, 0, 0, 1, 4*n+3, 4*n*n+5*n+3⟩ := by
  apply stepStar_trans (e_to_cd (4*n+2) 0 1 (4*n*n+3*n+2))
  simp only [Nat.zero_add]
  apply stepStar_trans (apply_subcycle_odd (4*n+2) (1+(4*n+2)) (4*n*n+3*n+2) (4*n*n+n) (2*n+1)
    (by ring) (by omega))
  rw [show (4*n+2)+1 = 4*n+3 from by ring,
      show (4*n*n+n)+(4*n+2)+1 = 4*n*n+5*n+3 from by omega]
  finish

-- Phase 3: (0,0,0,1, 4n+3, 4n²+5n+3) ⊢* (0,0,0,0, 4n+4, 4n²+7n+4)
theorem phase3 (n : ℕ) :
    ⟨0, 0, 0, 1, 4*n+3, 4*n*n+5*n+3⟩ [fm]⊢* ⟨0, 0, 0, 0, 4*n+4, 4*n*n+7*n+4⟩ := by
  apply stepStar_trans (e_to_cd (4*n+3) 0 1 (4*n*n+5*n+3))
  simp only [Nat.zero_add]
  apply stepStar_trans (apply_subcycle_even (4*n+3) (1+(4*n+3)) (4*n*n+5*n+3) (4*n*n+3*n) (2*n+2)
    (by ring) (by omega))
  rw [show (4*n+3)+1 = 4*n+4 from by ring,
      show (4*n*n+3*n)+(4*n+3)+1 = 4*n*n+7*n+4 from by omega]
  finish

-- Phase 4: (0,0,0,0, 4n+4, 4n²+7n+4) ⊢* (0,0,0,0, 4n+5, 4n²+9n+6)
theorem phase4 (n : ℕ) :
    ⟨0, 0, 0, 0, 4*n+4, 4*n*n+7*n+4⟩ [fm]⊢* ⟨0, 0, 0, 0, 4*n+5, 4*n*n+9*n+6⟩ := by
  apply stepStar_trans (e_to_cd (4*n+4) 0 0 (4*n*n+7*n+4))
  simp only [Nat.zero_add]
  apply stepStar_trans (apply_subcycle_even (4*n+4) (4*n+4) (4*n*n+7*n+4) (4*n*n+5*n+1) (2*n+2)
    (by ring) (by omega))
  rw [show (4*n+4)+1 = 4*n+5 from by ring,
      show (4*n*n+5*n+1)+(4*n+4)+1 = 4*n*n+9*n+6 from by omega]
  finish

theorem cycle (n : ℕ) :
    ⟨0, 0, 0, 0, 4*n+1, 4*n*n+n+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 4*n+5, 4*n*n+9*n+6⟩ := by
  apply stepStar_stepPlus_stepPlus (phase1 n)
  apply stepStar_stepPlus_stepPlus (phase2 n)
  apply stepStar_stepPlus_stepPlus (phase3 n)
  -- phase4 gives ⊢*, need ⊢⁺. Take first step explicitly.
  -- (0,0,0,0,4n+4,...): rule 5 fires since 4n+4 ≥ 1
  step fm
  -- Now at (0,0,1,1,4n+3,4n²+7n+4), need ⊢* to (0,0,0,0,4n+5,4n²+9n+6)
  -- This is the rest of phase4, starting from after one e_to_cd step.
  apply stepStar_trans (e_to_cd (4*n+3) 1 1 (4*n*n+7*n+4))
  rw [show 1 + (4*n+3) = 4*n+4 from by ring]
  apply stepStar_trans (apply_subcycle_even (4*n+4) (4*n+4) (4*n*n+7*n+4) (4*n*n+5*n+1) (2*n+2)
    (by ring) (by omega))
  rw [show (4*n+4)+1 = 4*n+5 from by ring,
      show (4*n*n+5*n+1)+(4*n+4)+1 = 4*n*n+9*n+6 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 0, 4*n+1, 4*n*n+n+1⟩) 0
  intro n; exact ⟨n + 1, by
    have h := cycle n
    convert h using 2
    all_goals ring_nf⟩

end Sz22_2003_unofficial_352
