import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #125: [1/45, 10/77, 49/5, 3/7, 6655/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0  1 -1 -1
 0  0 -1  2  0
 0  1  0 -1  0
-1  0  1  0  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_125

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+3⟩
  | _ => none

theorem r5r1_chain : ∀ k a b e,
    (⟨a+k, b+2*k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, b, 0, 0, e+3*k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a b (e + 3))
    rw [show e + 3 + 3 * k = e + 3 * (k + 1) from by ring]; finish

theorem r5_r3_b0 : ∀ a e,
    (⟨a+1, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 2, e+3⟩ := by
  intro a e; step fm; step fm; finish

theorem r5_r3_b1 : ∀ a e,
    (⟨a+1, 1, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, 1, 0, 2, e+3⟩ := by
  intro a e; step fm; step fm; finish

theorem r2r2r3_step_b0 : ∀ a c e,
    (⟨a, 0, c, 2, e+2⟩ : Q) [fm]⊢* ⟨a+2, 0, c+1, 2, e⟩ := by
  intro a c e; step fm; step fm; step fm; finish

theorem r2r2r3_step_b1 : ∀ a c e,
    (⟨a, 1, c, 2, e+2⟩ : Q) [fm]⊢* ⟨a+2, 1, c+1, 2, e⟩ := by
  intro a c e; step fm; step fm; step fm; finish

theorem r2r2r3_chain_b0 : ∀ m a c e,
    (⟨a, 0, c, 2, e+2*m⟩ : Q) [fm]⊢* ⟨a+2*m, 0, c+m, 2, e⟩ := by
  intro m; induction m with
  | zero => intro a c e; exists 0
  | succ m ih =>
    intro a c e
    rw [show e + 2 * (m + 1) = (e + 2 * m) + 2 from by ring]
    apply stepStar_trans (r2r2r3_step_b0 a c (e + 2 * m))
    apply stepStar_trans (ih (a + 2) (c + 1) e)
    rw [show a + 2 + 2 * m = a + 2 * (m + 1) from by ring,
        show c + 1 + m = c + (m + 1) from by ring]; finish

theorem r2r2r3_chain_b1 : ∀ m a c e,
    (⟨a, 1, c, 2, e+2*m⟩ : Q) [fm]⊢* ⟨a+2*m, 1, c+m, 2, e⟩ := by
  intro m; induction m with
  | zero => intro a c e; exists 0
  | succ m ih =>
    intro a c e
    rw [show e + 2 * (m + 1) = (e + 2 * m) + 2 from by ring]
    apply stepStar_trans (r2r2r3_step_b1 a c (e + 2 * m))
    apply stepStar_trans (ih (a + 2) (c + 1) e)
    rw [show a + 2 + 2 * m = a + 2 * (m + 1) from by ring,
        show c + 1 + m = c + (m + 1) from by ring]; finish

theorem r3_chain_b0 : ∀ k a c d,
    (⟨a, 0, c+k, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (d + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

theorem r3_chain_b1 : ∀ k a c d,
    (⟨a, 1, c+k, d, 0⟩ : Q) [fm]⊢* ⟨a, 1, c, d+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (d + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

theorem r4_chain : ∀ k a b,
    (⟨a, b, 0, k, 0⟩ : Q) [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b; step fm
    apply stepStar_trans (ih a (b + 1))
    rw [show b + 1 + k = b + (k + 1) from by ring]; finish

theorem terminal_e1_b0 : ∀ a c,
    (⟨a, 0, c, 2, 1⟩ : Q) [fm]⊢* ⟨a+1, 0, 0, 2*c+3, 0⟩ := by
  intro a c; step fm; step fm
  have h := r3_chain_b0 c (a+1) 0 3
  rwa [show 0 + c = c from by ring, show 3 + 2 * c = 2 * c + 3 from by ring] at h

theorem terminal_e1_b1 : ∀ a c,
    (⟨a, 1, c, 2, 1⟩ : Q) [fm]⊢* ⟨a+1, 1, 0, 2*c+3, 0⟩ := by
  intro a c; step fm; step fm
  have h := r3_chain_b1 c (a+1) 0 3
  rwa [show 0 + c = c from by ring, show 3 + 2 * c = 2 * c + 3 from by ring] at h

theorem terminal_e0_b0 : ∀ a c,
    (⟨a, 0, c+1, 2, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, 2*c+4, 0⟩ := by
  intro a c
  have h := r3_chain_b0 (c+1) a 0 2
  rwa [show 0 + (c + 1) = c + 1 from by ring, show 2 + 2 * (c + 1) = 2 * c + 4 from by ring] at h

theorem terminal_e0_b1 : ∀ a c,
    (⟨a, 1, c+1, 2, 0⟩ : Q) [fm]⊢* ⟨a, 1, 0, 2*c+4, 0⟩ := by
  intro a c
  have h := r3_chain_b1 (c+1) a 0 2
  rwa [show 0 + (c + 1) = c + 1 from by ring, show 2 + 2 * (c + 1) = 2 * c + 4 from by ring] at h

-- B=4j: (a+2j+1, 4j, 0, 0, 0) ⊢* (a+6j+3, 6j+5, 0, 0, 0)
theorem full_star_b4j (j a : ℕ) :
    (⟨a+2*j+1, 4*j, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+6*j+3, 6*j+5, 0, 0, 0⟩ := by
  have h1 : (⟨a+2*j+1, 4*j, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+1, 0, 0, 0, 6*j⟩ := by
    have := r5r1_chain (2*j) (a+1) 0 0
    rwa [show a+1+2*j = a+2*j+1 from by ring, show 0+2*(2*j) = 4*j from by ring,
         show 0+3*(2*j) = 6*j from by ring] at this
  apply stepStar_trans h1
  apply stepStar_trans (r5_r3_b0 a (6*j))
  have h2 : (⟨a, 0, 0, 2, 6*j+3⟩ : Q) [fm]⊢* ⟨a+6*j+2, 0, 3*j+1, 2, 1⟩ := by
    have := r2r2r3_chain_b0 (3*j+1) a 0 1
    rwa [show 1+2*(3*j+1) = 6*j+3 from by ring, show a+2*(3*j+1) = a+6*j+2 from by ring,
         show 0+(3*j+1) = 3*j+1 from by ring] at this
  rw [show 6*j+3 = 6*j+3 from rfl]
  apply stepStar_trans h2
  apply stepStar_trans (terminal_e1_b0 (a+6*j+2) (3*j+1))
  rw [show a+6*j+2+1 = a+6*j+3 from by ring, show 2*(3*j+1)+3 = 6*j+5 from by ring]
  have := r4_chain (6*j+5) (a+6*j+3) 0
  rwa [show 0+(6*j+5) = 6*j+5 from by ring] at this

-- B=4j+1: (a+2j+1, 4j+1, 0, 0, 0) ⊢* (a+6j+3, 6j+6, 0, 0, 0)
theorem full_star_b4j1 (j a : ℕ) :
    (⟨a+2*j+1, 4*j+1, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+6*j+3, 6*j+6, 0, 0, 0⟩ := by
  have h1 : (⟨a+2*j+1, 4*j+1, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+1, 1, 0, 0, 6*j⟩ := by
    have := r5r1_chain (2*j) (a+1) 1 0
    rwa [show a+1+2*j = a+2*j+1 from by ring, show 1+2*(2*j) = 4*j+1 from by ring,
         show 0+3*(2*j) = 6*j from by ring] at this
  apply stepStar_trans h1
  apply stepStar_trans (r5_r3_b1 a (6*j))
  have h2 : (⟨a, 1, 0, 2, 6*j+3⟩ : Q) [fm]⊢* ⟨a+6*j+2, 1, 3*j+1, 2, 1⟩ := by
    have := r2r2r3_chain_b1 (3*j+1) a 0 1
    rwa [show 1+2*(3*j+1) = 6*j+3 from by ring, show a+2*(3*j+1) = a+6*j+2 from by ring,
         show 0+(3*j+1) = 3*j+1 from by ring] at this
  rw [show 6*j+3 = 6*j+3 from rfl]
  apply stepStar_trans h2
  apply stepStar_trans (terminal_e1_b1 (a+6*j+2) (3*j+1))
  rw [show a+6*j+2+1 = a+6*j+3 from by ring, show 2*(3*j+1)+3 = 6*j+5 from by ring]
  have := r4_chain (6*j+5) (a+6*j+3) 1
  rwa [show 1+(6*j+5) = 6*j+6 from by ring] at this

-- B=4j+2: (a+2j+2, 4j+2, 0, 0, 0) ⊢* (a+6j+6, 6j+8, 0, 0, 0)
theorem full_star_b4j2 (j a : ℕ) :
    (⟨a+2*j+2, 4*j+2, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+6*j+6, 6*j+8, 0, 0, 0⟩ := by
  have h1 : (⟨a+2*j+2, 4*j+2, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+1, 0, 0, 0, 6*j+3⟩ := by
    have := r5r1_chain (2*j+1) (a+1) 0 0
    rwa [show a+1+(2*j+1) = a+2*j+2 from by ring, show 0+2*(2*j+1) = 4*j+2 from by ring,
         show 0+3*(2*j+1) = 6*j+3 from by ring] at this
  apply stepStar_trans h1
  apply stepStar_trans (r5_r3_b0 a (6*j+3))
  have h2 : (⟨a, 0, 0, 2, 6*j+6⟩ : Q) [fm]⊢* ⟨a+6*j+6, 0, 3*j+3, 2, 0⟩ := by
    have := r2r2r3_chain_b0 (3*j+3) a 0 0
    rwa [show 0+2*(3*j+3) = 6*j+6 from by ring, show a+2*(3*j+3) = a+6*j+6 from by ring,
         show 0+(3*j+3) = 3*j+3 from by ring] at this
  rw [show 6*j+3+3 = 6*j+6 from by ring]
  apply stepStar_trans h2
  rw [show 3*j+3 = (3*j+2)+1 from by ring]
  apply stepStar_trans (terminal_e0_b0 (a+6*j+6) (3*j+2))
  rw [show 2*(3*j+2)+4 = 6*j+8 from by ring]
  have := r4_chain (6*j+8) (a+6*j+6) 0
  rwa [show 0+(6*j+8) = 6*j+8 from by ring] at this

-- B=4j+3: (a+2j+2, 4j+3, 0, 0, 0) ⊢* (a+6j+6, 6j+9, 0, 0, 0)
theorem full_star_b4j3 (j a : ℕ) :
    (⟨a+2*j+2, 4*j+3, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+6*j+6, 6*j+9, 0, 0, 0⟩ := by
  have h1 : (⟨a+2*j+2, 4*j+3, 0, 0, 0⟩ : Q) [fm]⊢* ⟨a+1, 1, 0, 0, 6*j+3⟩ := by
    have := r5r1_chain (2*j+1) (a+1) 1 0
    rwa [show a+1+(2*j+1) = a+2*j+2 from by ring, show 1+2*(2*j+1) = 4*j+3 from by ring,
         show 0+3*(2*j+1) = 6*j+3 from by ring] at this
  apply stepStar_trans h1
  apply stepStar_trans (r5_r3_b1 a (6*j+3))
  have h2 : (⟨a, 1, 0, 2, 6*j+6⟩ : Q) [fm]⊢* ⟨a+6*j+6, 1, 3*j+3, 2, 0⟩ := by
    have := r2r2r3_chain_b1 (3*j+3) a 0 0
    rwa [show 0+2*(3*j+3) = 6*j+6 from by ring, show a+2*(3*j+3) = a+6*j+6 from by ring,
         show 0+(3*j+3) = 3*j+3 from by ring] at this
  rw [show 6*j+3+3 = 6*j+6 from by ring]
  apply stepStar_trans h2
  rw [show 3*j+3 = (3*j+2)+1 from by ring]
  apply stepStar_trans (terminal_e0_b1 (a+6*j+6) (3*j+2))
  rw [show 2*(3*j+2)+4 = 6*j+8 from by ring]
  have := r4_chain (6*j+8) (a+6*j+6) 1
  rwa [show 1+(6*j+8) = 6*j+9 from by ring] at this

-- Convert to stepPlus
theorem full_plus_b4j (j a : ℕ) :
    (⟨a+2*j+1, 4*j, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a+6*j+3, 6*j+5, 0, 0, 0⟩ :=
  stepStar_stepPlus (full_star_b4j j a) (by simp [Q]; omega)

theorem full_plus_b4j1 (j a : ℕ) :
    (⟨a+2*j+1, 4*j+1, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a+6*j+3, 6*j+6, 0, 0, 0⟩ :=
  stepStar_stepPlus (full_star_b4j1 j a) (by simp [Q]; omega)

theorem full_plus_b4j2 (j a : ℕ) :
    (⟨a+2*j+2, 4*j+2, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a+6*j+6, 6*j+8, 0, 0, 0⟩ :=
  stepStar_stepPlus (full_star_b4j2 j a) (by simp [Q]; omega)

theorem full_plus_b4j3 (j a : ℕ) :
    (⟨a+2*j+2, 4*j+3, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a+6*j+6, 6*j+9, 0, 0, 0⟩ :=
  stepStar_stepPlus (full_star_b4j3 j a) (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fun q ↦ ∃ a b, q = (⟨a, b, 0, 0, 0⟩ : Q) ∧ a ≥ 1 ∧ 2 * a > b ∧ b ≠ 1)
  · intro q ⟨a, b, hq, ha, hab, hb1⟩
    subst hq
    rcases b with _ | _ | b
    · -- b = 0
      refine ⟨⟨a+2, 5, 0, 0, 0⟩, ⟨a+2, 5, rfl, by omega, by omega, by omega⟩, ?_⟩
      have h := full_plus_b4j 0 (a-1)
      rwa [show (a-1)+2*0+1 = a from by omega, show 4*0 = 0 from by ring,
           show (a-1)+6*0+3 = a+2 from by omega, show 6*0+5 = 5 from by ring] at h
    · exact absurd rfl hb1
    · -- b+2: decompose b into 4 residue classes
      rcases Nat.even_or_odd b with ⟨j₁, hj₁⟩ | ⟨j₁, hj₁⟩
      · -- b = 2*j₁, so b+2 = 2*j₁+2 (even)
        rcases Nat.even_or_odd j₁ with ⟨i, hi⟩ | ⟨i, hi⟩
        · -- j₁=2i, b=4i, b+2=4i+2: use full_plus_b4j2 i
          subst hi; subst hj₁
          have hbeq : i + i + (i + i) + 1 + 1 = 4 * i + 2 := by omega
          refine ⟨⟨a+4*i+4, 6*i+8, 0, 0, 0⟩,
                  ⟨a+4*i+4, 6*i+8, rfl, by omega, by omega, by omega⟩, ?_⟩
          have h := full_plus_b4j2 i (a-2*i-2)
          rw [show (a-2*i-2)+2*i+2 = a from by omega,
              show (a-2*i-2)+6*i+6 = a+4*i+4 from by omega] at h
          rw [hbeq]; exact h
        · -- j₁=2i+1, b=4i+2, b+2=4i+4=4(i+1): use full_plus_b4j (i+1)
          subst hi; subst hj₁
          have hbeq : 2 * i + 1 + (2 * i + 1) + 1 + 1 = 4 * i + 4 := by omega
          refine ⟨⟨a+4*i+6, 6*i+11, 0, 0, 0⟩,
                  ⟨a+4*i+6, 6*i+11, rfl, by omega, by omega, by omega⟩, ?_⟩
          have h := full_plus_b4j (i+1) (a-2*i-3)
          rw [show (a-2*i-3)+2*(i+1)+1 = a from by omega,
              show 4*(i+1) = 4*i+4 from by ring,
              show (a-2*i-3)+6*(i+1)+3 = a+4*i+6 from by omega,
              show 6*(i+1)+5 = 6*i+11 from by ring] at h
          rw [hbeq]; exact h
      · -- b = 2*j₁+1, so b+2 = 2*j₁+3 (odd)
        rcases Nat.even_or_odd j₁ with ⟨i, hi⟩ | ⟨i, hi⟩
        · -- j₁=2i, b=4i+1, b+2=4i+3: use full_plus_b4j3 i
          subst hi; subst hj₁
          have hbeq : 2 * (i + i) + 1 + 1 + 1 = 4 * i + 3 := by omega
          refine ⟨⟨a+4*i+4, 6*i+9, 0, 0, 0⟩,
                  ⟨a+4*i+4, 6*i+9, rfl, by omega, by omega, by omega⟩, ?_⟩
          have h := full_plus_b4j3 i (a-2*i-2)
          rw [show (a-2*i-2)+2*i+2 = a from by omega,
              show (a-2*i-2)+6*i+6 = a+4*i+4 from by omega] at h
          rw [hbeq]; exact h
        · -- j₁=2i+1, b=4i+3, b+2=4i+5=4(i+1)+1: use full_plus_b4j1 (i+1)
          subst hi; subst hj₁
          have hbeq : 2 * (2 * i + 1) + 1 + 1 + 1 = 4 * i + 5 := by omega
          refine ⟨⟨a+4*i+6, 6*i+12, 0, 0, 0⟩,
                  ⟨a+4*i+6, 6*i+12, rfl, by omega, by omega, by omega⟩, ?_⟩
          have h := full_plus_b4j1 (i+1) (a-2*i-3)
          rw [show (a-2*i-3)+2*(i+1)+1 = a from by omega,
              show 4*(i+1)+1 = 4*i+5 from by ring,
              show (a-2*i-3)+6*(i+1)+3 = a+4*i+6 from by omega,
              show 6*(i+1)+6 = 6*i+12 from by ring] at h
          rw [hbeq]; exact h
  · exact ⟨1, 0, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_125
