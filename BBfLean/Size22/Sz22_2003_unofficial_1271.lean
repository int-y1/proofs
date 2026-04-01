import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1271: [5/6, 99/35, 5929/3, 2/11, 3/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 0 -1  0  2  2
 1  0  0  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1271

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: move e to a
theorem e_to_a : ∀ k, ∀ a d,
    ⟨a, (0 : ℕ), 0, d, k⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d; step fm
    apply stepStar_trans (ih (a + 1) d)
    rw [show a + 1 + k = a + (k + 1) from by ring]; finish

-- R2,R1,R1 chain: k rounds
-- From (a+2k, 0, c+1, d+k, e) to (a, 0, c+k+1, d, e+k)
-- The key: each round does R2(c≥1,d≥1),R1(a≥1,b≥1),R1(a≥1,b≥1)
-- Net: a-=2, c+=1, d-=1, e+=1
theorem r2r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 2 * k, (0 : ℕ), c + 1, d + k, e⟩ [fm]⊢*
    ⟨a, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; simp; exists 0
  | succ k ih =>
    intro a c d e
    rw [show a + 2 * (k + 1) = a + 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    -- State: (a+2k+2, 0, c+1, d+k+1, e)
    -- R2: needs c+1 >= 1 ✓ and d+k+1 >= 1 ✓
    step fm
    -- State: (a+2k+2, 2, c, d+k, e+1)
    -- R1: needs a+2k+2 >= 1 ✓ and 2 >= 1 ✓
    step fm
    -- State: (a+2k+1, 1, c+1, d+k, e+1)
    -- R1: needs a+2k+1 >= 1 ✓ and 1 >= 1 ✓
    step fm
    -- State: (a+2k, 0, c+2, d+k, e+1)
    -- Now apply IH with c' = c+1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih a (c + 1) d (e + 1))
    rw [show c + 1 + k + 1 = c + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

-- R2 chain: drain c and d simultaneously (a=0)
theorem r2_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b, c + k, d + k, e⟩ [fm]⊢*
    ⟨0, b + 2 * k, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro b c d e; simp; exists 0
  | succ k ih =>
    intro b c d e
    rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    -- State: (0, b+2, c+k, d+k, e+1)
    apply stepStar_trans (ih (b + 2) c d (e + 1))
    rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

-- R3 chain: drain b (a=0, c=0)
theorem r3_chain : ∀ k, ∀ d e,
    ⟨(0 : ℕ), k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro d e; simp; exists 0
  | succ k ih =>
    intro d e; step fm
    apply stepStar_trans (ih (d + 2) (e + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring,
        show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

-- Combined tail: (0, b+1, c, 0, e) ->* (0, 0, 0, 2*b+3*c+2, e+2*b+5*c+2)
theorem combined_tail : ∀ c, ∀ b e,
    ⟨(0 : ℕ), b + 1, c, 0, e⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * b + 3 * c + 2, e + 2 * b + 5 * c + 2⟩ := by
  intro c; induction c using Nat.strongRecOn with
  | ind c ih =>
    intro b e
    match c with
    | 0 =>
      -- R3^(b+1): (0, b+1, 0, 0, e) -> (0, 0, 0, 2(b+1), e+2(b+1))
      apply stepStar_trans (r3_chain (b + 1) 0 e)
      rw [show 0 + 2 * (b + 1) = 2 * b + 3 * 0 + 2 from by ring,
          show e + 2 * (b + 1) = e + 2 * b + 5 * 0 + 2 from by ring]; finish
    | 1 =>
      -- (0, b+1, 1, 0, e) -> R3 -> (0, b, 1, 2, e+2)
      -- -> R2 -> (0, b+2, 0, 1, e+3) -> R3^(b+2) -> done
      step fm; step fm
      -- State: (0, b+2, 0, 1, e+3)
      rw [show b + 2 = b + 2 from rfl]
      apply stepStar_trans (r3_chain (b + 2) 1 (e + 3))
      rw [show 1 + 2 * (b + 2) = 2 * b + 3 * 1 + 2 from by ring,
          show e + 3 + 2 * (b + 2) = e + 2 * b + 5 * 1 + 2 from by ring]; finish
    | c + 2 =>
      -- (0, b+1, c+2, 0, e) -> R3 -> (0, b, c+2, 2, e+2)
      -- -> R2 -> (0, b+2, c+1, 1, e+3) -> R2 -> (0, b+4, c, 0, e+4)
      -- -> IH(c, b+3, e+4)
      step fm
      rw [show c + 2 = (c + 1) + 1 from by ring,
          show (2 : ℕ) = 1 + 1 from by ring]
      step fm; step fm
      rw [show b + 4 = (b + 3) + 1 from by ring]
      apply stepStar_trans (ih c (by omega) (b + 3) (e + 4))
      rw [show 2 * (b + 3) + 3 * c + 2 = 2 * b + 3 * (c + 2) + 2 from by ring,
          show e + 4 + 2 * (b + 3) + 5 * c + 2 = e + 2 * b + 5 * (c + 2) + 2 from by ring]
      finish

-- Even transition: (0,0,0, D+m+1, 2m+2) ⊢+ (0,0,0, D+3m+4, 6m+5)
theorem transition_even (D m : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + m + 1, 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 3 * m + 4, 6 * m + 5⟩ := by
  -- Phase 1: R4^(2m+2)
  apply stepStar_stepPlus_stepPlus (e_to_a (2 * m + 2) 0 (D + m + 1))
  -- State: (2m+2, 0, 0, D+m+1, 0)
  -- R5: (2m+2, 0, 0, D+m+1, 0) -> (2m+1, 1, 0, D+m+1, 0)
  rw [show 0 + (2 * m + 2) = 2 * m + 1 + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨2 * m + 1 + 1, (0 : ℕ), 0, D + m + 1, 0⟩ : Q) [fm]⊢
                     ⟨2 * m + 1, 1, 0, D + m + 1, 0⟩)
  -- R1: (2m+1, 1, 0, D+m+1, 0) -> (2m, 0, 1, D+m+1, 0)
  rw [show 2 * m + 1 = 2 * m + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2 * m + 1, 0 + 1, 0, D + m + 1, 0⟩ : Q) [fm]⊢
                     ⟨2 * m, 0, 1, D + m + 1, 0⟩))
  -- R2R1R1^m: (2m, 0, 1, D+m+1, 0) -> (0, 0, m+1, D+1, m)
  rw [show 2 * m = 0 + 2 * m from by ring,
      show D + m + 1 = (D + 1) + m from by ring]
  apply stepStar_trans (r2r1r1_chain m 0 0 (D + 1) 0)
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 0 + m = m from by ring]
  -- State: (0, 0, m+1, D+1, m). Split on D vs m.
  by_cases hdm : D ≥ m
  · -- D >= m: R2^(m+1) then R3 drain
    obtain ⟨D2, rfl⟩ : ∃ D2, D = m + D2 := ⟨D - m, by omega⟩
    rw [show m + 1 = 0 + (m + 1) from by ring,
        show m + D2 + 1 = D2 + (m + 1) from by ring]
    apply stepStar_trans (r2_chain (m + 1) 0 0 D2 m)
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show m + (m + 1) = 2 * m + 1 from by ring]
    apply stepStar_trans (r3_chain (2 * m + 2) D2 (2 * m + 1))
    rw [show D2 + 2 * (2 * m + 2) = m + D2 + 3 * m + 4 from by ring,
        show 2 * m + 1 + 2 * (2 * m + 2) = 6 * m + 5 from by ring]; finish
  · -- D < m: R2^(D+1) then combined_tail
    push_neg at hdm
    -- State: (0, 0, m+1, D+1, m). Rewrite for r2_chain.
    -- r2_chain(D+1) needs (0, b, c+(D+1), d+(D+1), e)
    -- c = m-D-1+1, d = 0, k = D+1. So c+k = m-D-1+1+D+1 = m+1. ✓
    -- d+k = 0+D+1 = D+1. ✓
    -- But the 4th component D+1 needs to match d+k = 0 + (D+1).
    -- Use show to restate the goal
    suffices h : ⟨(0 : ℕ), 0, (m - D - 1 + 1) + (D + 1), 0 + (D + 1), m⟩ [fm]⊢*
        ⟨0, 0, 0, D + 3 * m + 4, 6 * m + 5⟩ by
      rwa [show (m - D - 1 + 1) + (D + 1) = m + 1 from by omega,
           show 0 + (D + 1) = D + 1 from by ring] at h
    apply stepStar_trans (r2_chain (D + 1) 0 (m - D - 1 + 1) 0 m)
    rw [show 0 + 2 * (D + 1) = 2 * D + 1 + 1 from by ring,
        show m + (D + 1) = m + D + 1 from by ring]
    apply stepStar_trans (combined_tail (m - D - 1 + 1) (2 * D + 1) (m + D + 1))
    rw [show 2 * (2 * D + 1) + 3 * (m - D - 1 + 1) + 2 = D + 3 * m + 4 from by omega,
        show m + D + 1 + 2 * (2 * D + 1) + 5 * (m - D - 1 + 1) + 2 = 6 * m + 5 from by omega]
    finish

-- Odd transition for e=1: (0,0,0,d+1,1) ⊢+ (0,0,0,d+3,2)
theorem transition_e1 (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 1, 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3, 2⟩ := by
  step fm; step fm; step fm; finish

-- Odd transition for e=2m'+3: (0,0,0, D+m'+2, 2m'+3) ⊢+ (0,0,0, D+3m'+6, 6m'+8)
theorem transition_odd (D m' : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + m' + 2, 2 * m' + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 3 * m' + 6, 6 * m' + 8⟩ := by
  -- Phase 1: R4^(2m'+3)
  apply stepStar_stepPlus_stepPlus (e_to_a (2 * m' + 3) 0 (D + m' + 2))
  -- State: (2m'+3, 0, 0, D+m'+2, 0)
  -- R5
  rw [show 0 + (2 * m' + 3) = 2 * m' + 2 + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨2 * m' + 2 + 1, (0 : ℕ), 0, D + m' + 2, 0⟩ : Q) [fm]⊢
                     ⟨2 * m' + 2, 1, 0, D + m' + 2, 0⟩)
  -- R1
  rw [show 2 * m' + 2 = 2 * m' + 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2 * m' + 1 + 1, 0 + 1, 0, D + m' + 2, 0⟩ : Q) [fm]⊢
                     ⟨2 * m' + 1, 0, 1, D + m' + 2, 0⟩))
  -- R2R1R1^m': (2m'+1, 0, 1, D+m'+2, 0) -> (1, 0, m'+1, D+2, m')
  rw [show 2 * m' + 1 = 1 + 2 * m' from by ring,
      show D + m' + 2 = (D + 2) + m' from by ring]
  apply stepStar_trans (r2r1r1_chain m' 1 0 (D + 2) 0)
  rw [show 0 + m' + 1 = m' + 1 from by ring,
      show 0 + m' = m' from by ring]
  -- State: (1, 0, m'+1, D+2, m')
  -- R2: needs c >= 1 ✓ (m'+1 >= 1) and d >= 1 ✓ (D+2 >= 1)
  rw [show D + 2 = (D + 1) + 1 from by ring,
      show m' + 1 = m' + 1 from rfl]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, (0 : ℕ), m' + 1, (D + 1) + 1, m'⟩ : Q) [fm]⊢
                     ⟨1, 2, m', D + 1, m' + 1⟩))
  -- R1: (1, 2, m', D+1, m'+1) -> (0, 1, m'+1, D+1, m'+1)
  rw [show (1 : ℕ) = 0 + 1 from rfl,
      show (2 : ℕ) = 0 + 1 + 1 from rfl]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0 + 1, 0 + 1 + 1, m', D + 1, m' + 1⟩ : Q) [fm]⊢
                     ⟨0, 0 + 1, m' + 1, D + 1, m' + 1⟩))
  -- State: (0, 0+1, m'+1, D+1, m'+1). Normalize 0+1 to 1.
  rw [show (0 + 1 : ℕ) = 1 from rfl]
  -- State: (0, 1, m'+1, D+1, m'+1)
  by_cases hdm : D ≥ m'
  · -- D >= m': R2^(m'+1) then R3 drain
    obtain ⟨D2, rfl⟩ : ∃ D2, D = m' + D2 := ⟨D - m', by omega⟩
    -- State: (0, 1, m'+1, m'+D2+1, m'+1). Need r2_chain form.
    suffices h : ⟨(0 : ℕ), 1, 0 + (m' + 1), D2 + (m' + 1), m' + 1⟩ [fm]⊢*
        ⟨0, 0, 0, m' + D2 + 3 * m' + 6, 6 * m' + 8⟩ by
      rwa [show 0 + (m' + 1) = m' + 1 from by ring,
           show D2 + (m' + 1) = m' + D2 + 1 from by ring] at h
    apply stepStar_trans (r2_chain (m' + 1) 1 0 D2 (m' + 1))
    rw [show 1 + 2 * (m' + 1) = 2 * m' + 3 from by ring,
        show m' + 1 + (m' + 1) = 2 * m' + 2 from by ring]
    apply stepStar_trans (r3_chain (2 * m' + 3) D2 (2 * m' + 2))
    rw [show D2 + 2 * (2 * m' + 3) = m' + D2 + 3 * m' + 6 from by ring,
        show 2 * m' + 2 + 2 * (2 * m' + 3) = 6 * m' + 8 from by ring]; finish
  · -- D < m': R2^(D+1) then combined_tail
    push_neg at hdm
    -- State: (0, 1, m'+1, D+1, m'+1). Need r2_chain form.
    suffices h : ⟨(0 : ℕ), 1, (m' - D - 1 + 1) + (D + 1), 0 + (D + 1), m' + 1⟩ [fm]⊢*
        ⟨0, 0, 0, D + 3 * m' + 6, 6 * m' + 8⟩ by
      rwa [show (m' - D - 1 + 1) + (D + 1) = m' + 1 from by omega,
           show 0 + (D + 1) = D + 1 from by ring] at h
    apply stepStar_trans (r2_chain (D + 1) 1 (m' - D - 1 + 1) 0 (m' + 1))
    rw [show 1 + 2 * (D + 1) = 2 * D + 2 + 1 from by ring,
        show m' + 1 + (D + 1) = m' + D + 2 from by ring]
    apply stepStar_trans (combined_tail (m' - D - 1 + 1) (2 * D + 2) (m' + D + 2))
    rw [show 2 * (2 * D + 2) + 3 * (m' - D - 1 + 1) + 2 = D + 3 * m' + 6 from by omega,
        show m' + D + 2 + 2 * (2 * D + 2) + 5 * (m' - D - 1 + 1) + 2 = 6 * m' + 8 from by omega]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 5⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨(0 : ℕ), 0, 0, d + 1, e + 1⟩ ∧ 2 * (d + 1) ≥ e + 1)
  · intro c ⟨d, e, hc, hinv⟩
    subst hc
    rcases Nat.even_or_odd (e + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e+1 = 2m (even). m >= 1 since e+1 >= 1.
      -- Write m = m₀+1, so e+1 = 2m₀+2, e = 2m₀+1.
      -- d+1 >= m₀+1 from invariant. Write d+1 = D+m₀+1, so d = D+m₀.
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
      have hd_ge : d ≥ m₀ := by omega
      obtain ⟨D, rfl⟩ : ∃ D, d = m₀ + D := ⟨d - m₀, by omega⟩
      refine ⟨⟨0, 0, 0, D + 3 * m₀ + 4, 6 * m₀ + 5⟩,
              ⟨D + 3 * m₀ + 3, 6 * m₀ + 4, ?_, ?_⟩, ?_⟩
      · simp [show D + 3 * m₀ + 3 + 1 = D + 3 * m₀ + 4 from by ring,
              show 6 * m₀ + 4 + 1 = 6 * m₀ + 5 from by ring]
      · omega
      · have he : e + 1 = 2 * m₀ + 2 := by omega
        rw [show m₀ + D + 1 = D + m₀ + 1 from by ring,
            show e + 1 = 2 * m₀ + 2 from he]
        exact transition_even D m₀
    · -- e+1 = 2m+1 (odd). e = 2m.
      match m with
      | 0 =>
        -- e = 0. State: (0,0,0,d+1,1)
        refine ⟨⟨0, 0, 0, d + 3, 2⟩, ⟨d + 2, 1, ?_, ?_⟩, ?_⟩
        · simp [show d + 2 + 1 = d + 3 from by ring]
        · omega
        · have he : e = 0 := by omega
          rw [show e + 1 = 1 from by omega]
          exact transition_e1 d
      | m₀ + 1 =>
        -- e+1 = 2(m₀+1)+1 = 2m₀+3, e = 2m₀+2.
        -- d+1 >= (2m₀+3)/2 => d+1 >= m₀+2, d >= m₀+1. Write d = (m₀+1)+D.
        have hd_ge : d ≥ m₀ + 1 := by omega
        obtain ⟨D, rfl⟩ : ∃ D, d = (m₀ + 1) + D := ⟨d - (m₀ + 1), by omega⟩
        refine ⟨⟨0, 0, 0, D + 3 * m₀ + 6, 6 * m₀ + 8⟩,
                ⟨D + 3 * m₀ + 5, 6 * m₀ + 7, ?_, ?_⟩, ?_⟩
        · simp [show D + 3 * m₀ + 5 + 1 = D + 3 * m₀ + 6 from by ring,
                show 6 * m₀ + 7 + 1 = 6 * m₀ + 8 from by ring]
        · omega
        · have he : e + 1 = 2 * m₀ + 3 := by omega
          rw [show m₀ + 1 + D + 1 = D + m₀ + 2 from by ring,
              show e + 1 = 2 * m₀ + 3 from he]
          exact transition_odd D m₀
  · exact ⟨4, 4, by simp [show 4 + 1 = 5 from rfl], by omega⟩

end Sz22_2003_unofficial_1271
