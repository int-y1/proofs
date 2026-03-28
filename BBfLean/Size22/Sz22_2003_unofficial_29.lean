import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #29: [1/15, 27/77, 49/3, 10/49, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 0  3  0 -1 -1
 0 -1  0  2  0
 1  0  1 -2  0
-1  1  0  0  1
```

This Fractran program's non-halting is equivalent to a Collatz-like property (prop_hydra).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_29

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

def prop_hydra :=
  ∀ (a : ℕ → ℕ) (b : ℕ → ℤ)
  (_a_ini : a 0 = 1)
  (_a_rec : ∀ n, a (n + 1) = if a n % 2 = 0 then 5 * (a n / 2) + 2 else 5 * (a n / 2))
  (_b_ini : b 0 = 0)
  (_b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n - 1 else b n + 2),
  ∀ n, b n ≥ 0

def hydra_a : ℕ → ℕ
  | 0 => 1
  | n+1 => if hydra_a n % 2 = 0 then 5 * (hydra_a n / 2) + 2 else 5 * (hydra_a n / 2)

def hydra_b : ℕ → ℤ
  | 0 => 0
  | n+1 => if hydra_a n % 2 = 0 then hydra_b n - 1 else hydra_b n + 2

-- ============================================================
-- Phase lemmas (with induction)
-- ============================================================

theorem r2r2r3_even : ∀ K, ∀ a b, ⟨a, b, 0, 2, 2*(K+1)⟩ [fm]⊢* ⟨a, b+5*(K+1)+1, 0, 0, 0⟩ := by
  intro K; induction' K with K ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (K + 1 + 1) = 2 * (K + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 5)); ring_nf; finish

theorem r2r2r3_odd : ∀ K, ∀ a b, ⟨a, b, 0, 2, 2*K+1⟩ [fm]⊢* ⟨a, b+5*K+3, 0, 1, 0⟩ := by
  intro K; induction' K with K ih <;> intro a b
  · step fm; ring_nf; finish
  · rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 5)); ring_nf; finish

theorem r3_drain : ∀ b, ∀ a d, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d+2*b, 0⟩ := by
  intro b; induction' b with b ih <;> intro a d
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih a (d + 2)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ a c, ⟨a, 0, c, 2*k, 0⟩ [fm]⊢* ⟨a+k, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; finish
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) (c + 1)); ring_nf; finish

theorem r4_drain_odd : ∀ k, ∀ a c, ⟨a, 0, c, 2*k+1, 0⟩ [fm]⊢* ⟨a+k, 0, c+k, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) (c + 1)); ring_nf; finish

theorem r5r1_drain : ∀ c, ∀ a e, ⟨a+c, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+c⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · ring_nf; finish
  · rw [show a + (c + 1) = (a + c) + 1 from by ring]
    step fm; step fm; apply stepStar_trans (ih a (e + 1)); ring_nf; finish

theorem odd_cleanup : ∀ a c, ⟨a+1, 0, c+4, 1, 0⟩ [fm]⊢* ⟨a, 0, c, 0, 0⟩ := by
  intro a c; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- ============================================================
-- Clean wrappers (with c=0 or b=0 or d=0 specialized)
-- ============================================================

theorem r2r2r3_even0 : ∀ K a, ⟨a, 0, 0, 2, 2*(K+1)⟩ [fm]⊢* ⟨a, 5*(K+1)+1, 0, 0, 0⟩ := by
  intro K a; have h := r2r2r3_even K a 0; simp only [Nat.zero_add] at h; exact h

theorem r2r2r3_odd0 : ∀ K a, ⟨a, 0, 0, 2, 2*K+1⟩ [fm]⊢* ⟨a, 5*K+3, 0, 1, 0⟩ := by
  intro K a; have h := r2r2r3_odd K a 0; simp only [Nat.zero_add] at h; exact h

theorem r3_drain0 : ∀ b a, ⟨a, b, 0, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 2*b, 0⟩ := by
  intro b a; have h := r3_drain b a 0; simp only [Nat.zero_add] at h; exact h

theorem r4_drain0 : ∀ k a, ⟨a, 0, 0, 2*k, 0⟩ [fm]⊢* ⟨a+k, 0, k, 0, 0⟩ := by
  intro k a; have h := r4_drain k a 0; simp only [Nat.zero_add] at h; exact h

theorem r4_drain_odd0 : ∀ k a, ⟨a, 0, 0, 2*k+1, 0⟩ [fm]⊢* ⟨a+k, 0, k, 1, 0⟩ := by
  intro k a; have h := r4_drain_odd k a 0; simp only [Nat.zero_add] at h; exact h

theorem r5r1_drain0 : ∀ c a, ⟨a+c, 0, c, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, c⟩ := by
  intro c a; have h := r5r1_drain c a 0; simp only [Nat.zero_add] at h; exact h

-- ============================================================
-- Round lemmas
-- ============================================================

-- Even round: E=2(K+1) is even, e=2K+1 is odd
theorem round_even : ∀ K B, ⟨B+1, 0, 0, 0, 2*K+1⟩ [fm]⊢* ⟨B, 0, 0, 0, 5*K+6⟩ := by
  intro K B
  step fm; step fm
  rw [show 2 * K + 2 = 2 * (K + 1) from by ring]
  apply stepStar_trans (r2r2r3_even0 K B)
  apply stepStar_trans (r3_drain0 (5*(K+1)+1) B)
  apply stepStar_trans (r4_drain0 (5*(K+1)+1) B)
  apply stepStar_trans (r5r1_drain0 (5*(K+1)+1) B)
  rw [show 5 * (K + 1) + 1 = 5 * K + 6 from by ring]; finish

-- Odd round: E=2K+1 is odd, e=2K is even, K≥1
theorem round_odd : ∀ K, K ≥ 1 → ∀ B, ⟨B+1, 0, 0, 0, 2*K⟩ [fm]⊢* ⟨B+3, 0, 0, 0, 5*K-1⟩ := by
  intro K hK B
  step fm; step fm
  apply stepStar_trans (r2r2r3_odd0 K B)
  apply stepStar_trans (r3_drain (5*K+3) B 1)
  rw [show 1 + 2 * (5 * K + 3) = 2 * (5 * K + 3) + 1 from by ring]
  apply stepStar_trans (r4_drain_odd0 (5*K+3) B)
  rw [show B + (5 * K + 3) = (B + 5 * K + 2) + 1 from by omega,
      show (5 * K + 3 : ℕ) = (5 * K - 1) + 4 from by omega]
  apply stepStar_trans (odd_cleanup (B + 5 * K + 2) (5 * K - 1))
  rw [show B + 5 * K + 2 = (B + 3) + (5 * K - 1) from by omega]
  exact r5r1_drain0 (5*K-1) (B+3)

-- ============================================================
-- Connecting FM to hydra sequences
-- ============================================================

-- Bootstrap computation
theorem bootstrap : c₀ [fm]⊢* ⟨2, 0, 0, 0, 1⟩ := by execute fm 18

-- Halted state
theorem halted_zero : ∀ e, halted fm ⟨0, 0, 0, 0, e⟩ := by intro e; rfl

-- ============================================================
-- Helpers for the main theorem
-- ============================================================

-- Helper: any a,b satisfying the recurrence equal hydra_a, hydra_b
private theorem unique_a (a : ℕ → ℕ) (ha0 : a 0 = 1)
    (ha : ∀ n, a (n + 1) = if a n % 2 = 0 then 5 * (a n / 2) + 2 else 5 * (a n / 2)) :
    ∀ n, a n = hydra_a n := by
  intro n; induction n with
  | zero => simp [hydra_a, ha0]
  | succ n ih => simp [ha, hydra_a, ih]

private theorem unique_b (a : ℕ → ℕ) (b : ℕ → ℤ) (ha0 : a 0 = 1)
    (ha : ∀ n, a (n + 1) = if a n % 2 = 0 then 5 * (a n / 2) + 2 else 5 * (a n / 2))
    (hb0 : b 0 = 0)
    (hb : ∀ n, b (n + 1) = if a n % 2 = 0 then b n - 1 else b n + 2) :
    ∀ n, b n = hydra_b n := by
  intro n; induction n with
  | zero => simp [hydra_b, hb0]
  | succ n ih => simp [hb, hydra_b, unique_a a ha0 ha n, ih]

-- prop_hydra ↔ ∀ n, hydra_b n ≥ 0
private theorem prop_hydra_iff : prop_hydra ↔ ∀ n, hydra_b n ≥ 0 := by
  constructor
  · intro h n
    exact h hydra_a hydra_b rfl (fun n => by simp [hydra_a]) rfl (fun n => by simp [hydra_b]) n
  · intro h a b ha0 ha hb0 hb n
    rw [unique_b a b ha0 ha hb0 hb n]; exact h n

-- Key hydra_a properties: hydra_a(n) ≥ 2 for n ≥ 2
private theorem hydra_a_ge_2 (n : ℕ) (hn : n ≥ 2) : hydra_a n ≥ 2 := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [hydra_a]
    split
    · omega
    · cases m with
      | zero => omega
      | succ k =>
        cases k with
        | zero => simp [hydra_a] at *
        | succ k => have := ih (by omega); omega

-- hydra_b step
private theorem hydra_b_step (n : ℕ) :
    hydra_b (n + 1) = if hydra_a n % 2 = 0 then hydra_b n - 1 else hydra_b n + 2 := by
  rfl

-- hydra_a step
private theorem hydra_a_step (n : ℕ) :
    hydra_a (n + 1) = if hydra_a n % 2 = 0 then 5 * (hydra_a n / 2) + 2 else 5 * (hydra_a n / 2) := by
  rfl

-- One round transition for canonical states
private theorem canonical_round (n : ℕ) (hbn : hydra_b (n + 2) ≥ 0)
    (hbn1 : hydra_b (n + 3) ≥ 0) :
    (⟨(hydra_b (n + 2)).toNat + 1, 0, 0, 0, hydra_a (n + 2) - 1⟩ : Q)
    [fm]⊢* ⟨(hydra_b (n + 3)).toNat + 1, 0, 0, 0, hydra_a (n + 3) - 1⟩ := by
  have ha2 := hydra_a_ge_2 (n + 2) (by omega)
  by_cases hpar : hydra_a (n + 2) % 2 = 0
  · -- Even case
    have hKpos : hydra_a (n + 2) / 2 ≥ 1 := by omega
    have he : hydra_a (n + 2) - 1 = 2 * (hydra_a (n + 2) / 2 - 1) + 1 := by omega
    have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) + 2 := by
      rw [hydra_a_step]; rw [if_pos hpar]
    have hb3 : hydra_b (n + 3) = hydra_b (n + 2) - 1 := by
      rw [hydra_b_step]; rw [if_pos hpar]
    have hb3nat : (hydra_b (n + 3)).toNat = (hydra_b (n + 2)).toNat - 1 := by
      rw [hb3]; omega
    have hbn2pos : (hydra_b (n + 2)).toNat ≥ 1 := by rw [hb3] at hbn1; omega
    rw [he, ha3, hb3nat]
    rw [show (hydra_b (n + 2)).toNat - 1 + 1 = (hydra_b (n + 2)).toNat from by omega]
    rw [show 5 * (hydra_a (n + 2) / 2) + 2 - 1 = 5 * (hydra_a (n + 2) / 2 - 1) + 6 from by omega]
    exact round_even (hydra_a (n + 2) / 2 - 1) ((hydra_b (n + 2)).toNat)
  · -- Odd case
    have hKpos : hydra_a (n + 2) / 2 ≥ 1 := by omega
    have he : hydra_a (n + 2) - 1 = 2 * (hydra_a (n + 2) / 2) := by omega
    have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) := by
      rw [hydra_a_step]; rw [if_neg hpar]
    have hb3 : hydra_b (n + 3) = hydra_b (n + 2) + 2 := by
      rw [hydra_b_step]; rw [if_neg hpar]
    have hb3nat : (hydra_b (n + 3)).toNat = (hydra_b (n + 2)).toNat + 2 := by
      rw [hb3]; omega
    rw [he, ha3, hb3nat]
    rw [show (hydra_b (n + 2)).toNat + 2 + 1 = (hydra_b (n + 2)).toNat + 3 from by omega]
    exact round_odd (hydra_a (n + 2) / 2) (by omega) ((hydra_b (n + 2)).toNat)

-- States differ (needed for ⊢* → ⊢⁺)
private theorem canonical_ne (n : ℕ) :
    (⟨(hydra_b (n + 2)).toNat + 1, 0, 0, 0, hydra_a (n + 2) - 1⟩ : Q) ≠
    ⟨(hydra_b (n + 3)).toNat + 1, 0, 0, 0, hydra_a (n + 3) - 1⟩ := by
  have ha2 := hydra_a_ge_2 (n + 2) (by omega)
  by_cases hpar : hydra_a (n + 2) % 2 = 0
  · have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) + 2 := by
      rw [hydra_a_step]; rw [if_pos hpar]
    intro h; simp only [Prod.mk.injEq] at h; omega
  · have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) := by
      rw [hydra_a_step]; rw [if_neg hpar]
    intro h; simp only [Prod.mk.injEq] at h; omega

-- Reach canonical state n from (2,0,0,0,1) given all hydra_b up to n+2 are ≥ 0
private theorem reach_canonical (n : ℕ) (hb : ∀ k, k ≤ n + 2 → hydra_b k ≥ 0) :
    (⟨2, 0, 0, 0, 1⟩ : Q) [fm]⊢*
    ⟨(hydra_b (n + 2)).toNat + 1, 0, 0, 0, hydra_a (n + 2) - 1⟩ := by
  induction n with
  | zero =>
    -- hydra_b(2) = 1, hydra_a(2) = 2
    -- Need: (2, 0, 0, 0, 1) ⊢* (1+1, 0, 0, 0, 2-1) = (2, 0, 0, 0, 1)
    have hb2 : hydra_b 2 = 1 := by decide
    have ha2 : hydra_a 2 = 2 := by decide
    rw [ha2, hb2]; finish
  | succ n ih =>
    have hb' : ∀ k, k ≤ n + 2 → hydra_b k ≥ 0 := fun k hk => hb k (by omega)
    apply stepStar_trans (ih hb')
    exact canonical_round n (hb (n + 2) (by omega)) (hb (n + 3) (by omega))

-- Even round halts when B = 0
private theorem round_even_halts (K : ℕ) :
    halts fm (⟨1, 0, 0, 0, 2 * K + 1⟩ : Q) :=
  stepStar_halts (round_even K 0) (halted_halts (halted_zero _))

-- First time hydra_b < 0 must come from an even step with hydra_b = 0
private theorem first_neg_is_even (n : ℕ)
    (hbprev : hydra_b n ≥ 0)
    (hbneg : hydra_b (n + 1) < 0) :
    hydra_a n % 2 = 0 ∧ hydra_b n = 0 := by
  rw [hydra_b_step] at hbneg
  split_ifs at hbneg with h
  · exact ⟨h, by omega⟩
  · omega

-- ============================================================
-- Main theorem
-- ============================================================

theorem nonhalt_iff_hydra : ¬halts fm c₀ ↔ prop_hydra := by
  rw [prop_hydra_iff]
  constructor
  · -- Forward: ¬halts → ∀ n, hydra_b n ≥ 0
    -- By contrapositive
    intro hnh n
    by_contra hlt
    push_neg at hlt
    apply hnh
    -- Find the first index m with hydra_b(m) < 0
    have hexists : ∃ m, hydra_b m < 0 := ⟨n, hlt⟩
    set m := Nat.find hexists with hm_def
    have hmneg : hydra_b m < 0 := Nat.find_spec hexists
    have hmin : ∀ k, k < m → ¬(hydra_b k < 0) := fun k hk => Nat.find_min hexists hk
    -- All k < m have hydra_b(k) ≥ 0
    have hball : ∀ k, k < m → hydra_b k ≥ 0 := by
      intro k hk; exact Int.not_lt.mp (hmin k hk)
    -- m ≥ 2 (hydra_b(0) = 0 ≥ 0 and hydra_b(1) = 2 ≥ 0)
    have hm2 : m ≥ 2 := by
      rcases m with _ | _ | m
      · simp [hydra_b] at hmneg
      · simp [hydra_b, hydra_a] at hmneg
      · omega
    -- hydra_b(m-1) ≥ 0 and hydra_b(m) < 0
    have hbm1 : hydra_b (m - 1) ≥ 0 := hball (m - 1) (by omega)
    have hm_eq : (m - 1) + 1 = m := by omega
    have ⟨heven, hb0⟩ := first_neg_is_even (m - 1) hbm1 (by rw [hm_eq]; exact hmneg)
    -- m ≥ 4 (m=2 → hydra_b(1)=2≠0, m=3 → hydra_b(2)=1≠0)
    have hm4 : m ≥ 4 := by
      rcases m with _ | _ | _ | _ | m
      · omega
      · omega
      · simp [hydra_b, hydra_a] at hb0
      · simp [hydra_b, hydra_a] at hb0
      · omega
    -- The FM reaches the canonical state for step m-1
    have ha_ge2 : hydra_a (m - 1) ≥ 2 := hydra_a_ge_2 (m - 1) (by omega)
    have hK : hydra_a (m - 1) - 1 = 2 * (hydra_a (m - 1) / 2 - 1) + 1 := by omega
    -- reach_canonical (m-3): reaches canonical state (m-3)+2 = m-1
    have hreach := reach_canonical (m - 3) (fun k hk => hball k (by omega))
    rw [show m - 3 + 2 = m - 1 from by omega] at hreach
    rw [show (hydra_b (m - 1)).toNat = 0 from by omega] at hreach
    rw [hK] at hreach
    exact stepStar_halts (stepStar_trans bootstrap hreach) (round_even_halts (hydra_a (m - 1) / 2 - 1))
  · -- Backward: ∀ n, hydra_b n ≥ 0 → ¬halts
    intro hb
    apply stepStar_not_halts_not_halts bootstrap
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n => (⟨(hydra_b (n + 2)).toNat + 1, 0, 0, 0, hydra_a (n + 2) - 1⟩ : Q)) 0
    intro n
    exact ⟨n + 1, stepStar_stepPlus (canonical_round n (hb (n + 2)) (hb (n + 3))) (canonical_ne n)⟩

end Sz22_2003_unofficial_29
