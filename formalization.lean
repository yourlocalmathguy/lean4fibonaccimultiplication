import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FibonacciMultiplication

/-- Knuth's Fibonacci multiplication. -/
noncomputable def fibMul (a b : ℕ) : ℕ :=
  (a.zeckendorf.flatMap fun i =>
    b.zeckendorf.map fun j => Nat.fib (i + j)).sum

private theorem sum_flatMap_nil (l : List ℕ) :
    (l.flatMap (fun _ : ℕ => ([] : List ℕ))).sum = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.nil_append]
      exact ih

theorem fibMul_zero (a : ℕ) : fibMul a 0 = 0 := by
  unfold fibMul
  simp only [Nat.zeckendorf_zero, List.map_nil]
  exact sum_flatMap_nil a.zeckendorf

theorem zero_fibMul (b : ℕ) : fibMul 0 b = 0 := by
  simp [fibMul]

private theorem sum_flatMap_cons
    (l : List ℕ) (f : ℕ → ℕ) (g : ℕ → List ℕ) :
    (l.flatMap fun x => f x :: g x).sum =
      (l.map f).sum + (l.flatMap g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons,
        List.sum_append, List.sum_cons]
      rw [ih]
      ac_rfl

private theorem sum_flatMap_map_comm
    (l₁ l₂ : List ℕ) (f : ℕ → ℕ → ℕ) :
    (l₁.flatMap fun i => l₂.map fun j => f i j).sum =
      (l₂.flatMap fun j => l₁.map fun i => f i j).sum := by
  induction l₁ generalizing l₂ with
  | nil =>
      exact (sum_flatMap_nil l₂).symm
  | cons x xs ih =>
      cases l₂ with
      | nil =>
          exact sum_flatMap_nil xs
      | cons y ys =>
          simp only [List.flatMap_cons, List.map_cons,
            List.sum_append, List.sum_cons]

          rw [sum_flatMap_cons xs
            (fun i => f i y)
            (fun i => ys.map fun j => f i j)]

          rw [sum_flatMap_cons ys
            (fun j => f x j)
            (fun j => xs.map fun i => f i j)]

          rw [ih ys]
          ac_rfl

theorem fibMul_comm (a b : ℕ) : fibMul a b = fibMul b a := by
  unfold fibMul
  simpa [Nat.add_comm] using
    (sum_flatMap_map_comm a.zeckendorf b.zeckendorf
      (fun i j => Nat.fib (i + j)))
/-- The threefold Fibonacci sum over three Zeckendorf representations. -/
private def fibTripleLists
    (xs ys zs : List ℕ) : ℕ :=
  (xs.map fun i =>
    (ys.map fun j =>
      (zs.map fun k => Nat.fib (i + j + k)).sum).sum).sum

private theorem sum_map_sum_eq_flatMap_sum
    (xs ys : List ℕ) (f : ℕ → ℕ → ℕ) :
    ((xs.map fun x => (ys.map fun y => f x y).sum).sum) =
      (xs.flatMap fun x => ys.map fun y => f x y).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons,
        List.flatMap_cons, List.sum_append]
      rw [ih]

private theorem sum_map_sum_comm
    (xs ys : List ℕ) (f : ℕ → ℕ → ℕ) :
    ((xs.map fun x => (ys.map fun y => f x y).sum).sum) =
      ((ys.map fun y => (xs.map fun x => f x y).sum).sum) := by
  calc
    _ = (xs.flatMap fun x => ys.map fun y => f x y).sum :=
      sum_map_sum_eq_flatMap_sum xs ys f
    _ = (ys.flatMap fun y => xs.map fun x => f x y).sum :=
      sum_flatMap_map_comm xs ys f
    _ = _ :=
      (sum_map_sum_eq_flatMap_sum ys xs
        (fun y x => f x y)).symm

private theorem fibTripleLists_swap12
    (xs ys zs : List ℕ) :
    fibTripleLists xs ys zs = fibTripleLists ys xs zs := by
  simpa [fibTripleLists, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using
    (sum_map_sum_comm xs ys
      (fun i j =>
        (zs.map fun k => Nat.fib (i + j + k)).sum))

private theorem fibTripleLists_swap23
    (xs ys zs : List ℕ) :
    fibTripleLists xs ys zs = fibTripleLists xs zs ys := by
  induction xs with
  | nil =>
      simp [fibTripleLists]
  | cons i is ih =>
      have hhead :
          (ys.map fun j =>
            (zs.map fun k => Nat.fib (i + j + k)).sum).sum =
          (zs.map fun k =>
            (ys.map fun j => Nat.fib (i + k + j)).sum).sum := by
        simpa [Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using
          (sum_map_sum_comm ys zs
            (fun j k => Nat.fib (i + j + k)))

      change
        (ys.map fun j =>
          (zs.map fun k => Nat.fib (i + j + k)).sum).sum
            + fibTripleLists is ys zs =
        (zs.map fun k =>
          (ys.map fun j => Nat.fib (i + k + j)).sum).sum
            + fibTripleLists is zs ys

      rw [hhead, ih]

private theorem fibTripleLists_cyclic
    (xs ys zs : List ℕ) :
    fibTripleLists xs ys zs = fibTripleLists ys zs xs := by
  calc
    fibTripleLists xs ys zs =
        fibTripleLists ys xs zs :=
      fibTripleLists_swap12 xs ys zs
    _ = fibTripleLists ys zs xs :=
      fibTripleLists_swap23 ys xs zs

/-- Shift every Fibonacci index in the Zeckendorf representation of n by k. -/
private def fibShiftValue (k n : ℕ) : ℕ :=
  (n.zeckendorf.map fun i => Nat.fib (i + k)).sum

private theorem fibMul_as_partial_products (a b : ℕ) :
    fibMul a b =
      (b.zeckendorf.map fun j => fibShiftValue j a).sum := by
  unfold fibMul fibShiftValue
  calc
    _ = (b.zeckendorf.flatMap fun j =>
          a.zeckendorf.map fun i => Nat.fib (i + j)).sum := by
      exact sum_flatMap_map_comm
        a.zeckendorf b.zeckendorf
        (fun i j => Nat.fib (i + j))
    _ = (b.zeckendorf.map fun j =>
          (a.zeckendorf.map fun i => Nat.fib (i + j)).sum).sum :=
      (sum_map_sum_eq_flatMap_sum
        b.zeckendorf a.zeckendorf
        (fun j i => Nat.fib (i + j))).symm
private noncomputable def fibError (n : ℕ) : ℝ :=
  (n.zeckendorf.map fun i => Real.goldenConj ^ i).sum

private theorem list_sum_map_reverse
    (l : List ℕ) (f : ℕ → ℝ) :
    (l.reverse.map f).sum = (l.map f).sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.reverse_cons, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons]
      rw [ih]
      ac_rfl

private theorem abs_list_sum_le (l : List ℝ) :
    |l.sum| ≤ (l.map fun x => |x|).sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      calc
        |x + xs.sum| ≤ |x| + |xs.sum| :=
          abs_add_le _ _
        _ ≤ |x| + (xs.map fun x => |x|).sum := by
          linarith

private instance zeckendorfRel_trans :
    Trans (fun a b : ℕ => b + 2 ≤ a)
          (fun a b : ℕ => b + 2 ≤ a)
          (fun a b : ℕ => b + 2 ≤ a) where
  trans := by
    intro a b c hab hbc
    omega

private theorem pairwise_prefix_append_singleton
    {α : Type*} {R : α → α → Prop}
    (l : List α) (x : α)
    (h : List.Pairwise R (l ++ [x])) :
    List.Pairwise R l := by
  induction l with
  | nil =>
      simp
  | cons a as ih =>
      have h' : List.Pairwise R (a :: (as ++ [x])) := by
        simpa using h
      rcases List.pairwise_cons.mp h' with ⟨ha, htail⟩
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        exact ha b (by simp [hb])
      · exact ih htail

private theorem zeckendorf_reverse_data (n : ℕ) :
    (n.zeckendorf.reverse).Pairwise
      (fun i j : ℕ => i + 2 ≤ j) ∧
    (∀ i ∈ n.zeckendorf.reverse, 2 ≤ i) := by

  have hchain :
      List.IsChain (fun a b : ℕ => b + 2 ≤ a)
        (n.zeckendorf ++ [0]) :=
    Nat.isZeckendorfRep_zeckendorf n

  have hdesc :
      List.IsChain (fun a b : ℕ => b + 2 ≤ a)
        n.zeckendorf :=
    hchain.left_of_append

  have hdescPair :
      List.Pairwise (fun a b : ℕ => b + 2 ≤ a)
        n.zeckendorf :=
    hdesc.pairwise

  have hrev :
      List.Pairwise (fun i j : ℕ => i + 2 ≤ j)
        n.zeckendorf.reverse := by
    simpa using List.Pairwise.reverse hdescPair

  have hall :
      List.Pairwise (fun a b : ℕ => b + 2 ≤ a)
        (n.zeckendorf ++ [0]) :=
    hchain.pairwise

  have hmin : ∀ i ∈ n.zeckendorf, 2 ≤ i := by
    intro i hi
    have hrel :
        (fun a b : ℕ => b + 2 ≤ a) i 0 :=
      hall.rel_of_mem_append hi (by simp)
    simpa using hrel

  constructor
  · exact hrev
  · intro i hi
    have hi' : i ∈ n.zeckendorf := by
      simpa using hi
    exact hmin i hi'

private theorem sum_pow_sep_lt_aux
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hrel : q + q ^ 2 = 1) :
    ∀ (N : ℕ) (l : List ℕ), 2 ≤ N →
      l.Pairwise (fun i j => i + 2 ≤ j) →
      (∀ i ∈ l, N ≤ i) →
      (l.map fun i => q ^ i).sum < q ^ (N - 1) := by

  intro N l
  induction l generalizing N with
  | nil =>
      intro hN hp hmin
      simpa using pow_pos hq0 (N - 1)

  | cons i is ih =>
      intro hN hp hmin

      rcases List.pairwise_cons.mp hp with ⟨hhead, htail⟩

      have hi : N ≤ i :=
        hmin i (by simp)

      have htailBound :
          (is.map fun j => q ^ j).sum <
            q ^ ((i + 2) - 1) := by
        apply ih (i + 2)
        · omega
        · exact htail
        · intro j hj
          exact hhead j hj

      have hindex : (i + 2) - 1 = i + 1 := by omega
      rw [hindex] at htailBound

      have hi1 : i = (i - 1) + 1 := by omega
      have hi2 : i + 1 = (i - 1) + 2 := by omega

      have hpow1 :
          q ^ ((i - 1) + 1) =
            q ^ (i - 1) * q := by
        rw [pow_succ]

      have hpow2 :
          q ^ ((i - 1) + 2) =
            q ^ (i - 1) * q ^ 2 := by
        calc
          q ^ ((i - 1) + 2) =
              q ^ (((i - 1) + 1) + 1) := by
                congr 1

          _ = q ^ ((i - 1) + 1) * q := by
                rw [pow_succ]
          _ = (q ^ (i - 1) * q) * q := by
                rw [hpow1]
          _ = q ^ (i - 1) * q ^ 2 := by
                ring

      have hpowa :
          q ^ i = q ^ ((i - 1) + 1) :=
        congrArg (fun t : ℕ => q ^ t) hi1

      have hpowb :
          q ^ (i + 1) = q ^ ((i - 1) + 2) :=
        congrArg (fun t : ℕ => q ^ t) hi2

      have hpowid :
          q ^ i + q ^ (i + 1) = q ^ (i - 1) := by
        rw [hpowa, hpowb, hpow1, hpow2]
        rw [← mul_add, hrel, mul_one]

      have hpowle :
          q ^ (i - 1) ≤ q ^ (N - 1) :=
        pow_le_pow_of_le_one hq0.le hq1 (by omega)

      have hsumlt :
          q ^ i + (is.map fun j => q ^ j).sum <
            q ^ i + q ^ (i + 1) := by
        linarith
      simp only [List.map_cons, List.sum_cons]
      calc
        q ^ i + (is.map fun j => q ^ j).sum <
            q ^ i + q ^ (i + 1) := hsumlt
        _ = q ^ (i - 1) := hpowid
        _ ≤ q ^ (N - 1) := hpowle

private theorem golden_inv_rel :
    Real.goldenRatio⁻¹ +
      (Real.goldenRatio⁻¹) ^ 2 = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem fibError_abs_lt (n : ℕ) :
    |fibError n| < Real.goldenRatio⁻¹ := by
  let q : ℝ := Real.goldenRatio⁻¹

  have hq0 : 0 < q := by
    dsimp [q]
    exact inv_pos.mpr Real.goldenRatio_pos

  have hqφ : q * Real.goldenRatio = 1 := by
    dsimp [q]
    exact inv_mul_cancel₀ Real.goldenRatio_ne_zero

  have hq1 : q ≤ 1 := by
    by_contra h
    have hlt : 1 < q := lt_of_not_ge h
    have hpos :
        0 < (q - 1) * (Real.goldenRatio - 1) :=
      mul_pos
        (sub_pos.mpr hlt)
        (sub_pos.mpr Real.one_lt_goldenRatio)
    nlinarith

  have hrel : q + q ^ 2 = 1 := by
    simpa [q] using golden_inv_rel

  rcases zeckendorf_reverse_data n with ⟨hp, hmin⟩

  have hsum :
      (n.zeckendorf.reverse.map fun i => q ^ i).sum < q := by
    have hh :=
      sum_pow_sep_lt_aux q hq0 hq1 hrel
        2 n.zeckendorf.reverse (by omega) hp hmin
    simpa using hh

  have hψ : |Real.goldenConj| = q := by
    rw [abs_of_neg Real.goldenConj_neg]
    dsimp [q]
    exact Real.inv_goldenRatio.symm

  unfold fibError
  calc
    |(n.zeckendorf.map fun i => Real.goldenConj ^ i).sum|
        =
      |(n.zeckendorf.reverse.map
          fun i => Real.goldenConj ^ i).sum| := by
            congr 1
            exact (list_sum_map_reverse n.zeckendorf _).symm
    _ ≤
      (n.zeckendorf.reverse.map
        fun i => |Real.goldenConj ^ i|).sum := by
      simpa only [List.map_map, Function.comp_def] using
        (abs_list_sum_le
          (n.zeckendorf.reverse.map
            (fun i => Real.goldenConj ^ i)))
    _ =
      (n.zeckendorf.reverse.map fun i => q ^ i).sum := by
        simp [abs_pow, hψ]
    _ < q := hsum
private theorem nat_list_map_sum_cast
    {α : Type*} (l : List α) (f : α → ℕ) :
    ((l.map f).sum : ℝ) =
      (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

private theorem nat_zeckendorf_cast (n : ℕ) :
    (n : ℝ) =
      (n.zeckendorf.map fun i => (Nat.fib i : ℝ)).sum := by
  calc
    (n : ℝ) =
        (((n.zeckendorf.map Nat.fib).sum : ℕ) : ℝ) := by
          exact congrArg
            (fun m : ℕ => (m : ℝ))
            (Nat.sum_zeckendorf_fib n).symm
    _ = _ :=
      nat_list_map_sum_cast n.zeckendorf Nat.fib

private theorem fib_error_list (l : List ℕ) :
    (l.map fun i => (Nat.fib (i + 1) : ℝ)).sum -
      Real.goldenRatio *
        (l.map fun i => (Nat.fib i : ℝ)).sum =
      (l.map fun i => Real.goldenConj ^ i).sum := by
  induction l with
  | nil =>
      simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        ((Nat.fib (i + 1) : ℝ) +
            (is.map fun j => (Nat.fib (j + 1) : ℝ)).sum) -
          Real.goldenRatio *
            ((Nat.fib i : ℝ) +
              (is.map fun j => (Nat.fib j : ℝ)).sum)
            =
          ((Nat.fib (i + 1) : ℝ) -
              Real.goldenRatio * (Nat.fib i : ℝ)) +
            ((is.map fun j => (Nat.fib (j + 1) : ℝ)).sum -
              Real.goldenRatio *
                (is.map fun j => (Nat.fib j : ℝ)).sum) := by
                  ring
        _ = Real.goldenConj ^ i +
              (is.map fun j => Real.goldenConj ^ j).sum := by
                  rw [Real.fib_succ_sub_goldenRatio_mul_fib, ih]

private theorem fibShift_one_error (n : ℕ) :
    (fibShiftValue 1 n : ℝ) -
      Real.goldenRatio * (n : ℝ) =
      fibError n := by
  have hs :
      (fibShiftValue 1 n : ℝ) =
        (n.zeckendorf.map
          fun i => (Nat.fib (i + 1) : ℝ)).sum := by
    unfold fibShiftValue
    exact nat_list_map_sum_cast n.zeckendorf
      (fun i => Nat.fib (i + 1))

  rw [hs, nat_zeckendorf_cast n]
  unfold fibError
  exact fib_error_list n.zeckendorf

private theorem mul_sum_map
    (l : List ℕ) (c : ℝ) (f : ℕ → ℝ) :
    c * (l.map f).sum =
      (l.map fun x => c * f x).sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]

private theorem sum_map_mul_eq_flatMap_sum
    (xs ys : List ℕ) (f g : ℕ → ℝ) :
    (xs.map f).sum * (ys.map g).sum =
      (xs.flatMap fun i =>
        ys.map fun j => f i * g j).sum := by
  induction xs with
  | nil =>
      simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons,
        List.flatMap_cons, List.sum_append]
      calc
        (f i + (is.map f).sum) * (ys.map g).sum =
            f i * (ys.map g).sum +
              (is.map f).sum * (ys.map g).sum := by ring
        _ = (ys.map fun j => f i * g j).sum +
              (is.map f).sum * (ys.map g).sum := by
                rw [mul_sum_map]
        _ = (ys.map fun j => f i * g j).sum +
              (is.flatMap fun i => ys.map fun j => f i * g j).sum := by
                rw [ih]

private theorem fibError_mul (a b : ℕ) :
    fibError a * fibError b =
      (a.zeckendorf.flatMap fun i =>
        b.zeckendorf.map fun j =>
          Real.goldenConj ^ (i + j)).sum := by
  unfold fibError
  calc
    (a.zeckendorf.map fun i => Real.goldenConj ^ i).sum *
        (b.zeckendorf.map fun j => Real.goldenConj ^ j).sum
        =
      (a.zeckendorf.flatMap fun i =>
        b.zeckendorf.map fun j =>
          Real.goldenConj ^ i * Real.goldenConj ^ j).sum :=
      sum_map_mul_eq_flatMap_sum
        a.zeckendorf b.zeckendorf
        (fun i => Real.goldenConj ^ i)
        (fun j => Real.goldenConj ^ j)
    _ =
      (a.zeckendorf.flatMap fun i =>
        b.zeckendorf.map fun j =>
          Real.goldenConj ^ (i + j)).sum := by
            simp_rw [← pow_add]

private theorem double_sum_error (xs ys : List ℕ) :
    (xs.map fun i =>
      (ys.map fun j => (Nat.fib (i + j + 1) : ℝ)).sum).sum -
      Real.goldenRatio *
        (xs.map fun i =>
          (ys.map fun j => (Nat.fib (i + j) : ℝ)).sum).sum =
      (xs.flatMap fun i =>
        ys.map fun j => Real.goldenConj ^ (i + j)).sum := by
  induction xs with
  | nil =>
      simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons,
        List.flatMap_cons, List.sum_append]

      have hrow :
          (ys.map fun j => (Nat.fib (i + j + 1) : ℝ)).sum -
            Real.goldenRatio *
              (ys.map fun j => (Nat.fib (i + j) : ℝ)).sum =
          (ys.map fun j => Real.goldenConj ^ (i + j)).sum := by
        simpa [List.map_map, Function.comp_def,
          Nat.add_assoc] using
          (fib_error_list (ys.map fun j => i + j))

      calc
        _ =
          ((ys.map fun j => (Nat.fib (i + j + 1) : ℝ)).sum -
            Real.goldenRatio *
              (ys.map fun j => (Nat.fib (i + j) : ℝ)).sum) +
          ((is.map fun x =>
              (ys.map fun j => (Nat.fib (x + j + 1) : ℝ)).sum).sum -
            Real.goldenRatio *
              (is.map fun x =>
                (ys.map fun j => (Nat.fib (x + j) : ℝ)).sum).sum) := by
                  ring
        _ =
          (ys.map fun j => Real.goldenConj ^ (i + j)).sum +
            (is.flatMap fun x =>
              ys.map fun j => Real.goldenConj ^ (x + j)).sum := by
                  rw [hrow, ih]

private theorem fibMul_cast_nested (a b : ℕ) :
    (fibMul a b : ℝ) =
      (b.zeckendorf.map fun j =>
        (a.zeckendorf.map fun i =>
          (Nat.fib (i + j) : ℝ)).sum).sum := by
  calc
    (fibMul a b : ℝ) =
        ((b.zeckendorf.map fun j => fibShiftValue j a).sum : ℝ) := by
          exact congrArg
            (fun n : ℕ => (n : ℝ))
            (fibMul_as_partial_products a b)
    _ = (b.zeckendorf.map fun j =>
          (fibShiftValue j a : ℝ)).sum :=
      nat_list_map_sum_cast b.zeckendorf
        (fun j => fibShiftValue j a)
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      unfold fibShiftValue
      exact nat_list_map_sum_cast a.zeckendorf
        (fun i => Nat.fib (i + j))

private theorem fibMul_shift_one_error (a b : ℕ) :
    ((b.zeckendorf.map fun j =>
        fibShiftValue (j + 1) a).sum : ℝ) -
      Real.goldenRatio * (fibMul a b : ℝ) =
      fibError a * fibError b := by

  have hshift :
      ((b.zeckendorf.map fun j =>
          fibShiftValue (j + 1) a).sum : ℝ) =
        (b.zeckendorf.map fun j =>
          (a.zeckendorf.map fun i =>
            (Nat.fib (i + j + 1) : ℝ)).sum).sum := by
    calc
      _ = (b.zeckendorf.map fun j =>
            (fibShiftValue (j + 1) a : ℝ)).sum :=
        nat_list_map_sum_cast b.zeckendorf
          (fun j => fibShiftValue (j + 1) a)
      _ = _ := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro j hj
        unfold fibShiftValue
        simpa [Nat.add_assoc] using
          (nat_list_map_sum_cast a.zeckendorf
            (fun i => Nat.fib (i + (j + 1))))

  calc
    _ =
        (b.zeckendorf.map fun j =>
          (a.zeckendorf.map fun i =>
            (Nat.fib (i + j + 1) : ℝ)).sum).sum -
        Real.goldenRatio *
          (b.zeckendorf.map fun j =>
            (a.zeckendorf.map fun i =>
              (Nat.fib (i + j) : ℝ)).sum).sum := by
          rw [hshift, fibMul_cast_nested]
    _ =
        (b.zeckendorf.flatMap fun j =>
          a.zeckendorf.map fun i =>
            Real.goldenConj ^ (j + i)).sum := by
          simpa only [Nat.add_comm] using
            (double_sum_error b.zeckendorf a.zeckendorf)
    _ = fibError b * fibError a :=
      (fibError_mul b a).symm
    _ = fibError a * fibError b :=
      mul_comm _ _

private theorem clean_partial_products_one (a b : ℕ) :
    fibShiftValue 1 (fibMul a b) =
      (b.zeckendorf.map fun j =>
        fibShiftValue (j + 1) a).sum := by

  let c : ℕ := fibMul a b
  let x : ℕ := fibShiftValue 1 c
  let y : ℕ :=
    (b.zeckendorf.map fun j => fibShiftValue (j + 1) a).sum
  let q : ℝ := Real.goldenRatio⁻¹

  have hq0 : 0 < q := by
    dsimp [q]
    exact inv_pos.mpr Real.goldenRatio_pos

  have hqrel : q + q ^ 2 = 1 := by
    simpa [q] using golden_inv_rel

  have hA : |fibError a| < q := by
    simpa [q] using fibError_abs_lt a

  have hB : |fibError b| < q := by
    simpa [q] using fibError_abs_lt b

  have hprod : |fibError a * fibError b| < q ^ 2 := by
    rw [abs_mul]

    have hpos1 :
        0 < q * (q - |fibError b|) :=
      mul_pos hq0 (sub_pos.mpr hB)

    have hpos2 :
        0 ≤ |fibError b| * (q - |fibError a|) :=
      mul_nonneg (abs_nonneg _) (le_of_lt (sub_pos.mpr hA))

    nlinarith

  have hxerr :
      (x : ℝ) -
        Real.goldenRatio * (c : ℝ) =
        fibError c := by
    dsimp [x, c]
    exact fibShift_one_error (fibMul a b)

  have hyerr :
      (y : ℝ) -
        Real.goldenRatio * (c : ℝ) =
        fibError a * fibError b := by
    dsimp [y, c]
    exact fibMul_shift_one_error a b

  have hleft :
      |(x : ℝ) -
        Real.goldenRatio * (c : ℝ)| < q := by
    rw [hxerr]
    simpa [q] using fibError_abs_lt c

  have hright :
      |(y : ℝ) -
        Real.goldenRatio * (c : ℝ)| < q ^ 2 := by
    rw [hyerr]
    exact hprod

  have hbridge :
      |Real.goldenRatio * (c : ℝ) - (y : ℝ)| =
        |(y : ℝ) - Real.goldenRatio * (c : ℝ)| := by
    rw [show Real.goldenRatio * (c : ℝ) - (y : ℝ) =
      -((y : ℝ) - Real.goldenRatio * (c : ℝ)) by ring]
    rw [abs_neg]

  have hdiff : |(x : ℝ) - (y : ℝ)| < 1 := by
    have hsum :
        (x : ℝ) - (y : ℝ) =
          ((x : ℝ) - Real.goldenRatio * (c : ℝ)) +
            (Real.goldenRatio * (c : ℝ) - (y : ℝ)) := by
      ring
    rw [hsum]
    calc
      _ ≤
          |(x : ℝ) - Real.goldenRatio * (c : ℝ)| +
            |Real.goldenRatio * (c : ℝ) - (y : ℝ)| :=
        abs_add_le _ _
      _ =
          |(x : ℝ) - Real.goldenRatio * (c : ℝ)| +
            |(y : ℝ) - Real.goldenRatio * (c : ℝ)| := by
              rw [hbridge]
      _ < q + q ^ 2 :=
        add_lt_add hleft hright
      _ = 1 := hqrel

  have hxy : x = y := by
    by_contra hne
    have hge : (1 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hnat : x + 1 ≤ y :=
          Nat.succ_le_of_lt hlt
        have hreal : (x : ℝ) + 1 ≤ (y : ℝ) := by
          exact_mod_cast hnat
        have hnonpos : (x : ℝ) - (y : ℝ) ≤ 0 := by
          linarith
        rw [abs_of_nonpos hnonpos]
        linarith
      · have hnat : y + 1 ≤ x :=
          Nat.succ_le_of_lt hgt
        have hreal : (y : ℝ) + 1 ≤ (x : ℝ) := by
          exact_mod_cast hnat
        have hnonneg : 0 ≤ (x : ℝ) - (y : ℝ) := by
          linarith
        rw [abs_of_nonneg hnonneg]
        linarith
    exact (not_lt_of_ge hge) hdiff

  simpa [x, y, c] using hxy
private theorem fibShiftValue_zero (n : ℕ) :
    fibShiftValue 0 n = n := by
  unfold fibShiftValue
  simpa using Nat.sum_zeckendorf_fib n

private theorem list_sum_fib_recurrence
    (l : List ℕ) (k : ℕ) :
    (l.map fun i => Nat.fib (i + (k + 2))).sum =
      (l.map fun i => Nat.fib (i + (k + 1))).sum +
      (l.map fun i => Nat.fib (i + k)).sum := by
  induction l with
  | nil =>
      simp
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]

      have h := Nat.fib_add_two (n := i + k)
      have hleft : i + (k + 2) = (i + k) + 2 := by omega
      have hright : i + (k + 1) = (i + k) + 1 := by omega

      have hfib :
          Nat.fib (i + (k + 2)) =
            Nat.fib (i + (k + 1)) + Nat.fib (i + k) := by
        rw [hleft, hright]
        simpa [Nat.add_comm] using h

      rw [hfib, ih]
      ring

private theorem fibShiftValue_add_two (k n : ℕ) :
    fibShiftValue (k + 2) n =
      fibShiftValue (k + 1) n + fibShiftValue k n := by
  unfold fibShiftValue
  exact list_sum_fib_recurrence n.zeckendorf k

private theorem list_sum_shift_recurrence
    (l : List ℕ) (a k : ℕ) :
    (l.map fun j => fibShiftValue (k + 2 + j) a).sum =
      (l.map fun j => fibShiftValue (k + 1 + j) a).sum +
      (l.map fun j => fibShiftValue (k + j) a).sum := by
  induction l with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.map_cons, List.sum_cons]

      have hleft : k + 2 + j = (k + j) + 2 := by omega
      have hright : k + 1 + j = (k + j) + 1 := by omega

      have hj :
          fibShiftValue (k + 2 + j) a =
            fibShiftValue (k + 1 + j) a +
              fibShiftValue (k + j) a := by
        rw [hleft, hright]
        exact fibShiftValue_add_two (k + j) a

      rw [hj, ih]
      ring

/-- Shift invariance for Fibonacci multiplication. -/
private theorem clean_partial_products
    (a b k : ℕ) :
    fibShiftValue k (fibMul a b) =
      (b.zeckendorf.map fun j =>
        fibShiftValue (k + j) a).sum := by

  let P : ℕ → ℕ := fun t =>
    fibShiftValue t (fibMul a b)
  let Q : ℕ → ℕ := fun t =>
    (b.zeckendorf.map fun j =>
      fibShiftValue (t + j) a).sum

  have h0 : P 0 = Q 0 := by
    dsimp [P, Q]
    rw [fibShiftValue_zero]
    simpa using fibMul_as_partial_products a b

  have h1 : P 1 = Q 1 := by
    dsimp [P, Q]
    simpa [Nat.add_comm] using clean_partial_products_one a b

  have hrecP (t : ℕ) :
      P (t + 2) = P (t + 1) + P t := by
    dsimp [P]
    exact fibShiftValue_add_two t (fibMul a b)

  have hrecQ (t : ℕ) :
      Q (t + 2) = Q (t + 1) + Q t := by
    dsimp [Q]
    exact list_sum_shift_recurrence b.zeckendorf a t

  have hpair :
      ∀ t, P t = Q t ∧ P (t + 1) = Q (t + 1) := by
    intro t
    induction t with
    | zero =>
        simpa using And.intro h0 h1
    | succ t ih =>
        refine ⟨?_, ?_⟩
        · simpa using ih.2
        · have hnext : P (t + 2) = Q (t + 2) := by
            calc
              P (t + 2) = P (t + 1) + P t := hrecP t
              _ = Q (t + 1) + Q t := by rw [ih.2, ih.1]
              _ = Q (t + 2) := (hrecQ t).symm
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext

  exact (hpair k).1

private theorem knuth_threefold_expansion
    (a b c : ℕ) :
    fibMul (fibMul a b) c =
      fibTripleLists
        a.zeckendorf b.zeckendorf c.zeckendorf := by
  calc
    fibMul (fibMul a b) c =
        (c.zeckendorf.map fun k =>
          fibShiftValue k (fibMul a b)).sum :=
      fibMul_as_partial_products (fibMul a b) c
    _ = (c.zeckendorf.map fun k =>
          (b.zeckendorf.map fun j =>
            fibShiftValue (k + j) a).sum).sum := by
              simp_rw [clean_partial_products]
    _ = fibTripleLists
          c.zeckendorf b.zeckendorf a.zeckendorf := by
              simp [fibTripleLists, fibShiftValue,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = fibTripleLists
          a.zeckendorf b.zeckendorf c.zeckendorf := by
              calc
                fibTripleLists c.zeckendorf b.zeckendorf a.zeckendorf =
                    fibTripleLists b.zeckendorf c.zeckendorf a.zeckendorf :=
                  fibTripleLists_swap12 _ _ _
                _ = fibTripleLists b.zeckendorf a.zeckendorf c.zeckendorf :=
                  fibTripleLists_swap23 _ _ _
                _ = fibTripleLists a.zeckendorf b.zeckendorf c.zeckendorf :=
                  fibTripleLists_swap12 _ _ _

/-- Fibonacci multiplication is associative. -/
theorem fibMul_assoc (a b c : ℕ) :
    fibMul (fibMul a b) c = fibMul a (fibMul b c) := by
  calc
    fibMul (fibMul a b) c =
        fibTripleLists
          a.zeckendorf b.zeckendorf c.zeckendorf :=
      knuth_threefold_expansion a b c
    _ = fibTripleLists
          b.zeckendorf c.zeckendorf a.zeckendorf :=
      fibTripleLists_cyclic
        a.zeckendorf b.zeckendorf c.zeckendorf
    _ = fibMul (fibMul b c) a :=
      (knuth_threefold_expansion b c a).symm
    _ = fibMul a (fibMul b c) :=
      fibMul_comm _ _

end FibonacciMultiplication
#eval Lean.versionString
#print axioms FibonacciMultiplication.fibMul_assoc
