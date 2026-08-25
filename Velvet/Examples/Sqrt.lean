import Velvet

/-- Squares are monotone on Nat. -/
theorem sq_le_sq {x y : Nat} (h : x ≤ y) : x * x ≤ y * y := Nat.mul_le_mul h h

/-- Cubes are monotone on Nat. -/
theorem cube_le_cube {x y : Nat} (h : x ≤ y) : x * x * x ≤ y * y * y :=
  calc x * x * x ≤ y * y * x := Nat.mul_le_mul_right x (sq_le_sq h)
    _ ≤ y * y * y := Nat.mul_le_mul (Nat.le_refl _) h

/-- A positive natural is at most its square. -/
theorem le_mul_self {n : Nat} (h : 0 < n) : n ≤ n * n :=
  Nat.le_mul_of_pos_right n h

/-- A positive natural is at most its cube. -/
theorem le_cube_self {n : Nat} (h : 0 < n) : n ≤ n * n * n :=
  Nat.le_trans (le_mul_self h) (Nat.le_mul_of_pos_right _ h)

/-- A cube bounded by `x` bounds the base itself. -/
theorem le_of_mul_self_cube_le {x y : Nat} (h : y * y * y ≤ x) : y ≤ x := by
  by_cases hp : 0 < y
  · have := le_cube_self hp; omega
  · omega

/-- A square bounded by `x` bounds the base itself. -/
theorem le_of_mul_self_le {x y : Nat} (h : y * y ≤ x) : y ≤ x := by
  by_cases hp : 0 < y
  · have := le_mul_self hp; omega
  · omega

set_option velvet.semantics.termination "total" in
method sqrt_total (x : Nat)
  returns (res : Nat)
  ensures sqrt_is: res * res ≤ x
  ensures sqrt_max1: ∀ i, i ≤ res → i * i ≤ x
  ensures sqrt_max2: ∀ i, i * i ≤ x → i ≤ res
do
  if x = 0 then
    return 0
  else
    let mut i : Nat := 0
    while' loop_cond: i * i ≤ x
      invariant below: ∀ j, j < i → j * j ≤ x
      decreasing by_x: x + 8 - i
    do
      i := i + 1
    return i - 1

prove_correct sqrt_total by
  vcgen_ [sqrt_total] with try finish
  case sqrt_max2 => rename_i x; intro i hi; have := le_of_mul_self_le hi; omega
  case sqrt_is =>
    rename_i x a
    by_cases ha : a = 0
    · simp [ha] at h_done_with
    · exact below (a - 1) (by omega)
  case sqrt_max2 =>
    rename_i x a
    intro i hi
    by_cases hlt : i < a
    · omega
    · have hsq : a * a ≤ i * i := sq_le_sq (by omega)
      have := h_done_with
      omega
  case by_x => rename_i x b; have hb : b ≤ x := le_of_mul_self_le loop_cond; omega

set_option velvet.semantics.termination "total" in
method cbrt (x : Nat)
  returns (res : Nat)
  ensures cbrt_is: res * res * res ≤ x
  ensures cbrt_max1: ∀ i, i ≤ res → i * i * i ≤ x
  ensures cbrt_max2: ∀ i, i * i * i ≤ x → i ≤ res
do
  if x = 0 then
    return 0
  else
    let mut i : Nat := 0
    while' loop_cond: i * i * i ≤ x
      invariant below: ∀ j, j < i → j * j * j ≤ x
      decreasing by_x: x + 8 - i
    do
      i := i + 1
    return i - 1

prove_correct cbrt by
  vcgen_ [cbrt] with try finish
  case cbrt_max2 => rename_i x; intro i hi; have := le_of_mul_self_cube_le hi; omega
  case cbrt_is =>
    rename_i x a
    by_cases ha : a = 0
    · simp [ha] at h_done_with
    · exact below (a - 1) (by omega)
  case cbrt_max2 =>
    rename_i x a
    intro i hi
    by_cases hlt : i < a
    · omega
    · have hcb : a * a * a ≤ i * i * i := cube_le_cube (by omega)
      have := h_done_with
      omega
  case by_x => rename_i x b; have hb : b ≤ x := le_of_mul_self_cube_le loop_cond; omega

set_option velvet.semantics.termination "total" in
method sqrt_bn (x : Nat) (bnd : Nat)
  returns (res : Nat)
  requires bnd_pos: x < bnd * bnd
  ensures bn_is: res * res ≤ x
  ensures bn_max1: ∀ i, i ≤ res → i * i ≤ x
  ensures bn_max2: ∀ i, i * i ≤ x → i ≤ res
do
  let mut l : Nat := 0
  let mut r : Nat := bnd
  while' loop_cond: 1 < r - l
    invariant low_ok: l * l ≤ x
    invariant high_ok: x < r * r
    invariant low_max: ∀ i, i ≤ l → i * i ≤ x
    decreasing by_width: r - l
  do
    let m := (r + l) / 2
    if m * m ≤ x then
      l := m
    else
      r := m
  return l

prove_correct sqrt_bn by
  vcgen_ [sqrt_bn] with try finish
  case bn_max2 =>
    rename_i x bnd a b
    intro i hi
    by_cases hle : i ≤ a
    · exact hle
    · have hsq : b * b ≤ i * i := sq_le_sq (by omega)
      omega
  case low_max =>
    rename_i x bnd a b
    intro i hi
    exact Nat.le_trans (sq_le_sq hi) if_cond
