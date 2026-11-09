import QSym.Functions

namespace QSym.FunctionOrder

def Increasing (f : Function1 ℝ ℝ) : Prop := StrictMonoOn f.value {x | f.domain x}
def Decreasing (f : Function1 ℝ ℝ) : Prop := StrictAntiOn f.value {x | f.domain x}

theorem sinh : Increasing Functions.sinhR := Real.sinh_strictMono.strictMonoOn _
theorem asinh : Increasing Functions.asinhR := Real.arsinh_strictMono.strictMonoOn _
theorem atan : Increasing Functions.atanR := Real.arctan_strictMono.strictMonoOn _
theorem asin : Increasing Functions.asinR := Real.strictMonoOn_arcsin
theorem acos : Decreasing Functions.acosR := Real.strictAntiOn_arccos

theorem tanh : Increasing Functions.tanhR := by
  intro x _ y _ hxy
  change Real.tanh x < Real.tanh y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  have h := Real.sinh_pos_iff.mpr (sub_pos.mpr hxy)
  rw [Real.sinh_sub] at h
  nlinarith

theorem acosh : Increasing Functions.acoshR := by
  intro x hx y hy hxy
  change 1≤x at hx
  change 1≤y at hy
  apply Real.log_lt_log
  · have := Real.sqrt_nonneg (x^2-1); linarith
  · exact add_lt_add_of_lt_of_le hxy (Real.sqrt_le_sqrt (by nlinarith))

theorem atanh : Increasing Functions.atanhR := by
  intro x hx y hy hxy
  change -1<x ∧ x<1 at hx
  change -1<y ∧ y<1 at hy
  change (Real.log (1+x)-Real.log (1-x))/2 < (Real.log (1+y)-Real.log (1-y))/2
  have hp := Real.log_lt_log (by linarith [hx.1] : 0<1+x) (by linarith : 1+x<1+y)
  have hm := Real.log_lt_log (by linarith [hy.2] : 0<1-y) (by linarith : 1-y<1-x)
  linarith

private theorem cube_root_cube {x : ℝ} (hx : 0≤x) : (x^(1/3 : ℝ))^3=x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem cbrt_cube (x : ℝ) : (Functions.cbrtR.value x)^3=x := by
  unfold Functions.cbrtR
  dsimp
  split_ifs with hx
  · rw [neg_pow, cube_root_cube (by linarith : 0≤-x)]
    norm_num
  · exact cube_root_cube (le_of_not_gt hx)

theorem cbrt : Increasing Functions.cbrtR := by
  intro x _ y _ hxy
  apply (show Odd 3 from ⟨1, rfl⟩).pow_lt_pow.mp
  simpa only [cbrt_cube] using hxy

theorem erf : Increasing Functions.erfR := by
  intro x _ y _ hxy
  have hc : Continuous (fun t : ℝ => Real.exp (-t^2)) := by fun_prop
  have hp := intervalIntegral.intervalIntegral_pos_of_pos (hc.intervalIntegrable x y)
    (fun t => Real.exp_pos (-t^2)) hxy
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ:=MeasureTheory.volume)
    (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x y)
  apply mul_lt_mul_of_pos_left (by linarith [hp, ha])
  exact div_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)

theorem erfc : Decreasing Functions.erfcR := by
  intro x _ y _ hxy
  exact sub_lt_sub_left (erf trivial trivial hxy) 1

end QSym.FunctionOrder
