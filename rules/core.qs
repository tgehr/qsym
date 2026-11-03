# Every rule becomes a native D matcher and a Lean theorem over partial values.
# Compilation checks syntax, types and structural decrease. Lean checks truth.
rule real_add_zero(x:ℝ):x+0⇒x;
rule real_zero_add(x:ℝ):0+x⇒x;
rule real_mul_one(x:ℝ):x·1⇒x;
rule real_one_mul(x:ℝ):1·x⇒x;
rule real_mask_true(x:ℝ):[true]·x⇒x;
rule real_mask_false(x:ℝ):[false]·x⇒0;
rule complex_add_zero(x:ℂ):x+0⇒x;
rule complex_zero_add(x:ℂ):0+x⇒x;
rule complex_mul_one(x:ℂ):x·1⇒x;
rule complex_one_mul(x:ℂ):1·x⇒x;
rule complex_mask_true(x:ℂ):[true]·x⇒x;
rule complex_mask_false(x:ℂ):[false]·x⇒0;
rule complex_conj_conj(x:ℂ):conj(conj(x))⇒x;
rule erase_puncture(d:Density):forget(puncture(d))⇒forget(d);
