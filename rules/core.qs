# Every rule becomes a native D matcher and a Lean theorem over partial values.
# Compilation checks syntax, types and structural decrease. Lean checks truth.
rule real_add_zero(x:Real):addR(x,real(0))=>x;
rule real_zero_add(x:Real):addR(real(0),x)=>x;
rule real_mul_one(x:Real):mulR(x,real(1))=>x;
rule real_one_mul(x:Real):mulR(real(1),x)=>x;
rule real_mask_true(x:Real):maskR(true,x)=>x;
rule real_mask_false(x:Real):maskR(false,x)=>real(0);
rule complex_add_zero(x:Complex):addC(x,complex(0,0))=>x;
rule complex_zero_add(x:Complex):addC(complex(0,0),x)=>x;
rule complex_mul_one(x:Complex):mulC(x,complex(1,0))=>x;
rule complex_one_mul(x:Complex):mulC(complex(1,0),x)=>x;
rule complex_mask_true(x:Complex):maskC(true,x)=>x;
rule complex_mask_false(x:Complex):maskC(false,x)=>complex(0,0);
rule complex_conj_conj(x:Complex):conj(conj(x))=>x;
rule erase_puncture(d:Density):forget(puncture(d))=>forget(d);
