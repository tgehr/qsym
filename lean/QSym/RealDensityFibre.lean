import QSym.Value

namespace QSym.Distribution

/-- The signed atomic coefficient at a query and its retained regular weight.
The obstruction to a Lebesgue density is tested after combining the atoms. -/
structure RealDensityFibre where
  charge : ℝ
  regular : Option ℝ

namespace RealDensityFibre

noncomputable def density (s : RealDensityFibre) : Option ℝ :=
  if s.charge = 0 then s.regular else none

theorem density_eq (s : RealDensityFibre) :
    s.density = (if s.charge = 0 then s.regular else none) := rfl

noncomputable def add (s t : RealDensityFibre) : RealDensityFibre :=
  ⟨s.charge + t.charge, Value.add s.regular t.regular⟩

noncomputable def scale (r : ℝ) (s : RealDensityFibre) : RealDensityFibre :=
  ⟨r * s.charge, Value.mul (some r) s.regular⟩

end RealDensityFibre
end QSym.Distribution
