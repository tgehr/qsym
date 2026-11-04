module qsym.tools.unicode;
import std.string:startsWith;
@safe:

struct Symbol{ string key,text; }
// Agda/TeX-style spellings; this is data for input, not parser syntax.
immutable Symbol[] symbols=[
	Symbol("alpha","α"),Symbol("beta","β"),Symbol("gamma","γ"),Symbol("delta","δ"),
	Symbol("epsilon","ε"),Symbol("zeta","ζ"),Symbol("eta","η"),Symbol("theta","θ"),
	Symbol("iota","ι"),Symbol("kappa","κ"),Symbol("lambda","λ"),Symbol("mu","μ"),
	Symbol("nu","ν"),Symbol("xi","ξ"),Symbol("omicron","ο"),Symbol("pi","π"),
	Symbol("rho","ρ"),Symbol("sigma","σ"),Symbol("tau","τ"),Symbol("upsilon","υ"),
	Symbol("phi","φ"),Symbol("chi","χ"),Symbol("psi","ψ"),Symbol("omega","ω"),
	Symbol("Alpha","Α"),Symbol("Beta","Β"),Symbol("Gamma","Γ"),Symbol("Delta","Δ"),
	Symbol("Epsilon","Ε"),Symbol("Zeta","Ζ"),Symbol("Eta","Η"),Symbol("Theta","Θ"),
	Symbol("Iota","Ι"),Symbol("Kappa","Κ"),Symbol("Lambda","Λ"),Symbol("Mu","Μ"),
	Symbol("Nu","Ν"),Symbol("Xi","Ξ"),Symbol("Omicron","Ο"),Symbol("Pi","Π"),
	Symbol("Rho","Ρ"),Symbol("Sigma","Σ"),Symbol("Tau","Τ"),Symbol("Upsilon","Υ"),
	Symbol("Phi","Φ"),Symbol("Chi","Χ"),Symbol("Psi","Ψ"),Symbol("Omega","Ω"),
	Symbol("varepsilon","ϵ"),Symbol("vartheta","ϑ"),Symbol("varphi","ϕ"),Symbol("varsigma","ς"),
	Symbol("Gl","λ"),Symbol("GL","Λ"),Symbol("Ga","α"),Symbol("Gb","β"),
	Symbol("Gg","γ"),Symbol("Gd","δ"),Symbol("Gp","π"),Symbol("Gr","ρ"),
	Symbol("bR","ℝ"),Symbol("bC","ℂ"),Symbol("bN","ℕ"),Symbol("bZ","ℤ"),Symbol("bQ","ℚ"),Symbol("bB","𝔹"),
	Symbol("mathbb{R}","ℝ"),Symbol("mathbb{C}","ℂ"),Symbol("mathbb{N}","ℕ"),Symbol("mathbb{Z}","ℤ"),
	Symbol("mathbb{Q}","ℚ"),Symbol("mathbb{B}","𝔹"),
	Symbol("cdot","·"),Symbol(".","·"),Symbol("times","×"),Symbol("x","×"),Symbol("div","÷"),
	Symbol("ne","≠"),Symbol("neq","≠"),Symbol("!=","≠"),Symbol("le","≤"),Symbol("leq","≤"),Symbol("<=","≤"),
	Symbol("ge","≥"),Symbol("geq","≥"),Symbol(">=","≥"),Symbol("equiv","≡"),Symbol("approx","≈"),
	Symbol("neg","¬"),Symbol("not","¬"),Symbol("and","∧"),Symbol("land","∧"),Symbol("wedge","∧"),
	Symbol("or","∨"),Symbol("lor","∨"),Symbol("vee","∨"),
	Symbol("to","→"),Symbol("rightarrow","→"),Symbol("r-","→"),Symbol("->","→"),
	Symbol("leftarrow","←"),Symbol("l-","←"),Symbol("<-","←"),Symbol("mapsto","↦"),Symbol("r-|","↦"),
	Symbol("Rightarrow","⇒"),Symbol("r=","⇒"),Symbol("=>","⇒"),Symbol("Leftarrow","⇐"),Symbol("l=","⇐"),
	Symbol("leftrightarrow","↔"),Symbol("<->","↔"),Symbol("iff","⇔"),Symbol("<=>","⇔"),
	Symbol("uparrow","↑"),Symbol("u","↑"),Symbol("downarrow","↓"),Symbol("d","↓"),
	Symbol("forall","∀"),Symbol("all","∀"),Symbol("exists","∃"),Symbol("in","∈"),Symbol("notin","∉"),
	Symbol("sum","∑"),Symbol("prod","∏"),Symbol("int","∫"),Symbol("infty","∞"),Symbol("infinity","∞"),
	Symbol("partial","∂"),Symbol("nabla","∇"),Symbol("sqrt","√"),Symbol("ii","ⅈ"),
	Symbol("langle","⟨"),Symbol("rangle","⟩"),Symbol("[","⟦"),Symbol("]","⟧"),
	Symbol("lfloor","⌊"),Symbol("rfloor","⌋"),Symbol("lceil","⌈"),Symbol("rceil","⌉"),
	Symbol("prime","′"),Symbol("'1","′"),Symbol("'2","″"),Symbol("'3","‴"),Symbol("...","…"),
	Symbol("_0","₀"),Symbol("_1","₁"),Symbol("_2","₂"),Symbol("_3","₃"),Symbol("_4","₄"),
	Symbol("_5","₅"),Symbol("_6","₆"),Symbol("_7","₇"),Symbol("_8","₈"),Symbol("_9","₉"),
	Symbol("_-","₋"),Symbol("_+","₊"),Symbol("_=","₌"),Symbol("_(","₍"),Symbol("_)","₎"),
	Symbol("_a","ₐ"),Symbol("_e","ₑ"),Symbol("_h","ₕ"),Symbol("_i","ᵢ"),Symbol("_j","ⱼ"),
	Symbol("_k","ₖ"),Symbol("_l","ₗ"),Symbol("_m","ₘ"),Symbol("_n","ₙ"),Symbol("_o","ₒ"),
	Symbol("_p","ₚ"),Symbol("_r","ᵣ"),Symbol("_s","ₛ"),Symbol("_t","ₜ"),Symbol("_u","ᵤ"),Symbol("_v","ᵥ"),Symbol("_x","ₓ"),
	Symbol("^0","⁰"),Symbol("^1","¹"),Symbol("^2","²"),Symbol("^3","³"),Symbol("^4","⁴"),
	Symbol("^5","⁵"),Symbol("^6","⁶"),Symbol("^7","⁷"),Symbol("^8","⁸"),Symbol("^9","⁹"),
	Symbol("^-","⁻"),Symbol("^-1","⁻¹"),Symbol("^+","⁺"),Symbol("^=","⁼"),Symbol("^(","⁽"),Symbol("^)","⁾"),
	Symbol("^i","ⁱ"),Symbol("^n","ⁿ"),Symbol("\\","\\")
];

struct SymbolMatch{ string exact,unique; bool prefix,longer; }
SymbolMatch symbolMatch(string key){
	SymbolMatch m; size_t count;
	foreach(s;symbols) if(s.key.startsWith(key)){
		m.prefix=true; m.unique=s.text; ++count;
		if(s.key==key) m.exact=s.text; else m.longer=true;
	}
	if(count!=1) m.unique=null;
	return m;
}

unittest{
	import std.utf:validate;
	foreach(i,s;symbols){
		validate(s.text); assert(s.key.length&&s.text.length);
		foreach(t;symbols[0..i]) assert(s.key!=t.key,"duplicate Unicode spelling");
	}
	assert(symbolMatch("alpha").exact=="α");
	assert(symbolMatch("lam").unique=="λ");
	assert(symbolMatch("ne").exact=="≠"&&symbolMatch("ne").longer);
}
