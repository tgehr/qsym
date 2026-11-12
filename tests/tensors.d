module tensor_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:

private struct Case{ string name,source,expected,variables; }
private Case[] cases(){
	return [
		Case("TupleType","ℝ×ℕ","ℝ×ℕ"),
		Case("UniformType","ℕ×ℕ×ℕ","ℕ^3"),
		Case("CompatibleType","ℕ×ℕ×ℕ=ℕ^3","true"),
		Case("DifferentShape","ℕ^2=ℕ^3","false"),
		Case("DimensionConstant","ℝ^(2+1)=ℝ^3","true"),
		Case("DimensionParameter","ℝ^(n+1)","ℝ^(n+1)","n:ℕ"),
		Case("DimensionProduct","ℝ^(m*n)","ℝ^(m*n)","m:ℕ,n:ℕ"),
		Case("DimensionEquality","ℝ^n=ℝ^m","(ℝ^n=ℝ^m)","n:ℕ,m:ℕ"),
		Case("DimensionZero","ℝ^n=ℝ^0","(ℝ^n=ℝ^0)","n:ℕ"),
		Case("NestedVectorType","((ℝ^2)^2)^2","(ℝ^2)^(2×2)"),
		Case("NestedVectorLambda","λ(x:(ℝ^(m×n))^k).x","λ(x:(ℝ^n)^(k×m)). x","n:ℕ,m:ℕ,k:ℕ"),
		Case("Unit","()","()"),
		Case("Singleton","(1,)","(1,)"),
		Case("Vector","(1,2,3)","(1,2,3)"),
		Case("MixedTuple","(1,true)","((1,true):ℕ×𝔹)"),
		Case("NumericTuple","((1,2):ℝ×ℕ)","(((1:ℝ),2):ℝ×ℕ)"),
		Case("RealVector","((1,2):ℝ^2)","((1:ℝ),(2:ℝ))"),
		Case("EmptyVector","(():ℝ^0)","(():ℝ^0)"),
		Case("Project","get((1,2,3),1)","2"),
		Case("ProjectTuple","get(((1,2):ℝ×ℕ),1)","2"),
		Case("ProjectGlobal","get(t,1)","get(t,1)","t:ℝ×ℕ"),
		Case("ProjectLambda","λ(t:ℝ×ℕ).get(t,1)","λ(t:ℝ×ℕ). get(t,1)"),
		Case("VectorLambda","λ(x:ℝ^2).dot(x,x)","λ(x:ℝ^2). dot(x,x)"),
		Case("VectorBeta","(λ(x:ℝ^2).dot(x,x))((3,4))","25"),
		Case("Add","(1,2,3)+(4,5,6)","(5,7,9)"),
		Case("Hadamard","(1,2,3)·(4,5,6)","(4,10,18)"),
		Case("MatrixHadamard","((1,2),(3,4))·((1,2),(3,4))","((1,4),(9,16))"),
		Case("Dot","dot((1,2,3),(4,5,6))","32"),
		Case("DotEmpty","dot((():ℝ^0),(():ℝ^0))","0"),
		Case("DotInteger","dot((-1,2),(3,-4))","-11"),
		Case("DotRational","dot((1/2,1/3),(2/3,3/4))","7/12"),
		Case("DotReal","dot(((1,2):ℝ^2),((3,4):ℝ^2))","11"),
		Case("DotComplex","dot((1,ⅈ),(ⅈ,1))","0"),
		Case("DotComplexDual","dot((ⅈ,),(1,))","-ⅈ"),
		Case("DotComplexNorm","dot((1,ⅈ),(1,ⅈ))","2"),
		Case("DotComplexCasts","dot((1,2,ⅈ),(ⅈ,1,2))","2-ⅈ"),
		Case("DotVariables","dot((x,y),(x,y))","x^2+y^2","x:ℝ,y:ℝ"),
		Case("MatrixComplex","((ⅈ,1),(1,ⅈ))@(1,ⅈ)","(2·ⅈ,(0:ℂ))"),
		Case("MatVec","((1,2),(3,4))@(5,6)","(17,39)"),
		Case("MatVecRectangle","((1,2,3),(4,5,6))@(7,8,9)","(50,122)"),
		Case("MatMul","((1,2),(3,4))@((5,6),(7,8))","((19,22),(43,50))"),
		Case("MatMulRectangle","((1,2,3),(4,5,6))@((7,),(8,),(9,))","((50,),(122,))"),
		Case("MatrixPowerZero","((1,2),(3,4))^0","((1,0),(0,1))"),
		Case("MatrixPowerFive","((1,1),(1,0))^5","((8,5),(5,3))"),
		Case("FibonacciTen","get(((1,1),(1,0))^10@(1,0),1)","55"),
		Case("EmptyInnerDimension","((((),()):ℝ^(2×0)))@(():ℝ^0)","((0:ℝ),(0:ℝ))"),
		Case("SymbolicMatVec","A@x","(A@x)","n:ℕ,m:ℕ,x:ℝ^n,A:ℝ^(m×n)"),
		Case("SymbolicMatMul","A@B","(A@B)","n:ℕ,m:ℕ,k:ℕ,A:ℝ^(m×n),B:ℝ^(n×k)"),
		Case("SymbolicHadamard","x·x","(x·x)","n:ℕ,x:ℝ^n"),
		Case("SymbolicDot","dot(x,x)","dot(x,x)","n:ℕ,x:ℝ^n"),
		Case("SymbolicComplexDot","dot(x,x)","dot(x,x)","n:ℕ,x:ℂ^n"),
		Case("SymbolicPower","A^n","(A^n)","n:ℕ,m:ℕ,A:ℝ^(m×m)"),
		Case("VectorEquality","x=x","true","n:ℕ,x:ℝ^n"),
		Case("VectorEmptySet","{v:ℝ^n|true}={v:ℝ^n|false}","false","n:ℕ"),
		Case("TupleEmptySet","{t:ℝ×ℕ|true}={t:ℝ×ℕ|false}","false"),
		Case("ShapeCapture","λ(n:ℕ).A","λ(n1:ℕ). A","n:ℕ,A:ℝ^n"),
		Case("DependentCutoff","λ(v:ℝ^n).μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then 0 else if k≤10 then f(k sub 1) else f(k+1)","λ(v:ℝ^n). λ(k:{k:ℕ | k≤10}). 0","n:ℕ"),
		Case("RecurrenceVector","((μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then 3 else f(k sub 1)+2)(3),2)","(9,2)"),
		Case("TupleUndefined","defined((undefined(ℝ),1))","false"),
		Case("VectorUndefined","defined(((1/0,1):ℝ^2))","false"),
		Case("IndexOutside","defined(get((1,2),2))","false"),
		Case("IndexNegative","defined(get((1,2),0 sub 1))","false"),
		Case("UnitDefined","defined(())","true"),
		Case("EmptyDefined","defined((():ℝ^0))","true")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true)),output=s.format(a,r); enforce(!r.exhausted,c.name~" exhausted");
		enforce(output==c.expected,c.name~": "~output);
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip: "~s.format(a,again));
		if(!r.scalarOnly&&!r.lowered){
			enforce(!again.scalarOnly&&!again.lowered&&r.bindings.type(r.reduction.output)==again.bindings.type(again.reduction.output),c.name~" round-trip type");
			enforce(r.bindings.normalize(r.reduction.output,4096,true).output==r.reduction.output,c.name~" not normalized");
		}
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run();
	foreach(source;["(1,2)+(1,)","((1,2),(3,4))@(1,)","((1,2,3),(4,5,6))^2",
		"(1,2)@(3,4)","get((1,2),-1)","get((true,1),2)","((1,2):ℝ^3)","ℝ^(-1)",
		"λ(n:ℕ).λ(x:ℝ^n).x","((true,1):ℝ^2)","dot((true,false),(true,false))"]){
		auto owner=Session.open(); FunctionSyntax s; assertThrown(s.run(owner.arena,source));
	}
	FunctionSyntax s; s.declare("n:ℕ,x:ℝ^n"); assertThrown(s.declare("n:ℝ"));
	assertThrown(s.declare("bad:ℝ^(n sub 1)")); assertThrown(s.declare("bad:ℝ^z"));
	FunctionSyntax staged; assertThrown(staged.declare("n:ℕ,A:ℝ^n,bad:ℝ^(n sub 1)"));
	staged.declare("m:ℕ,A:ℝ^m"); enforce(staged.typeName(staged.functions[0].type)=="ℝ^m","failed declaration leaked a dimension name");
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/tensors"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," tensor certificates"); return 0;
}
