module qsym.text;
import qsym.ir;
import qsym.spec:Parser,Pattern,Parameter;
import std.conv:to;
import std.exception:enforce;
@safe:

// Symbol indices stay stable across inputs. Arenas can be fresh for each line.
struct Syntax{
	Parameter[] variables;
	void declare(string source){
		auto added=Parser(source).parseParameters(),next=variables.dup;
		foreach(i,v;added){
			enforce(!v.natural&&(numeric(v.sort)||v.sort==Sort.boolean),"expected a scalar expression type");
			foreach(old;added[0..i]) enforce(old.name!=v.name,"duplicate variable: "~v.name);
			bool found;
			foreach(ref old;next) if(old.name==v.name){ old=v; found=true; break; }
			if(!found) next~=v;
		}
		variables=next;
	}
	Term parse(Arena a,string source){
		auto next=variables.dup;
		auto p=Parser(source).parseExpression(next);
		Term build(Pattern p){
			if(p.variable){
				foreach(i,v;next) if(v.name==p.name) return a.variable(v.sort,cast(uint)i);
				assert(0,"missing variable");
			}
			if(p.name=="nat") return a.natural_(p.args[0].number);
			if(p.name=="int") return a.integer(p.args[0].number);
			if(p.name=="rat") return a.rational(p.args[0].number,p.args[1].number);
			if(p.name=="real") return p.args.length==1?a.real_(p.args[0].number):a.real_(Rational(BigInt(p.args[0].number),BigInt(p.args[1].number)));
			if(p.name=="complex") return a.complex(p.args[0].number,p.args[1].number);
			if(p.name=="true"||p.name=="false") return a.boolean(p.name=="true");
			if(p.name=="lebesgue") return a.lebesgue();
			auto f=builtin(p.name);
			if(f!=Builtin.invalid){ Term[] args; foreach(arg;p.args) args~=build(arg); return a.call(f,args); }
			auto x=build(p.args[0]);
			if(p.name=="powN"||p.name=="powZ"||p.name=="powQ"||p.name=="powR"||p.name=="powC"){
				ulong exponent(Pattern q){
					if(q.name=="#") return cast(ulong)q.number;
					auto l=exponent(q.args[0]),r=exponent(q.args[1]);
					auto v=q.name=="natAdd"?l+r:l*r;
					enforce(v<=uint.max,"exponent exceeds uint range"); return v;
				}
				return a.pow(x,cast(uint)exponent(p.args[1]));
			}
			Term y; if(p.args.length==2) y=build(p.args[1]);
			switch(p.name){
				case "addR","addC":return a.add(x,y);
				case "mulR","mulC":return a.mul(x,y);
				case "invR","invC":return a.inv(x);
				case "nonzeroR","nonzeroC":return a.nonzero(x);
				case "maskN","maskZ","maskQ","maskR","maskC":return a.mask(x,y);
				case "absR":return a.abs(x);
				case "conj":return a.conj(x);
				case "not":return a.not_(x);
				case "and":return a.and_(x,y);
				case "or":return a.or_(x,y);
				case "ltR":return a.lt(x,y);
				case "leR":return a.le(x,y);
				case "puncture":return a.puncture(x);
				case "densityAt":return a.densityAt(x,y);
				case "forget":return a.forget(x);
				default:assert(0,"unsupported expression");
			}
		}
		auto result=build(p); variables=next; return result;
	}
	string format(Arena a,Term root){
		struct Piece{ string text; uint precedence=100; bool negative,iverson; }
		Piece[] memo=new Piece[a.length];
		bool[] symbolic=new bool[a.length];
		// A rigid spelling fixes its type before the surrounding context is
		// considered. In particular, sqrt(3) is real but 3^(1/2) is overloaded.
		bool[] rigid=new bool[a.length];
		string render(Piece p,uint precedence=0,bool magnitude=false){
			if(p.negative&&!magnitude){
				p.text="-"~(p.precedence<70?"("~p.text~")":p.text);
				if(p.precedence>80) p.precedence=80;
			}
			return p.precedence<precedence?"("~p.text~")":p.text;
		}
		string arg(uint id,uint precedence=0){ return render(memo[id],precedence); }
		Piece rational(Rational q){ return Piece((q<Rational(0)?-q:q).toString,q.integral?100:70,q<Rational(0)); }
		bool conversion(Node n){ return n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC; }
		Piece promoted(uint id,Sort expected,Sort minimum=Sort.natural){
			auto t=a.at(id),n=a.node(t);
			if(a.sort(t)!=expected) return memo[id];
			while(conversion(n)&&rigid[n.a]&&rank(a.sort(a.at(n.a)))>=rank(minimum)){ id=n.a; n=a.node(a.at(id)); }
			if(expected==Sort.complex&&a.isNumber(a.at(id))&&a.number(a.at(id)).im.zero)
				return rational(a.number(a.at(id)).re);
			return memo[id];
		}
		void pair(uint x,uint y,out Piece l,out Piece r){
			l=memo[x]; r=memo[y];
			// Keep one type anchor. Removing both embeddings could select a
			// different overload, even when the enclosing result is complex.
			bool anchor(uint id){
				auto t=a.at(id);
				return rigid[id]&&!conversion(a.node(t))&&!(a.sort(t)==Sort.complex&&a.isNumber(t)&&a.number(t).im.zero);
			}
			if(anchor(x)) r=promoted(y,a.sort(a.at(x)));
			else if(anchor(y)||!rigid[x]&&rigid[y]) l=promoted(x,a.sort(a.at(y)));
			else if(rigid[x]) r=promoted(y,a.sort(a.at(x)));
		}
		string expected(uint id,Sort s,uint precedence=0){ return render(promoted(id,s),precedence); }
		string exponent(Node n){
			// The complex base supplies the type when this is parsed again.
			auto t=a.at(n.b);
			if(n.value==Builtin.powerC){
				if(a.isNumber(t)&&a.number(t).im.zero) return render(rational(a.number(t).re),91);
				// A natural/integer exponent would select a different power.
				if(rigid[n.a]) return render(promoted(n.b,Sort.complex,Sort.real_),91);
			}
			return arg(n.b,91);
		}
		Piece sum(uint x,uint y){
			Piece l,r; pair(x,y,l,r);
			auto tail=render(r,r.negative||conversion(a.node(a.at(y)))?61:60,true);
			auto sign=r.negative?"-":tail.length&&tail[0]=='-'?"":"+";
			return Piece(render(l,60)~sign~tail,60);
		}
		Piece comparison(uint x,uint y,string relation){
			Piece l,r; pair(x,y,l,r);
			return Piece(render(l,51)~relation~render(r,51),50);
		}
		Piece product(Node n){
			// [p]·x denotes a non-strict mask, so a strict product needs an explicit call.
			if(memo[n.a].iverson)
				return Piece("mul"~suffix(n.sort)~"("~expected(n.a,n.sort)~","~expected(n.b,n.sort)~")");
			auto l=memo[n.a],r=memo[n.b];
			bool unit(uint id){ return (n.sort==Sort.real_||n.sort==Sort.complex)&&a.isNumber(a.at(id))&&(a.number(a.at(id)).one||(-a.number(a.at(id))).one); }
			if(unit(n.a)){ r.negative=l.negative!=r.negative; return r; }
			if(unit(n.b)){ l.negative=l.negative!=r.negative; return l; }
			pair(n.a,n.b,l,r);
			auto v=a.node(a.at(n.b));
			auto strict=v.op==Op.mul||v.op==Op.builtin&&(v.value==Builtin.mulN||v.value==Builtin.mulZ||v.value==Builtin.mulQ);
			return Piece(render(l,70,true)~"·"~render(r,strict?70:71,true),70,l.negative!=r.negative);
		}
		Piece zeroComparison(Term t,string relation){
			Term[] pending=[t],terms; string left,right; Number constant;
			Term variable; uint variables;
			void append(ref string side,string term){ side~=(side.length?"+":"")~term; }
			while(pending.length){
				auto u=pending[$-1]; --pending.length; auto n=a.node(u);
				if(n.op==Op.add) pending~=[a.at(n.b),a.at(n.a)];
				else if(a.isNumber(u)) constant=constant+a.number(u);
				else{
					terms~=u;
					if(symbolic[u.id]){ variable=u; ++variables; }
				}
			}
			if(variables==1){
				left=arg(variable.id,61);
				foreach(u;terms) if(u!=variable){
					auto p=memo[u.id]; p.negative=!p.negative;
					if(!right.length) right=render(p,60);
					else right~=(p.negative?"-":"+")~render(p,61,true);
				}
			}else foreach(u;terms){
				if(memo[u.id].negative) append(right,render(memo[u.id],61,true));
				else append(left,arg(u.id,61));
			}
			if(!left.length&&right.length){ left=right; right=""; constant=-constant; }
			if(!constant.zero){
				auto v=-constant;
				if(v.im.zero){
					auto p=rational(v.re);
					if(right.length) right~=(p.negative?"-":"+")~render(p,61,true);
					else right=render(p);
				}else{
					auto sign=v.im<Rational(0)?"":"+";
					append(right,"("~v.re.toString~sign~v.im.toString~"·ⅈ)");
				}
			}
			return Piece((left.length?left:"0")~relation~(right.length?right:"0"),50);
		}
		foreach(id;a.postorder(root)){
			auto t=a.at(id),n=a.node(t); Piece p;
			rigid[id]=true;
			symbolic[id]=n.op==Op.variable||n.op==Op.densityAt||
				n.arity>=1&&symbolic[n.a]||n.arity==2&&symbolic[n.b];
			final switch(n.op){
				case Op.realLit,Op.complexLit,Op.numberLit:
					auto z=a.number(t);
					if(n.sort==Sort.natural||n.sort==Sort.integer) p.text=(n.sort==Sort.natural?"nat(":"int(")~z.re.toString~")";
					else if(n.sort==Sort.rational) p.text="rat("~to!string(z.re.numerator)~","~to!string(z.re.denominator)~")";
					else if(n.sort==Sort.real_){ p=rational(z.re); rigid[id]=false; }
					else{
						auto negative=z.re<Rational(0)||z.re.zero&&z.im<Rational(0); if(negative) z=-z;
						auto im=z.im==Rational(1)?"ⅈ":z.im==Rational(-1)?"-ⅈ":z.im.toString~"·ⅈ";
						p=z.re.zero&&!z.im.zero?Piece(im,z.im==Rational(1)?100:70):Piece(z.re.toString~(z.im<Rational(0)?"":"+")~im,60);
						p.negative=negative;
					}
					break;
				case Op.variable:
					enforce(n.value<variables.length&&variables[cast(size_t)n.value].sort==n.sort,"unknown variable index");
					p.text=variables[cast(size_t)n.value].name; break;
				case Op.boolLit:p.text=n.value?"true":"false"; break;
				case Op.add:p=sum(n.a,n.b); rigid[id]=rigid[n.a]||rigid[n.b]; break;
				case Op.mul:p=product(n); rigid[id]=rigid[n.a]||rigid[n.b]; break;
				case Op.inv:p=Piece(arg(n.a,91)~"⁻¹",90); rigid[id]=rigid[n.a]; break;
				case Op.pow:p=Piece(arg(n.a,91)~"^"~to!string(n.value),90); rigid[id]=rigid[n.a]; break;
				case Op.abs:p.text="abs("~expected(n.a,Sort.real_)~")"; break;
				case Op.conj:p.text="conj("~expected(n.a,Sort.complex)~")"; break;
				case Op.not_:
					auto inner=a.node(a.at(n.a));
					p=inner.op==Op.nonzero?zeroComparison(a.at(inner.a),"="):Piece("¬"~arg(n.a,80),80); break;
				case Op.and_:p=Piece(arg(n.a,40)~"∧"~arg(n.b,41),40); break;
				case Op.or_:p=Piece(arg(n.a,30)~"∨"~arg(n.b,31),30); break;
				case Op.lt,Op.le:p=comparison(n.a,n.b,n.op==Op.lt?"<":"≤"); break;
				case Op.nonzero:p=zeroComparison(a.at(n.a),"≠"); break;
				case Op.mask:
					rigid[id]=rigid[n.b];
					if(a.isNumber(a.at(n.b))&&a.number(a.at(n.b)).one){
						p.text="["~arg(n.a)~"]";
						p.iverson=true;
						if(n.sort!=Sort.real_) p.text="("~p.text~":"~["ℕ","ℤ","ℚ","ℝ","ℂ"][rank(n.sort)]~")";
						rigid[id]=n.sort!=Sort.real_;
					}
					else p=Piece("["~arg(n.a)~"]·"~arg(n.b,71),70);
					break;
				case Op.builtin:
					auto f=cast(Builtin)n.value,info=builtinInfo(f),code=info.code;
					if(code=="pi") p.text="π";
					else if(code=="e") p.text="e";
					else if(code=="addN"||code=="addZ"||code=="addQ") p=sum(n.a,n.b);
					else if(code=="mulN"||code=="mulZ"||code=="mulQ") p=product(n);
					else if(f==Builtin.invQ) p=Piece(arg(n.a,91)~"⁻¹",90);
					else if(code=="nonzeroN"||code=="nonzeroZ"||code=="nonzeroQ") p=Piece(arg(n.a,51)~"≠0",50);
					else if(code=="ltN"||code=="ltZ"||code=="ltQ") p=comparison(n.a,n.b,"<");
					else if(code=="leN"||code=="leZ"||code=="leQ") p=comparison(n.a,n.b,"≤");
					else if(f==Builtin.eqB) p=Piece(arg(n.a,51)~"="~arg(n.b,51),50);
					else if(code=="powerR"||code=="powerC"||code.length==5&&code[0..3]=="pow"){
						auto base=arg(n.a,91);
						rigid[id]=rigid[n.a];
						if(f==Builtin.powRZ&&!rigid[id]){ base="("~arg(n.a)~":ℝ)"; rigid[id]=true; }
						p=Piece(base~"^"~exponent(n),90);
					}
					else p.text=info.name~"("~expected(n.a,info.args[0])~(n.arity==2?","~expected(n.b,info.args[1]):"")~")";
					if(code=="powerR"||code=="powerC") rigid[id]=rigid[n.a]||rigid[n.b];
					break;
				case Op.lebesgue:p.text="lebesgue()"; break;
				case Op.puncture:p.text="puncture("~arg(n.a)~")"; break;
				case Op.densityAt:p.text="densityAt("~arg(n.a)~","~arg(n.b)~")"; break;
				case Op.forget:p.text="forget("~arg(n.a)~")"; break;
			}
			enforce(p.text.length<=1_000_000,"formatted expression exceeds one million bytes");
			memo[id]=p;
		}
		return arg(root.id);
	}
}

unittest{
	import qsym.simplify;
	import std.exception:assertThrown;
	auto session=Session.open(); auto a=session.arena; Syntax syntax;
	assert(syntax.format(a,simplify(a,syntax.parse(a,"x+x")).output)=="2·x");
	assert(syntax.format(a,simplify(a,syntax.parse(a,"[x≠0]·x⁻¹")).output)=="[x≠0]·x⁻¹");
	syntax.declare("z:ℂ,p:𝔹");
	assert(syntax.format(a,simplify(a,syntax.parse(a,"(1+ⅈ)^2")).output)=="2·ⅈ");
	assert(syntax.format(a,simplify(a,syntax.parse(a,"conj(conj(z))")).output)=="z");
	assert(syntax.format(a,simplify(a,syntax.parse(a,"[p]·x+[¬p]·x")).output)=="x");
	foreach(source;["(x+1)·x⁻¹","¬(x<0)","[p]·(x+1)","(-x)^2","[x<1]·[x≥0]·x"]){
		auto x=syntax.parse(a,source);
		assert(simplify(a,syntax.parse(a,syntax.format(a,x))).output==simplify(a,x).output,source);
	}
	auto count=syntax.variables.length;
	assertThrown(syntax.parse(a,"newvar+true"));
	assert(syntax.variables.length==count);
	assertThrown(syntax.declare("z:ℝ,p:Density"));
	assert(a.sort(syntax.parse(a,"z"))==Sort.complex);
	assertThrown(syntax.parse(a,"unknown(x)"));
	assertThrown(syntax.parse(a,"x junk"));
	assert(a.sort(syntax.parse(a,"x^(4294967295+1)"))==Sort.real_);
	auto deep="x"; foreach(i;0..200) deep~="+x";
	assertThrown(syntax.parse(a,deep));
}

unittest{
	import qsym.simplify;
	auto session=Session.open(); auto a=session.arena; Syntax s; s.declare("z:ℂ,x:ℝ");
	foreach(pair;[["cpow(z,1/2)","z^(1/2)"],["cpow(z,-1/3)","z^(-1/3)"],["cpow(z,x)","z^x"],["clog(cpow(z,1/2))","1/2·clog(z)"],["toℂ(2)*z","2·z"],["z-1/2","z-1/2"]]){
		auto input=pair[0],expected=pair[1];
		auto t=simplify(a,s.parse(a,input)).output,printed=s.format(a,t);
		assert(printed==expected,printed);
		assert(simplify(a,s.parse(a,printed)).output==t,printed~" failed to round-trip");
	}
}

unittest{
	import qsym.simplify;
	auto session=Session.open(); auto a=session.arena; Syntax s;
	s.declare("z:ℂ,x:ℝ,y:ℝ,q:ℚ,k:ℤ,n:ℕ,p:𝔹");
	foreach(pair;[
		["ⅈ*toℂ(sqrt(3))","ⅈ·sqrt(3)"],
		["toℂ(sqrt(3))*ⅈ","sqrt(3)·ⅈ"],
		["z+toℂ(x)","z+x"],
		["z+toℂ(x+y)","z+(x+y)"],
		["toℂ(x+y)+z","x+y+z"],
		["toℂ(x+y)*z","(x+y)·z"],
		["z*toℂ(x^y)","z·x^y"],
		["z*toℂ(log(x))","z·log(x)"],
		["z*toℂ(sqrt(-1))","z·sqrt(-1)"],
		["ⅈ*toℂ([p]*x)","ⅈ·([p]·x)"],
		["toℂ([p]*x)*z","[p]·x·z"],
		["mulC(([p]:ℂ),toℂ(x))","mulC(([p]:ℂ),x)"],
		["cexp(toℂ(x))","cexp(x)"],
		["csqrt(toℂ(sqrt(x)))","csqrt(sqrt(x))"],
		["conj(toℂ(x))","conj(x)"],
		["carg(toℂ(x))","carg(x)"],
		["cpow(z,toℂ(toℝ(toℚ(toℤ(n)))))","z^toℝ(n)"],
		["z*toℂ(powRN(3,n))","z·toℂ(3^n)"],
		["z*toℂ(powRZ(3,k))","z·(3:ℝ)^k"],
		["cexp(toℂ(toℝ(toℚ(toℤ(n)))))","cexp(n)"],
		["x+toℝ(q)","x+q"],
		["q*toℚ(k)","q·k"],
		["k+toℤ(n)","k+n"],
		["toℝ(q)<x","q<x"],
		["q≤toℚ(k)","q≤k"],
		["toℤ(n)<k","n<k"],
		["toℂ(x)","toℂ(x)"],
		["toℂ(sqrt(3))","toℂ(sqrt(3))"],
		["toℂ(x)+toℂ(y)","toℂ(x)+y"],
		["z*toℂ((-1)^(2⁻¹))","z·toℂ((-1)^(2⁻¹))"],
		["ⅈ*toℂ([p])","ⅈ·toℂ([p])"]
	]){
		auto input=s.parse(a,pair[0]),printed=s.format(a,input),output=s.parse(a,printed);
		assert(printed==pair[1],pair[0]~" printed as "~printed);
		assert(a.sort(input)==a.sort(output),printed~" changes type");
		assert(input==output,printed~" changes typed operations or their domains");
		assert(simplify(a,input).output==simplify(a,output).output,printed~" changes meaning");
		assert(s.format(a,output)==printed,printed~" is not stable");
	}
	assert(s.format(a,simplify(a,s.parse(a,"ⅈ*3^(1/2)")).output)=="ⅈ·sqrt(3)");
	// Fixed builtin signatures should recover every omitted embedding, even
	// through several numeric types. Powers must retain their exponent kind.
	foreach(i;0..cast(uint)Builtin.invalid){
		auto f=cast(Builtin)i; if(f==Builtin.eqB||f==Builtin.nonzeroN) continue;
		Term[] args;
		foreach(sort;builtinInfo(f).args) args~=sort==Sort.boolean?s.parse(a,"p"):a.castTo(s.parse(a,"n"),sort);
		auto input=a.call(f,args),printed=s.format(a,input),output=s.parse(a,printed);
		assert(input==output,builtinInfo(f).code~" changed operations: "~printed);
	}
}
