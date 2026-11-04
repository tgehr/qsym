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
			enforce(!v.natural&&(v.sort==Sort.real_||v.sort==Sort.complex||v.sort==Sort.boolean),"expected Real, Complex or Bool");
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
			if(p.name=="real") return a.real_(p.args[0].number);
			if(p.name=="complex") return a.complex(p.args[0].number,p.args[1].number);
			if(p.name=="true"||p.name=="false") return a.boolean(p.name=="true");
			if(p.name=="lebesgue") return a.lebesgue();
			auto x=build(p.args[0]);
			if(p.name=="powR"||p.name=="powC"){
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
				case "maskR","maskC":return a.mask(x,y);
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
		struct Piece{ string text; uint precedence=100; }
		Piece[] memo=new Piece[a.length];
		string arg(uint id,uint precedence=0){
			auto p=memo[id]; return p.precedence<precedence?"("~p.text~")":p.text;
		}
		Piece rational(Rational q){ return Piece(q.toString,q.integral?(q<Rational(0)?80:100):70); }
		foreach(id;a.postorder(root)){
			auto t=a.at(id),n=a.node(t); Piece p;
			final switch(n.op){
				case Op.realLit,Op.complexLit,Op.numberLit:
					auto z=a.number(t);
					if(n.sort==Sort.real_) p=rational(z.re);
					else if(z.re.zero&&z.im==Rational(1)) p.text="ⅈ";
					else if(z.re.zero&&z.im==Rational(-1)) p=Piece("-ⅈ",80);
					else{
						auto im=z.im==Rational(1)?"ⅈ":z.im==Rational(-1)?"-ⅈ":z.im.toString~"·ⅈ";
						p=z.re.zero&&!z.im.zero?Piece(im,70):Piece(z.re.toString~(z.im<Rational(0)?"":"+")~im,60);
					}
					break;
				case Op.variable:
					enforce(n.value<variables.length&&variables[cast(size_t)n.value].sort==n.sort,"unknown variable index");
					p.text=variables[cast(size_t)n.value].name; break;
				case Op.boolLit:p.text=n.value?"true":"false"; break;
				case Op.add:p=Piece(arg(n.a,60)~"+"~arg(n.b,61),60); break;
				case Op.mul:p=Piece(arg(n.a,70)~"·"~arg(n.b,71),70); break;
				case Op.inv:p=Piece(arg(n.a,91)~"⁻¹",90); break;
				case Op.pow:p=Piece(arg(n.a,91)~"^"~to!string(n.value),90); break;
				case Op.abs:p.text="abs("~arg(n.a)~")"; break;
				case Op.conj:p.text="conj("~arg(n.a)~")"; break;
				case Op.not_:p=Piece("¬"~arg(n.a,80),80); break;
				case Op.and_:p=Piece(arg(n.a,40)~"∧"~arg(n.b,41),40); break;
				case Op.or_:p=Piece(arg(n.a,30)~"∨"~arg(n.b,31),30); break;
				case Op.lt,Op.le:p=Piece(arg(n.a,51)~(n.op==Op.lt?"<":"≤")~arg(n.b,51),50); break;
				case Op.nonzero:p=Piece(arg(n.a,51)~"≠0",50); break;
				case Op.mask:p=Piece("["~arg(n.a)~"]·"~arg(n.b,71),70); break;
				case Op.lebesgue:p.text="lebesgue()"; break;
				case Op.puncture:p.text="puncture("~arg(n.a)~")"; break;
				case Op.densityAt:p.text="densityAt("~arg(n.a)~","~arg(n.b)~")"; break;
				case Op.forget:p.text="forget("~arg(n.a)~")"; break;
			}
			enforce(p.text.length<=1_000_000,"formatted expression exceeds one million bytes");
			memo[id]=p;
		}
		return memo[root.id].text;
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
	assertThrown(syntax.parse(a,"x^(4294967295+1)"));
	auto deep="x"; foreach(i;0..200) deep~="+x";
	assertThrown(syntax.parse(a,deep));
}
