module rulec;
import qsym.ir;
import qsym.spec;
import qsym.lexer:symbolCode;
import std.file:readText,write;
import std.conv:to;
import std.array:join;
import std.string:replace;
import std.stdio:stderr,writeln;
import std.exception:enforce;
@safe:

string dOp(string n){
	if(builtin(n)!=Builtin.invalid) return "builtin";
	switch(n){
		case "nat","int","rat":return "numberLit";
		case "real":return "realLit";
		case "complex":return "complexLit";
		case "true","false":return "boolLit";
		case "addR","addC":return "add";
		case "mulR","mulC":return "mul";
		case "invR","invC":return "inv";
		case "nonzeroR","nonzeroC":return "nonzero";
		case "powN","powZ","powQ","powR","powC":return "pow";
		case "absR":return "abs";
		case "ltR":return "lt";
		case "leR":return "le";
		case "not","and","or":return n~"_";
		case "maskN","maskZ","maskQ","maskR","maskC":return "mask";
		default:return n;
	}
}
string dInteger(long n){ return n==long.min?"long.min":to!string(n)~"L"; }
string rootOp(Pattern p){
	if(p.name=="real"&&p.args.length==2)
		return Rational(BigInt(p.args[0].number),BigInt(p.args[1].number)).small?"realLit":"numberLit";
	return dOp(p.name);
}
bool containsVariable(Pattern p,string name){
	if(p.variable) return p.name==name;
	foreach(arg;p.args) if(containsVariable(arg,name)) return true;
	return false;
}
bool functionPattern(Pattern p){
	if(p.variable||p.natural) return false;
	auto op=rootOp(p);
	if(op=="builtin"||op=="inv"||op=="abs") return true;
	foreach(arg;p.args) if(functionPattern(arg)) return true;
	return false;
}
bool earlyRule(Rule r){
	if(!r.automatic) return false;
	// Normalize exact embeddings before expanding the general integrality test.
	if(r.lhs.name=="isIntR"&&r.lhs.args[0].variable) return false;
	auto op=rootOp(r.lhs);
	auto comparison=op=="nonzero"||op=="lt"||op=="le"||
		op=="builtin"&&r.lhs.sort==Sort.boolean;
	if(comparison&&!r.premises.length) return true;
	// Keep constant reductions ahead of identities with overlapping empty domains.
	if(!r.premises.length) foreach(arg;r.lhs.args){
		auto head=rootOp(arg);
		if(head=="realLit"||head=="complexLit"||head=="numberLit"||head=="boolLit"||arg.natural&&arg.name=="#") return true;
		if(head=="pow"||head=="conj") return true;
	}
	// Join guard partitions before simplifying away their complementary shapes.
	if((op=="add"||r.lhs.name=="addN"||r.lhs.name=="addZ"||r.lhs.name=="addQ")&&r.lhs.args.length==2&&rootOp(r.lhs.args[0])=="mask"&&rootOp(r.lhs.args[1])=="mask") return true;
	// Preserve function shapes before normalizing their operands. Algebraic
	// conditions wait until counted sums and products have been collected.
	foreach(arg;r.lhs.args) if(functionPattern(arg)) return true;
	return false;
}
bool pairRule(Rule r){
	auto op=rootOp(r.lhs);
	if(!r.automatic||(op!="add"&&op!="mul")) return false;
	auto x=r.lhs.args[0],y=r.lhs.args[1];
	return !x.variable&&!y.variable||x.variable&&!y.variable&&containsVariable(y,x.name)||
		y.variable&&!x.variable&&containsVariable(x,y.name);
}
string rootTest(Pattern p,string node){
	if(p.variable) return "true";
	auto test=node~".op==Op."~rootOp(p);
	if(builtin(p.name)!=Builtin.invalid) test~="&&"~node~".value==Builtin."~p.name;
	if(p.name=="true"||p.name=="false") test~="&&"~node~".value=="~(p.name=="true"?"1":"0");
	if(p.name=="real"&&p.args.length==1&&!p.args[0].variable) test~="&&"~node~".value=="~dInteger(p.args[0].number);
	if(p.name=="complex") foreach(i,arg;p.args) if(!arg.variable) test~="&&"~node~(i?".imaginary==":".value==")~dInteger(arg.number);
	return test;
}
string headCode(Pattern p){
	if(p.variable) return "uint.max";
	return "(cast(uint)Op."~rootOp(p)~"|(cast(uint)Sort."~to!string(p.sort)~"<<8)"~
		(builtin(p.name)!=Builtin.invalid?"|(cast(uint)Builtin."~p.name~"<<16)":"")~")";
}
string variablePath(Pattern p,string variable,string path){
	if(p.variable) return !p.natural&&p.name==variable?path:"";
	if(p.natural||p.name=="#"||rootOp(p)=="add"||rootOp(p)=="mul") return "";
	if(p.name=="real"||p.name=="complex"||p.name=="nat"||p.name=="int"||p.name=="rat") return "";
	foreach(i,arg;p.args){
		auto result=variablePath(arg,variable,"a.viewChild("~path~","~to!string(i)~")");
		if(result.length) return result;
	}
	return "";
}
string shapeTest(Pattern p,string path,uint depth=2){
	if(p.variable||p.natural||p.name=="#") return "true";
	if(rootOp(p)=="add"||rootOp(p)=="mul") return "a.sort("~path~")==Sort."~to!string(p.sort);
	auto test=rootTest(p,"a.view("~path~")");
	if(depth&&rootOp(p)!="add"&&rootOp(p)!="mul") foreach(i,arg;p.args) if(!arg.variable&&!arg.natural&&arg.name!="#")
		test~="&&"~shapeTest(arg,"a.viewChild("~path~","~to!string(i)~")",depth-1);
	return test;
}
string dPattern(Pattern p){
	if(p.variable) return parameterCode(p.name);
	if(p.name=="real"&&p.args.length==2) return "a.real_(Rational(BigInt("~dInteger(p.args[0].number)~"),BigInt("~dInteger(p.args[1].number)~")))";
	if(p.name=="natAdd"||p.name=="natMul") return "nat(cast(ulong)("~dPattern(p.args[0])~")"~(p.name=="natAdd"?"+":"*")~dPattern(p.args[1])~")";
	if(p.natural&&p.name=="#") return to!string(p.number)~"u";
	if(p.name=="powN"||p.name=="powZ"||p.name=="powQ"||p.name=="powR"||p.name=="powC") return "a.pow("~dPattern(p.args[0])~","~dPattern(p.args[1])~")";
	if(p.name=="#") return "("~dInteger(p.number)~")";
	if(p.name=="true"||p.name=="false") return "a.boolean("~p.name~")";
	string[] args;
	foreach(arg;p.args) args~=dPattern(arg);
	if(builtin(p.name)!=Builtin.invalid) return "a.call(Builtin."~p.name~",["~args.join(",")~"])";
	auto name=p.name=="real"||p.name=="complex"?p.name:p.name=="nat"?"natural_":p.name=="int"?"integer":p.name=="rat"?"rational":dOp(p.name);
	if(name=="real") name="real_";
	return "a."~name~"("~args.join(",")~(name=="add"||name=="mul"?",raw":"")~")";
}
string emitD(Rule[] rules){
	string d="// Generated by rulec; edit rules/core.qs.\nmodule qsym.generated.rules;\nimport qsym.ir;\nimport qsym.matching;\nimport qsym.budget:Limit;\nimport std.exception:enforce;\n@safe:\n"~
		"struct Rewrite{ bool applied; Term result; string rule; Term[] bindings; }\n"~
		"struct Condition{ Term term; bool defined,literal; }\n"~
		"struct Instance{ Term before,result; string rule; Term[] bindings; Condition[] conditions; bool[] naturals; bool equality,reversed; Law law; bool raw; }\n"~
		"private uint nat(ulong n){ if(n>uint.max) throw new Limit; return cast(uint)n; }\n"~
		"uint head(Node n){ return cast(uint)n.op|(cast(uint)n.sort<<8)|(n.op==Op.builtin?cast(uint)n.value<<16:0); }\n"~
		"enum Law{\n";
	foreach(r;rules) d~="\t"~symbolCode(r.name)~",\n";
	d~="}\nInstance instantiate(Arena a,Law law,Term[] bindings,bool raw=false){\n\tswitch(law){\n";
	foreach(r;rules){
		d~="\t\tcase Law."~symbolCode(r.name)~":{\n\t\t\tenforce(bindings.length=="~to!string(r.parameters.length)~",\"rule arity mismatch\");\n";
		string[] naturals;
		foreach(i,v;r.parameters){
			auto at="bindings["~to!string(i)~"]";
			d~="\t\t\tenforce(a.sort("~at~")==Sort."~to!string(v.sort)~",\"rule binding type mismatch\");\n";
			if(v.natural){
				d~="\t\t\tenforce(a.isNumber("~at~")&&a.number("~at~").re.small&&a.number("~at~").re.integer>=0&&a.number("~at~").re.integer<=uint.max,\"natural binding expected\");\n";
				d~="\t\t\tauto "~parameterCode(v.name)~"=cast(uint)a.number("~at~").re.integer;\n";
			}else d~="\t\t\tauto "~parameterCode(v.name)~"="~at~";\n";
			naturals~=v.natural?"true":"false";
		}
		string[] conditions;
		foreach(p;r.premises) conditions~="Condition("~dPattern(p.term)~","~(p.defined?"true":"false")~","~(p.literal?"true":"false")~")";
		d~="\t\t\treturn Instance("~dPattern(r.lhs)~","~dPattern(r.rhs)~",\""~ruleCode(r.name)~"\",bindings,["~conditions.join(",")~"],["~naturals.join(",")~"],"~(r.equality?"true":"false")~",false,law,raw);\n\t\t}\n";
	}
	d~="\t\tdefault:assert(0);\n\t}\n}\n"~
		"Rewrite rewrite(Arena a,Term root,bool trace){\n"~
		"\tforeach(law;rewrites(a.view(root))){\n"~
		"\t\tif(conditionCount(law)) continue;\n"~
		"\t\tTerm[] bindings;\n"~
		"\t\tif(!match(a,law,-1,root,bindings)) continue;\n"~
		"\t\tauto i=instantiate(a,law,bindings);\n"~
		"\t\tif(i.result==root) continue;\n"~
		"\t\treturn Rewrite(true,i.result,i.rule,trace?bindings:null);\n"~
		"\t}\n\treturn Rewrite(false,root);\n}\n";
	d~="bool match(Arena a,Law law,int part,Term input,ref Term[] bindings){\n\tauto work=new MatchWork;\n\tswitch(law){\n";
	foreach(r;rules){
		literalParameters=null;
		foreach(p;r.premises) if(p.literal&&p.term.variable) literalParameters~=p.term.name;
		d~="\t\tcase Law."~symbolCode(r.name)~":\n\t\t\tif(!bindings.length) bindings.length="~to!string(r.parameters.length)~";\n\t\t\tenforce(bindings.length=="~to!string(r.parameters.length)~",\"binding count mismatch\");\n\t\t\tswitch(part){\n";
		d~="\t\t\t\tcase -1:\n"~matchCode(r.lhs,"input",r.parameters,"\t\t\t\t\t",r.automatic)~"\t\t\t\t\treturn true;\n";
		foreach(i,p;r.premises) d~="\t\t\t\tcase "~to!string(i)~":\n"~matchCode(p.term,"input",r.parameters,"\t\t\t\t\t")~"\t\t\t\t\treturn true;\n";
		d~="\t\t\t\tdefault:return false;\n\t\t\t}\n";
	}
	d~="\t\tdefault:return false;\n\t}\n}\n";
	d~="bool candidate(Arena a,Law law,Term input){\n\tswitch(law){\n";
	foreach(r;rules) if(r.automatic||r.inference)
		d~="\t\tcase Law."~symbolCode(r.name)~":return "~shapeTest(r.lhs,"input")~";\n";
	d~="\t\tdefault:return false;\n\t}\n}\n";
	foreach(kind;0..3){
		bool selected(Rule r){ return kind==2?earlyRule(r):kind==1?r.inference:r.automatic; }
		auto name=kind==2?"earlyRewrites":kind==1?"inferences":"rewrites";
		string[] heads;
		foreach(r;rules) if(selected(r)){
			auto head=headCode(r.lhs); bool found;
			foreach(old;heads) if(old==head) found=true;
			if(!found) heads~=head;
		}
		d~="const(Law)[] "~name~"(Node n){\n\tswitch(head(n)){\n";
		foreach(head;heads){
			string[] ids;
			foreach(r;rules) if(selected(r)&&headCode(r.lhs)==head) ids~="Law."~symbolCode(r.name);
			d~="\t\tcase "~head~":{ static immutable Law[] laws=["~ids.join(",")~"]; return laws; }\n";
		}
		d~="\t\tdefault:return null;\n\t}\n}\n";
		if(kind==2) continue;
		d~="const(Law)[] "~name~"(Op op){\n\tswitch(op){\n";
		foreach(op;opsFor(rules,kind==1)){
			string[] ids;
			foreach(r;rules) if(selected(r)&&rootOp(r.lhs)==op) ids~="Law."~symbolCode(r.name);
			d~="\t\tcase Op."~op~":{ static immutable Law[] laws=["~ids.join(",")~"]; return laws; }\n";
		}
		d~="\t\tdefault:return null;\n\t}\n}\n";
	}
	d~="struct PairRule{ Law law; uint left,right; }\n";
	d~="const(PairRule)[] pairRewrites(Op op){\n\tswitch(op){\n";
	foreach(op;["add","mul"]){
		string[] ids;
		foreach(r;rules) if(pairRule(r)&&rootOp(r.lhs)==op)
			ids~="PairRule(Law."~symbolCode(r.name)~","~headCode(r.lhs.args[0])~","~headCode(r.lhs.args[1])~")";
		d~="\t\tcase Op."~op~":{ static immutable PairRule[] laws=["~ids.join(",")~"]; return laws; }\n";
	}
	d~="\t\tdefault:return null;\n\t}\n}\n";
	d~="bool pairCandidate(Law law,Node x,Node y){\n\tswitch(law){\n";
	foreach(r;rules) if(pairRule(r))
		d~="\t\tcase Law."~symbolCode(r.name)~":return "~rootTest(r.lhs.args[0],"x")~"&&"~rootTest(r.lhs.args[1],"y")~";\n";
	d~="\t\tdefault:return false;\n\t}\n}\n";
	d~="bool pairKey(Arena a,Law law,bool right,Term input,out uint key){\n\tswitch(law){\n";
	foreach(r;rules) if(pairRule(r)){
		string left,right;
		foreach(v;r.parameters) if(!v.natural){
			left=variablePath(r.lhs.args[0],v.name,"input"); right=variablePath(r.lhs.args[1],v.name,"input");
			if(left.length&&right.length) break;
		}
		d~="\t\tcase Law."~symbolCode(r.name)~":\n";
		foreach(side;[true,false]){
			d~="\t\t\t"~(side?"if(right)":"else")~"{\n";
			d~="\t\t\t\tif(!("~shapeTest(r.lhs.args[side?1:0],"input",128)~")) return false;\n";
			d~="\t\t\t\tkey="~(left.length&&right.length?(side?right:left)~".id":"0")~"; return true;\n\t\t\t}\n";
		}
	}
	d~="\t\tdefault:return false;\n\t}\n}\n";
	d~="size_t conditionCount(Law law){\n\tswitch(law){\n";
	foreach(r;rules) d~="\t\tcase Law."~symbolCode(r.name)~":return "~to!string(r.premises.length)~";\n";
	return d~"\t\tdefault:assert(0);\n\t}\n}\n";
}

string[] opsFor(Rule[] rules,bool inference){
	string[] result;
	foreach(r;rules) if(inference?r.inference:r.automatic){
		auto op=rootOp(r.lhs); bool found;
		foreach(old;result) if(old==op) found=true;
		if(!found) result~=op;
	}
	return result;
}

string matchPayload(Pattern p,string value,Parameter[] parameters,string indent,bool big=false){
	if(!p.variable) return indent~"if("~value~"!="~dInteger(p.number)~") return false;\n";
	return indent~"if("~value~"<0||"~value~">uint.max) return false;\n"~
		matchCode(p,"cast(uint)("~value~")"~(big?".toLong()":""),parameters,indent);
}
private uint nextMatcher;
private string[] literalParameters;
bool naturalLinear(Pattern p,out Pattern variable,out ulong coefficient,out ulong offset){
	if(p.variable){ variable=p; coefficient=1; return true; }
	if(p.name=="#"){ offset=p.number; return offset<=uint.max; }
	if(p.args.length!=2||(p.name!="natAdd"&&p.name!="natMul")) return false;
	Pattern x,y; ulong a,b,c,d;
	if(!naturalLinear(p.args[0],x,a,b)||!naturalLinear(p.args[1],y,c,d)) return false;
	if(x&&y&&x.name!=y.name) return false;
	variable=x?x:y;
	if(p.name=="natAdd"){ coefficient=a+c; offset=b+d; }
	else{
		if(a&&c) return false;
		coefficient=a*d+c*b; offset=b*d;
	}
	return coefficient<=uint.max&&offset<=uint.max;
}
string matchCode(Pattern p,string path,Parameter[] parameters,string indent,bool top=false){
	if(p.name=="real"&&p.args.length==2) return indent~"if("~path~"!="~dPattern(p)~") return false;\n";
	if(p.variable){
		size_t i; while(parameters[i].name!=p.name) ++i;
		auto slot="bindings["~to!string(i)~"]";
		auto value=p.natural?"a.real_("~path~")":path;
		return (p.natural?"":indent~"if(a.sort("~path~")!=Sort."~to!string(p.sort)~") return false;\n")~
			indent~"if("~slot~".id==uint.max) "~slot~"="~value~"; else if("~slot~"!="~value~") return false;\n";
	}
	if(p.natural){
		if(p.name=="#") return indent~"if("~path~"!="~to!string(p.number)~"u) return false;\n";
		Pattern variable; ulong coefficient,offset;
		if(naturalLinear(p,variable,coefficient,offset)&&coefficient){
			auto a=coefficient.to!string~"u",b=offset.to!string~"u",delta="("~path~"-"~b~")";
			return indent~"if("~path~"<"~b~"||"~delta~"%"~a~") return false;\n"~
				matchCode(variable,delta~"/"~a,parameters,indent);
		}
		return indent~"return false;\n";
	}
	if(dOp(p.name)=="add"||dOp(p.name)=="mul"){
		Pattern[] atoms;
		void flatten(Pattern q){ if(!q.variable&&q.name==p.name){ flatten(q.args[0]); flatten(q.args[1]); }else atoms~=q; }
		flatten(p); string[] entries; bool bounded;
		if(top) foreach(q;atoms) if(!q.variable&&q.name!="real"&&q.name!="complex"&&q.name!="nat"&&q.name!="int"&&q.name!="rat") bounded=true;
		foreach(q;atoms){
			if(q.variable){
				size_t i; while(parameters[i].name!=q.name) ++i;
				bool literal; foreach(name;literalParameters) literal|=name==q.name;
				entries~="MatchOperand(null,"~to!string(i)~",uint.max,"~(literal?"true":"false")~","~(bounded?"true":"false")~")";
			}else{
				auto id=to!string(nextMatcher++),term="t"~id,slots="bs"~id;
				auto body=matchCode(q,term,parameters,indent~"\t").replace("bindings",slots);
				auto head=rootOp(q)=="add"||rootOp(q)=="mul"?"uint.max":headCode(q);
				entries~="MatchOperand((Term "~term~",ref Term[] "~slots~"){\n"~body~indent~"\treturn true;\n"~indent~"},-1,"~head~")";
			}
		}
		return indent~"if(a.sort("~path~")!=Sort."~to!string(p.sort)~") return false;\n"~
			indent~"if(!matchRegion(a,"~path~",Op."~dOp(p.name)~",["~entries.join(",")~"],bindings,work)) return false;\n";
	}
	string s=indent~"if(a.view("~path~").op!=Op."~dOp(p.name)~"||a.sort("~path~")!=Sort."~to!string(p.sort)~") return false;\n";
	if(p.name=="real"||p.name=="complex"){
		s~=matchPayload(p.args[0],"a.view("~path~").value",parameters,indent);
		if(p.name=="complex") s~=matchPayload(p.args[1],"a.view("~path~").imaginary",parameters,indent);
	}else if(p.name=="nat"||p.name=="int"||p.name=="rat"){
		bool variables; foreach(arg;p.args) variables|=arg.variable;
		if(!variables) s~=indent~"if("~path~"!="~dPattern(p)~") return false;\n";
		else{
			s~=matchPayload(p.args[0],"a.number("~path~").re.numerator",parameters,indent,true);
			if(p.name=="rat") s~=matchPayload(p.args[1],"a.number("~path~").re.denominator",parameters,indent,true);
		}
	}else if(p.name=="true"||p.name=="false") s~=indent~"if(a.view("~path~").value!="~(p.name=="true"?"1":"0")~") return false;\n";
	else if(p.name=="powN"||p.name=="powZ"||p.name=="powQ"||p.name=="powR"||p.name=="powC")
		s~=matchCode(p.args[0],"a.viewChild("~path~",0)",parameters,indent)~matchCode(p.args[1],"cast(uint)a.view("~path~").value",parameters,indent);
	else{
		if(builtin(p.name)!=Builtin.invalid) s~=indent~"if(a.view("~path~").value!=cast(long)Builtin."~p.name~") return false;\n";
		foreach(i,arg;p.args) s~=matchCode(arg,"a.viewChild("~path~","~to!string(i)~")",parameters,indent);
	}
	return s;
}

string leanValue(Pattern p){
	if(p.variable||p.natural) return leanPattern(p);
	if(p.name=="real"&&p.args.length==2) return "(some ((("~leanPattern(p.args[0])~" : ℚ) / "~leanPattern(p.args[1])~" : ℚ) : ℝ))";
	if(p.name=="nat") return "(some ("~leanPattern(p.args[0])~" : ℕ))";
	if(p.name=="int") return "(some ("~leanPattern(p.args[0])~" : ℤ))";
	if(p.name=="rat") return "(some (("~leanPattern(p.args[0])~" : ℚ) / "~leanPattern(p.args[1])~"))";
	if(p.name=="real") return "(some (("~leanPattern(p.args[0])~" : Int) : ℝ))";
	if(p.name=="complex") return "(some ((("~leanPattern(p.args[0])~" : Int) : ℂ) + (("~leanPattern(p.args[1])~" : Int) : ℂ) * Complex.I))";
	if(p.name=="true"||p.name=="false") return "(some "~p.name~")";
	if(p.name=="lebesgue") return "(some Density.lebesgue)";
	if(p.name=="powN"||p.name=="powZ"||p.name=="powQ"||p.name=="powR"||p.name=="powC") return "("~leanValue(p.args[0])~".map (fun x => x ^ "~leanPattern(p.args[1])~"))";
	if(p.name=="puncture"||p.name=="forget") return "("~leanValue(p.args[0])~".map Density."~p.name~")";
	if(builtin(p.name)!=Builtin.invalid){
		if(!p.args.length) return "(some Functions."~p.name~")";
		string s="(Functions."~p.name~".apply"; foreach(arg;p.args) s~=" "~leanValue(arg); return s~")";
	}
	auto op=dOp(p.name);
	if(op=="not_"||op=="and_"||op=="or_") op=op[0..$-1];
	string s="(Value."~op;
	foreach(arg;p.args) s~=" "~leanValue(arg);
	return s~")";
}

string emitLean(Rule[] rules){
	string lean="-- Generated by rulec; every declaration must pass the Lean kernel.\n"~
		"import QSym.Refinement\nimport QSym.AxiomCheck\nimport QSym.ProofCache\nnamespace QSym.Generated\n";
	foreach(r;rules){
		lean~="theorem "~ruleCode(r.name);
		foreach(v;r.parameters) lean~=" ("~parameterCode(v.name)~" : "~(v.natural?"Nat":"Option (Ty.denote ."~leanSort(v.sort)~")")~")";
		foreach(i,p;r.premises) if(!p.literal){
			auto e=leanValue(p.term);
			lean~="\n    (hp"~to!string(i)~" : "~(p.defined?"Value.Defined "~e:"Value.Refines "~e~" (some true)")~")";
		}
		lean~=" :\n    "~(r.equality?leanValue(r.lhs)~" = "~leanValue(r.rhs):"Value.Refines "~leanValue(r.lhs)~" "~leanValue(r.rhs))~" := qsym_cached% by\n";
		// Apply these shared lemmas before splitting partial arguments. Splitting
		// first makes elaboration repeatedly unfold the large affine predicate.
		if(r.name=="natural_literal_affine_nonzero"||r.name=="integer_literal_affine_nonzero"){
			lean~="  exact Value.refines_"~r.name~" v_a v_x v_b hp2\n\n#qsym_check_axioms "~ruleCode(r.name)~"\n\n";
			continue;
		}
		string[] cases;
		foreach(v;r.parameters) if(!v.natural) cases~="cases "~parameterCode(v.name);
		if(cases.length) lean~="  "~cases.join(" <;> ")~"\n";
		if(r.equality) lean~="  all_goals apply Value.Refines.antisymm\n";
		lean~="  all_goals qsym_rule\n\n";
		lean~="#qsym_check_axioms "~ruleCode(r.name)~"\n\n";
	}
	return lean~"end QSym.Generated\n";
}

@system int main(string[] args){
	try{
		enforce(args.length==4,"usage: rulec INPUT.qs OUTPUT.d OUTPUT.lean");
		auto rules=Parser(readText(args[1])).parse();
		auto d=emitD(rules),lean=emitLean(rules);
		write(args[2],d); write(args[3],lean);
		writeln("Generated ",rules.length," rules; Lean checking is required before trusting them.");
		return 0;
	}catch(Exception e){ stderr.writeln(e.msg); return 1; }
}
