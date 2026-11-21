module qsym.distribution_syntax;
import qsym.spec:Pattern,TypePattern,pattern;
import std.exception:enforce;
@safe:

// Recognize a joint Lebesgue/Dirac graph over two distinct real axes.
private bool graphForm(Pattern p,out Pattern input,out Pattern mapping,out Pattern target){
	if(p.name!="$disintegrate"||p.args[0].name!="$mul") return false;
	auto denominator=p.args[1];
	bool measure(Pattern q){ return q.name=="$distributionApply"&&q.args[0].name=="λ"&&!q.args[0].called; }
	if(!measure(denominator)) return false;
	target=denominator.args[1];
	auto factors=p.args[0].args;
	foreach(i;0..2){
		auto base=factors[i],point=factors[1-i];
		if(!measure(base)||base.args[1].name==target.name||point.name!="$distributionApply"||
			point.args[1].name!=target.name) continue;
		auto atom=point.args[0];
		if((atom.name=="δ"||atom.name=="dirac")&&atom.args.length==1){
			input=base.args[1]; mapping=atom.args[0]; return true;
		}
	}
	return false;
}

// Distribution application is a scoped form, not a scalar density or function
// application. Lower its single output axis before ordinary elaboration.
string distributionOutputAxis(Pattern root){
	string axis;
	void visit(Pattern p,bool inForm) @safe {
		if(p.binder.length) return;
		if(p.name=="$disintegrate"){
			Pattern input,mapping,target;
			if(inForm&&graphForm(p,input,mapping,target)){
				if(!axis.length) axis=input.name;
				enforce(axis==input.name,"multiple free output axes require explicit distribution binders");
			}
			return;
		}
		if(p.name=="$distributionApply"){
			if(!axis.length) axis=p.args[1].name;
			enforce(axis==p.args[1].name,"multiple free output axes require explicit distribution binders"); return;
		}
		if(p.name=="$if"){ visit(p.args[1],inForm); visit(p.args[2],inForm); return; }
		foreach(a;p.args) visit(a,inForm&&(p.name=="$mul"||p.name=="$add"||p.name=="$neg"));
	}
	visit(root,true); return axis;
}

bool distributionOccurs(Pattern p,string name) @safe {
	bool inType(TypePattern t) @safe {
		if(t is null) return false;
		if(t.dimension !is null&&distributionOccurs(t.dimension,name)) return true;
		if(t.binder!=name&&t.predicate !is null&&distributionOccurs(t.predicate,name)) return true;
		foreach(i,a;t.args){
			if(t.name=="pi"&&i==1&&t.binder==name) continue;
			if(inType(a)) return true;
		}
		return false;
	}
	// A binder scopes over its body, not its own parameter annotation.
	if(inType(p.annotation)) return true;
	if(p.binder==name) return false;
	if(!p.called&&!p.args.length&&p.name==name) return true;
	foreach(a;p.args) if(distributionOccurs(a,name)) return true;
	return false;
}

Pattern distributionSyntax(Pattern root){
	bool form(Pattern p,string axis) @safe {
		if(p.binder==axis) return false;
		if(p.name=="$distributionApply"&&p.args[1].name==axis) return true;
		foreach(a;p.args) if(form(a,axis)) return true;
		return false;
	}
	Pattern lambda(string name,TypePattern ty,Pattern body) @safe {
		auto p=pattern("$lambda",[body]); p.binder=name; p.annotation=ty; return p;
	}
	Pattern typed(Pattern p,TypePattern ty) @safe { auto q=pattern("$ascribe",[p]); q.annotation=ty; return q; }
	Pattern delegate(Pattern) @safe expand;
	Pattern lower(Pattern p,string axis,TypePattern ty) @safe {
		auto dt=new TypePattern("Distribution",[ty]);
		if(p.name=="$if"){
			enforce(!distributionOccurs(p.args[0],axis),"a distribution branch condition must be independent of its output axis");
			return pattern("$if",[expand(p.args[0]),lower(p.args[1],axis,ty),lower(p.args[2],axis,ty)]);
		}
		if(p.name=="$bottom") return typed(p,dt);
		if(p.name=="$disintegrate"){
			Pattern input,mapping,target;
			enforce(graphForm(p,input,mapping,target)&&input.name==axis,"graph disintegration requires its retained axis");
			return typed(expand(p),dt);
		}
		if(p.name=="#"&&p.number==0){ auto t=pattern("$type",[]); t.annotation=ty; return pattern("zeroD",[t]); }
		if(p.name=="$integral"){
			enforce(p.binder!=axis,"an integral shadows the distribution output axis");
			Pattern[] factors;
			void flatten(Pattern q) @safe { if(q.name=="$mul"){ flatten(q.args[0]); flatten(q.args[1]); }else factors~=q; }
			flatten(p.args[0]); size_t selected=size_t.max;
			foreach(i,f;factors) if(f.name=="$distributionApply"&&f.args[1].name==p.binder){
				enforce(selected==size_t.max,"multiple distributions for one integration axis are unsupported"); selected=i;
			}
			if(selected==size_t.max) return pattern("integralD",[lambda(p.binder,p.annotation,lower(p.args[0],axis,ty))]);
			enforce(!distributionOccurs(factors[selected].args[0],axis),"integration source depending on the output axis is unsupported");
			auto measure=lower(factors[selected],p.binder,p.annotation); Pattern rest;
			foreach(i,f;factors) if(i!=selected) rest=rest is null?f:pattern("$mul",[rest,f]);
			enforce(rest !is null,"a distribution-valued integral needs an output form");
			// Keep the map of a restricted Lebesgue graph. A row-wise bind
			// forgets it before a downstream pointwise density query.
			auto base=factors[selected].args[0];
			if(base.name=="λ"&&!base.called&&rest.name=="$mul"){
				foreach(i;0..2){
					auto mask=rest.args[i],point=rest.args[1-i];
					if(mask.name!="$iverson"||point.name!="$distributionApply"||point.args[1].name!=axis) continue;
					auto atom=point.args[0];
					if((atom.name!="δ"&&atom.name!="dirac")||atom.args.length!=1||
						distributionOccurs(mask,axis)||distributionOccurs(atom,axis)) continue;
					auto pred=lambda(p.binder,p.annotation,expand(mask.args[0]));
					auto map=lambda(p.binder,p.annotation,typed(expand(atom.args[0]),ty));
					return typed(pattern("pushforwardOnD",[pred,map]),dt);
				}
			}
			return pattern("bindD",[measure,lambda(p.binder,p.annotation,lower(rest,axis,ty))]);
		}
		if(p.name=="$distributionApply"){
			enforce(p.args[1].name==axis,"distribution form has an unbound output axis");
			auto d=p.args[0];
			if(d.name=="λ"&&!d.called&&!d.args.length) return typed(new Pattern("lebesgueD"),dt);
			enforce(!distributionOccurs(d,axis),"distribution source must be independent of its output axis");
			return typed(expand(d),dt);
		}
		if(p.name=="$add") return pattern("addD",[lower(p.args[0],axis,ty),lower(p.args[1],axis,ty)]);
		if(p.name=="$neg"){ auto one=new Pattern("#"); one.number=1; return pattern("scaleD",[pattern("$neg",[one]),lower(p.args[0],axis,ty)]); }
		if(p.name=="$mul"){
			auto l=form(p.args[0],axis),r=form(p.args[1],axis);
			enforce(l!=r,"a form product must contain exactly one distribution factor for its output axis");
			auto scalar=p.args[l?1:0],d=p.args[l?0:1];
			// A weight independent of the axis is exactly strict scaling on a Dirac,
			// including when the coefficient or atom is undefined.
			if(d.name=="$distributionApply"&&(d.args[0].name=="δ"||d.args[0].name=="dirac")&&!distributionOccurs(scalar,axis))
				return pattern("scaleD",[expand(scalar),lower(d,axis,ty)]);
			return pattern("weightD",[lambda(axis,ty,expand(scalar)),lower(d,axis,ty)]);
		}
		enforce(false,"unsupported distribution form; expected d[x], a weighted form, or a sum");
		return null;
	}
	expand = (Pattern p) @safe {
		if(p.name=="$distribution") return lower(p.args[0],p.binder,p.annotation);
		if(p.name=="$integral") return pattern("massD",[lower(p.args[0],p.binder,p.annotation)]);
		if(p.name=="$disintegrate"){
			Pattern input,mapping,target;
			if(graphForm(p,input,mapping,target)){
				enforce(!distributionOccurs(mapping,target.name),"a graph map cannot depend on its output axis");
				return pattern("graphFibreD",[lambda(input.name,new TypePattern("Real"),expand(mapping)),target]);
			}
			auto d=p.args[1];
			enforce(d.name=="$distributionApply"&&d.args[0].name=="λ","only disintegration with respect to λ[x] is supported");
			auto x=d.args[1];
			return pattern("densityAtD",[lower(p.args[0],x.name,new TypePattern("Real")),x]);
		}
		enforce(p.name!="$distributionApply","distribution applications need a Λ or ∫ binder, or //λ[x]");
		auto q=new Pattern(p.name=="δ"?"dirac":p.name);
		q.annotation=p.annotation; q.binder=p.binder; q.called=p.called;
		q.number=p.number; q.sort=p.sort; q.variable=p.variable; q.natural=p.natural;
		foreach(a;p.args) q.args~=expand(a);
		return q;
	};
	auto axis=distributionOutputAxis(root);
	if(axis.length){
		auto wrapper=pattern("$distribution",[root]); wrapper.binder=axis; wrapper.annotation=new TypePattern("Real"); root=wrapper;
	}
	return expand(root);
}
