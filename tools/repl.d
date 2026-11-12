module qsym.tools.repl;
import qsym;
import qsym.functional:FunctionSyntax;
import std.stdio:stdout,stderr,writeln;
import std.string:strip,startsWith;
import std.file:write;
import std.exception:enforce;
import qsym.tools.lineedit:LineReader;
import qsym.tools.unicode:symbols;

int repl(){
	auto reader=LineReader.open();
	//if(reader.interactive) writeln("enter an expression; :help for commands.");
	FunctionSyntax syntax,lastSyntax;
	string last;
	bool lastExpand,lastDomain;
	string[] facts,lastFacts;

	for(;;){
		string input; if(!reader.readLine(input)) break;
		auto line=strip(input);
		scope(exit) stdout.flush();
		if(!line.length||line.startsWith("#")) continue;
		try{
			if(line==":quit"||line==":q") break;
			if(line==":help"){
				writeln("Expressions: 2^(1/2), exp(z), sin(z), [x≠0]·x⁻¹, (1+ⅈ)^2");
				writeln("Undeclared variables are real. ASCII operators also work.");
				writeln("Whole numerals default to ℕ; decimals such as 0.125 or 1e-3 are exact rationals.");
				writeln("Up/Down: session history; Left/Right, Home/End, Backspace/Delete: edit.");
				writeln("Unicode: \\alpha → α, \\ne → ≠, \\bR → ℝ, \\^2 → ², \\ii → ⅈ.");
				writeln("Tab completes a unique prefix; Space commits a symbol; Esc cancels it.");
				writeln("Ctrl-A/E: Home/End; Ctrl-U/K/W: kill before/after cursor/previous word.");
				writeln("Ctrl-Y: yank; Alt-Y: cycle kills; Ctrl-_: undo; Ctrl-T: transpose characters.");
				writeln("Alt-B/F: move by word; Alt-Backspace/D: kill word backward/forward; Alt-</>: first/last history.");
				writeln("Ctrl-C: cancel line; Ctrl-D: delete character, or exit on an empty line.");
				writeln("Functions: λ(x:ℝ). 1/x; domains: domain(f), x∈domain(f)");
				writeln("Subsets: {x:ℝ | x>0}, A⊆B; restrictions: λ(x:{t:ℝ | t>0}). log(x)");
				writeln(":vars n:ℕ,k:ℤ,q:ℚ,z:ℂ,p:𝔹   declare types; :vars lists them");
				writeln(":symbols [PREFIX] list Unicode input spellings");
				writeln(":functions [PREFIX] list built-in signatures");
				writeln(":assume EXPR      assume a defined, true Boolean expression");
				writeln(":facts            list assumptions; :clear removes them");
				writeln(":expand EXPR      simplify with polynomial power expansion");
				writeln(":domain EXPR      definedness condition, or input subset for a function");
				writeln(":type EXPR        inspect the type without simplifying");
				writeln(":lean FILE        export a Lean certificate for the last expression");
				writeln(":reset            clear assumptions, variables and the last expression");
				writeln(":quit             exit (or EOF)");
				continue;
			}
			if(line==":symbols"||line.startsWith(":symbols ")){
				auto prefix=strip(line[8..$]);
				if(prefix.startsWith("\\")) prefix=prefix[1..$];
				foreach(s;symbols) if(s.key.startsWith(prefix)) writeln("\\",s.key,"  ",s.text);
				continue;
			}
			if(line==":functions"||line.startsWith(":functions ")){
				auto prefix=strip(line[10..$]);
				foreach(i;0..cast(uint)Builtin.invalid){
					auto f=builtinInfo(cast(Builtin)i);
					if(!f.name.startsWith(prefix)) continue;
					stdout.write(f.name,"(");
					foreach(j,s;f.args) stdout.write(j?",":"",sortName(s));
					writeln("): ",sortName(f.result));
				}
				continue;
			}
			if(line==":reset"){ syntax=FunctionSyntax.init; lastSyntax=FunctionSyntax.init; last=null; facts=null; lastFacts=null; continue; }
			if(line==":vars"){
				foreach(v;syntax.scalar.variables) writeln(v.name,":",sortName(v.sort));
				foreach(f;syntax.functions) writeln(f.name,":",syntax.typeName(f.type));
				continue;
			}
			if(line.startsWith(":vars ")){
				auto next=syntax; next.declare(strip(line[6..$]));
				if(facts.length){
					foreach(i,v;syntax.scalar.variables) enforce(next.scalar.variables[i].sort==v.sort,"use :clear before changing the type of "~v.name);
					foreach(i,v;syntax.functions) enforce(next.functions[i].type==v.type,"use :clear before changing the type of "~v.name);
				}
				syntax=next; continue;
			}
			if(line==":facts"){ foreach(f;facts) writeln(f); continue; }
			if(line==":type"||line.startsWith(":type ")){
				auto source=strip(line[5..$]); enforce(source.length!=0,"expected an expression");
				auto next=syntax,session=Session.open(); writeln(next.inspectType(session.arena,source)); syntax=next; continue;
			}
			if(line==":clear"){ facts=null; continue; }
			if(line.startsWith(":assume ")){
				auto source=strip(line[8..$]),next=syntax;
				auto session=Session.open(); auto a=session.arena;
				enforce(a.sort(next.assumption(a,source))==Sort.boolean,"assumptions must be Bool");
				syntax=next; facts~=source; continue;
			}
			if(line.startsWith(":lean ")){
				enforce(last.length!=0,"no expression to export");
				auto path=strip(line[6..$]); enforce(path.length!=0,"expected a file name");
				auto session=Session.open(); auto a=session.arena;
				auto assumptions=lastSyntax.assumptions(a,lastFacts);
				auto options=Options(DensityMode.preserve,true); options.expandPowers=lastExpand;
				auto result=lastSyntax.run(a,last,FunctionSyntax.predicates(assumptions),options,lastDomain);
				write(path,lastSyntax.exportCertificate(a,result,assumptions));
				writeln("Wrote ",path);
				continue;
			}
			auto options=Options.init; bool domainQuery;
			if(line==":domain"||line.startsWith(":domain ")){
				line=strip(line[7..$]); enforce(line.length!=0,"expected an expression");
				domainQuery=true;
			}else
			if(line==":expand"||line.startsWith(":expand ")){
				line=strip(line[7..$]); enforce(line.length!=0,"expected an expression");
				options.expandPowers=true;
			}else enforce(!line.startsWith(":"),"unknown command; use :help");
			auto session=Session.open(); auto a=session.arena;
			auto assumptions=syntax.assumptions(a,facts);
			auto next=syntax,result=next.run(a,line,FunctionSyntax.predicates(assumptions),options,domainQuery);
			writeln(next.format(a,result)); syntax=next;
			if(result.exhausted) stderr.writeln("simplification budget exhausted; showing the partial result");
			last=line; lastSyntax=syntax; lastFacts=facts.dup; lastExpand=options.expandPowers; lastDomain=domainQuery;
		}catch(Exception e){ stderr.writeln(e.msg); }
	}
	return 0;
}
