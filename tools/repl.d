module qsym.tools.repl;
import qsym;
import std.stdio:stdin,stdout,stderr,writeln;
import std.string:strip,startsWith;
import std.file:write;
import std.exception:enforce;

version(Windows) extern(C) int _isatty(int);

int repl(){
	version(Posix){
		import core.sys.posix.unistd:isatty;
		bool interactive=isatty(stdin.fileno())!=0;
	}else version(Windows){
		bool interactive=_isatty(stdin.fileno())!=0;
	}else bool interactive=true;
	if(interactive) writeln("qsym — enter an expression; :help for commands.");
	Syntax syntax,lastSyntax;
	string last;
	for(;;){
		if(interactive){ stdout.write("qsym> "); stdout.flush(); }
		auto input=stdin.readln(); if(input is null) break;
		auto line=strip(input);
		scope(exit) stdout.flush();
		if(!line.length||line.startsWith("#")) continue;
		try{
			if(line==":quit"||line==":q") break;
			if(line==":help"){
				writeln("Expressions: (x+1)^2, [x≠0]·x⁻¹, abs(x), (1+ⅈ)^2");
				writeln("Undeclared variables are real. ASCII operators also work.");
				writeln(":vars z:ℂ,p:𝔹   declare variable types; :vars lists them");
				writeln(":lean FILE        export a Lean certificate for the last expression");
				writeln(":reset            clear variables and the last expression");
				writeln(":quit             exit (or EOF)");
				continue;
			}
			if(line==":reset"){ syntax=Syntax.init; lastSyntax=Syntax.init; last=null; continue; }
			if(line==":vars"){
				foreach(v;syntax.variables) writeln(v.name,":",sortName(v.sort));
				continue;
			}
			if(line.startsWith(":vars ")){ syntax.declare(strip(line[6..$])); continue; }
			if(line.startsWith(":lean ")){
				enforce(last.length!=0,"no expression to export");
				auto path=strip(line[6..$]); enforce(path.length!=0,"expected a file name");
				auto session=Session.open(); auto a=session.arena;
				auto result=simplify(a,lastSyntax.parse(a,last),Options(DensityMode.preserve,true));
				write(path,exportLean(a,result));
				writeln("Wrote ",path);
				continue;
			}
			enforce(!line.startsWith(":"),"unknown command; use :help");
			auto session=Session.open(); auto a=session.arena;
			auto result=simplify(a,syntax.parse(a,line));
			writeln(syntax.format(a,result.output));
			if(result.exhausted) stderr.writeln("simplification budget exhausted; showing the partial result");
			last=line; lastSyntax=syntax;
		}catch(Exception e){ stderr.writeln(e.msg); }
	}
	return 0;
}
