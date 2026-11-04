module qsym.tools.repl;
import qsym;
import std.stdio:stdout,stderr,writeln;
import std.string:strip,startsWith;
import std.file:write;
import std.exception:enforce;
import qsym.tools.lineedit:LineReader;
import qsym.tools.unicode:symbols;

int repl(){
	auto reader=LineReader.open();
	if(reader.interactive) writeln("qsym — enter an expression; :help for commands.");
	Syntax syntax,lastSyntax;
	string last;
	for(;;){
		string input; if(!reader.readLine(input)) break;
		auto line=strip(input);
		scope(exit) stdout.flush();
		if(!line.length||line.startsWith("#")) continue;
		try{
			if(line==":quit"||line==":q") break;
			if(line==":help"){
				writeln("Expressions: (x+1)^2, [x≠0]·x⁻¹, abs(x), (1+ⅈ)^2");
				writeln("Undeclared variables are real. ASCII operators also work.");
				writeln("Up/Down: session history; Left/Right, Home/End, Backspace/Delete: edit.");
				writeln("Unicode: \\alpha → α, \\ne → ≠, \\bR → ℝ, \\^2 → ², \\ii → ⅈ.");
				writeln("Tab completes a unique prefix; Space commits a symbol; Esc cancels it.");
				writeln("Ctrl-A/E: Home/End; Ctrl-U/K/W: delete before/after cursor/previous word.");
				writeln("Ctrl-C: cancel line; Ctrl-D: delete character, or exit on an empty line.");
				writeln(":vars z:ℂ,p:𝔹   declare variable types; :vars lists them");
				writeln(":symbols [PREFIX] list Unicode input spellings");
				writeln(":lean FILE        export a Lean certificate for the last expression");
				writeln(":reset            clear variables and the last expression");
				writeln(":quit             exit (or EOF)");
				continue;
			}
			if(line==":symbols"||line.startsWith(":symbols ")){
				auto prefix=strip(line[8..$]);
				if(prefix.startsWith("\\")) prefix=prefix[1..$];
				foreach(s;symbols) if(s.key.startsWith(prefix)) writeln("\\",s.key,"  ",s.text);
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
