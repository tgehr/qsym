// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
// Identifier handling adapted from sym/dparse.d, revision
// f80db2f7569499a4368866a4f0d1801a23d504dd (Timon Gehr).
module qsym.lexer;
import std.uni:isAlpha,isWhite;
import std.utf:decode,validate;
import std.ascii:isDigit;
import std.conv:to;
import std.string:startsWith;
@safe:

enum TokenKind{ end,identifier,integer,symbol,power }
struct Token{ TokenKind kind; string text; size_t offset; }

struct Lexer{
	private string source;
	private size_t pos;
	this(string source){ validate(source); this.source=source; }
	private dchar cur(){ auto i=pos; return decode(source,i); }
	private void advance(){ decode(source,pos); }
	private void ws(){
		while(pos<source.length){
			if(isWhite(cur())){ advance(); continue; }
			if(source[pos]=='#'){
				while(pos<source.length&&source[pos]!='\n')++pos;
				continue;
			}
			break;
		}
	}
	private static bool identifierChar(dchar c){
		return isAlpha(c)||c=='_'||c>='₀'&&c<='₉'||c=='₋';
	}
	Token next(){
		ws(); auto start=pos;
		if(pos==source.length) return Token(TokenKind.end,"",pos);
		foreach(s;["<=>","≡","=>","⇒","→","!=","≠","<=","≤",">=","≥","==","&&","||"]){
			if(source[pos..$].startsWith(s)){
				pos+=s.length;
				return Token(TokenKind.symbol,s=="≡"?"<=>":s=="⇒"||s=="→"?"=>":s=="≠"?"!=":s=="≤"?"<=":s=="≥"?">=":s=="=="?"=":s,start);
			}
		}
		auto c=cur();
		if(c=='⁻'||superscript(c)>=0){
			string exponent;
			if(c=='⁻'){ exponent="-"; advance(); }
			auto begin=pos;
			while(pos<source.length&&superscript(cur())>=0){ exponent~=cast(char)('0'+superscript(cur())); advance(); }
			if(pos==begin) throw new Exception("superscript exponent expected");
			return Token(TokenKind.power,exponent,start);
		}
		if(isDigit(c)){
			do{ advance(); }while(pos<source.length&&isDigit(cur()));
			return Token(TokenKind.integer,source[start..pos],start);
		}
		if(c!='ⅈ'&&c!='𝑖'&&(isAlpha(c)||c=='_')){
			do{ advance(); }while(pos<source.length&&(identifierChar(cur())||isDigit(cur())));
			while(pos<source.length&&(cur()=='\''||cur()=='′')) advance();
			return Token(TokenKind.identifier,source[start..pos],start);
		}
		advance();
		string symbol;
		switch(c){
			case '𝑖':symbol="ⅈ"; break;
			case '·','⋅','×':symbol="*"; break;
			case '÷':symbol="/"; break;
			case '−':symbol="-"; break;
			case '∧':symbol="&&"; break;
			case '∨':symbol="||"; break;
			case '¬':symbol="!"; break;
			case '(',')','[',']',',',':',';','+','-','*','/','^','⅟','ⅈ','<','>','=','!','|':symbol=source[start..pos]; break;
			default:throw new Exception("unexpected character '"~source[start..pos]~"' at byte "~to!string(start));
		}
		return Token(TokenKind.symbol,symbol,start);
	}
	private static int superscript(dchar c){
		foreach(i,x;"⁰¹²³⁴⁵⁶⁷⁸⁹"d) if(c==x) return cast(int)i;
		return -1;
	}
}

// Injective ASCII encoding; prefixes at call sites avoid target-language keywords.
string symbolCode(string name){
	bool plain=!name.startsWith("u_");
	foreach(c;name) if(!(c>='a'&&c<='z'||c>='A'&&c<='Z'||c>='0'&&c<='9'||c=='_')) plain=false;
	if(plain) return name;
	string code="u_";
	foreach(c;name){ code~="0123456789abcdef"[c>>4]; code~="0123456789abcdef"[c&15]; }
	return code;
}

unittest{
	import std.exception:assertThrown;
	auto l=Lexer("\u2003# comment\nα₁′:ℂ⇒α₁′·ⅈ");
	assert(l.next().text=="α₁′");
	assert(l.next().text==":");
	assert(l.next().text=="ℂ");
	assert(l.next().text=="=>");
	assert(l.next().text=="α₁′");
	assert(l.next().text=="*");
	assert(l.next().text=="ⅈ");
	assert(l.next().kind==TokenKind.end);
	assertThrown(Lexer("\xff"));
	assert(symbolCode("α")!=symbolCode("u_ceb1"));
}
