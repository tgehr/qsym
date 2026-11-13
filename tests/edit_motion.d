module edit_motion_tests;
import qsym.tools.edit;
import std.array:replicate;
import std.exception:enforce;
import std.stdio:writeln;
import std.string:indexOf;
import std.utf:validate;
@safe:

private EditBuffer buffer(string text){
	auto e=EditBuffer(null); e.handle(Event(Key.pasteStart));
	e.handle(Event(Key.text,text)); e.handle(Event(Key.pasteEnd)); return e;
}
private string position(string marked,out size_t at){
	auto p=marked.indexOf("¦"); enforce(p>=0,"missing cursor"); at=p;
	return marked[0..at]~marked[at+"¦".length..$];
}
private void move(string before,string after,Key key,Action action=Action.redraw){
	size_t start,finish; auto text=position(before,start),expected=position(after,finish);
	enforce(text==expected,"motion changed the test text"); auto e=buffer(text);
	e.handle(Event(Key.home)); while(e.cursor<start) e.handle(Event(Key.right));
	enforce(e.cursor==start,"test cursor splits a grapheme");
	enforce(e.handle(Event(key))==action,before~" wrong action");
	enforce(e.text==text&&e.cursor==finish,before~" -> "~after);
	validate(e.text);
}

int main(){
	struct Motion{ string before,after; Key key; Action action=Action.redraw; }
	enum left=Key.expressionLeft,right=Key.expressionRight;
	auto cases=[
		Motion("¦(α+[β*{γ}])","(α+[β*{γ}])¦",right),
		Motion("(α+[β*{γ}])¦","¦(α+[β*{γ}])",left),
		Motion("¦  (a) tail","  (a)¦ tail",right),
		Motion("head [a]  ¦","head ¦[a]  ",left),
		Motion("¦()[]{}","()¦[]{}",right),
		Motion("()[]{}¦","()[]¦{}",left),
		Motion("(¦[a]{b})","([a]¦{b})",right),
		Motion("([a]{b}¦)","([a]¦{b})",left),
		Motion("¦e\u0301₁+界","e\u0301₁+界¦",right),
		Motion("e\u0301₁+界¦","¦e\u0301₁+界",left),
		Motion("¦\u2003α₁′\u2003β","\u2003α₁′¦\u2003β",right),
		Motion("α\u2003β\u2003¦","α\u2003¦β\u2003",left),
		Motion("¦(👩‍💻+e\u0301)","(👩‍💻+e\u0301)¦",right),
		Motion("(👩‍💻+e\u0301)¦","¦(👩‍💻+e\u0301)",left),
		Motion("¦([)]","¦([)]",right,Action.beep),
		Motion("([)]¦","([)]¦",left,Action.beep),
		Motion("¦(a","¦(a",right,Action.beep),
		Motion("a)¦","a)¦",left,Action.beep),
		Motion("(a¦)","(a¦)",right,Action.beep),
		Motion("(¦a)","(¦a)",left,Action.beep),
		Motion("¦","¦",right,Action.beep),
		Motion("¦","¦",left,Action.beep),
		Motion("¦ \u2003","¦ \u2003",right,Action.beep),
		Motion(" \u2003¦"," \u2003¦",left,Action.beep),
		Motion("¦(a) # [}","(a)¦ # [}",right),
		Motion("(a) # [}¦","¦(a) # [}",left),
		Motion("¦(a # )","¦(a # )",right,Action.beep),
		Motion("¦# (a)","¦# (a)",right,Action.beep),
		Motion("# (a)¦","# (a)¦",left,Action.beep),
		Motion("¦(a # ]\nb)","(a # ]\nb)¦",right)
	];
	foreach(c;cases) move(c.before,c.after,c.key,c.action);
	writeln(cases.length," motion cases passed");
	struct Encoding{ string bytes; Key key; }
	auto encodings=[
		Encoding("\x1b\x02",left),Encoding("\x1b\x06",right),
		Encoding("\x1b[27;7;98~",left),Encoding("\x1b[27;7;102~",right),
		Encoding("\x1b[27;8;66~",left),Encoding("\x1b[27;8;70~",right),
		Encoding("\x1b[98;7u",left),Encoding("\x1b[102;7u",right),
		Encoding("\x1b[98;7:1u",left),Encoding("\x1b[102;7:2u",right),
		Encoding("\x1b[98;71u",left),Encoding("\x1b[102;199u",right),
		Encoding("\x1b[98;7:3u",Key.none),Encoding("\x1b[102;7:0u",Key.none),
		Encoding("\x1b[98;5u",Key.none),Encoding("\x1b[102;3u",Key.none),
		Encoding("\x1b[98;15u",Key.none),Encoding("\x1b[98;0u",Key.none),
		Encoding("\x1b[99;7u",Key.none),Encoding("\x1b[98;9999999u",Key.none),
		Encoding("\x1b[98;7:u",Key.none),Encoding("\x1b[98;7;1u",Key.none),
		Encoding("\x1bb",Key.wordLeft),Encoding("\x1bf",Key.wordRight),
		Encoding("\x02",Key.left),Encoding("\x06",Key.right),
		Encoding("\x1b[3~",Key.del),Encoding("\x1b[200~",Key.pasteStart)
	];
	foreach(c;encodings){
		KeyDecoder decoder;
		foreach(i,ubyte b;c.bytes){
			auto event=decoder.feed(b);
			enforce(event.key==(i+1==c.bytes.length?c.key:Key.none),"key decoding");
		}
		enforce(!decoder.pendingEscape,"incomplete sequence");
		enforce(decoder.feed('x').key==Key.text,"decoder recovery");
	}
	writeln(encodings.length," encoding cases passed");
	uint seed=20261113;
	string[] opens=["(","[","{"],closes=[")","]","}"];
	foreach(i;0..256){
		string text="e\u0301+👩‍💻+α₁′";
		foreach(j;0..1+i%24){
			seed=1664525*seed+1013904223; auto k=seed%3;
			text=opens[k]~"α "~text~" β"~closes[k];
		}
		move("before ¦"~text~" after","before "~text~"¦ after",right);
		move("before "~text~"¦ after","before ¦"~text~" after",left);
	}
	writeln("512 generated balanced-expression movements passed");
	auto deep="(".replicate(EditBuffer.limit/2)~")".replicate(EditBuffer.limit/2);
	move("¦"~deep,deep~"¦",right); move(deep~"¦","¦"~deep,left);
	auto atom="α".replicate(EditBuffer.limit/2);
	move("¦"~atom,atom~"¦",right); move(atom~"¦","¦"~atom,left);
	auto e=buffer("(a)"); e.handle(Event(Key.text,"+b")); e.handle(Event(left));
	e.handle(Event(Key.undo)); enforce(e.text=="(a)"&&e.cursor==3,"motion polluted undo");
	e=EditBuffer(["(a)","[b]"]); e.handle(Event(Key.up)); e.handle(Event(left));
	e.handle(Event(Key.up)); e.handle(Event(Key.down)); enforce(e.text=="[b]"&&e.cursor==0,"history cursor");
	e=buffer("(a)"); e.handle(Event(Key.pasteStart));
	enforce(e.handle(Event(left))==Action.none,"paste executed motion");
	e.handle(Event(Key.text,"x")); e.handle(Event(Key.pasteEnd)); enforce(e.text=="(a)x","paste insertion");
	writeln("Boundary, undo, history and paste checks passed"); return 0;
}
