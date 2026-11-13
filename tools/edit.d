module qsym.tools.edit;
import qsym.tools.unicode:symbolMatch;
import std.uni:graphemeStride,isWhite,isAlphaNum;
import std.utf:decode;
@safe:

enum Key{ none,text,left,right,home,end,up,down,backspace,del,enter,cancel,eof,
	killBefore,killAfter,killWord,complete,escape,suspend,clear,pasteStart,pasteEnd,wordLeft,wordRight,
	killWordBefore,killWordAfter,yank,yankPop,undo,transpose,first,last,expressionLeft,expressionRight }
struct Event{ Key key; string text; }

// Streaming decoder: UTF-8 and escape sequences may cross read boundaries.
struct KeyDecoder{
	private string escape,utf8;
	private size_t expected;
	bool pendingEscape()const{ return escape.length!=0; }
	Event timeout(){ escape=null; return Event(Key.escape); }
	private static Event modifiedExpression(string s){
		if(s.length<3||s[0..2]!="\x1b[") return Event.init;
		auto end=s[$-1]; s=s[2..$-1]; size_t at;
		bool number(out uint n){
			auto start=at; n=0;
			while(at<s.length&&s[at]>='0'&&s[at]<='9'){
				if(n>6553) return false;
				n=n*10+s[at++]-'0';
			}
			return at!=start;
		}
		bool take(char c){ if(at==s.length||s[at]!=c) return false; ++at; return true; }
		uint code,modifiers,kind=1;
		if(!number(code)||!take(';')||!number(modifiers)) return Event.init;
		if(end=='~'){
			if(code!=27||!take(';')||!number(code)) return Event.init;
		}else if(end=='u'){
			if(take(':')&&!number(kind)) return Event.init;
		}else return Event.init;
		if(at!=s.length||!modifiers||((modifiers-1)&~(1u|64u|128u))!=6||kind<1||kind>2) return Event.init;
		return Event(code=='b'||code=='B'?Key.expressionLeft:code=='f'||code=='F'?Key.expressionRight:Key.none);
	}
	Event feed(ubyte c){
		if(escape.length){
			if(escape.length==1&&c!='['&&c!='O'){
				escape=null;
				switch(c){
					case 2:return Event(Key.expressionLeft);
					case 6:return Event(Key.expressionRight);
					case 'b','B':return Event(Key.wordLeft);
					case 'f','F':return Event(Key.wordRight);
					case 'd','D':return Event(Key.killWordAfter);
					case 'y','Y':return Event(Key.yankPop);
					case 8,127:return Event(Key.killWordBefore);
					case '<':return Event(Key.first);
					case '>':return Event(Key.last);
					default:return Event.init;
				}
			}
			escape~=cast(char)c;
			if(escape.length>32){ escape=null; return Event.init; }
			if(escape.length<3||c<0x40||c>0x7e) return Event.init;
			auto s=escape; escape=null;
			if(c=='u'||c=='~'){
				auto event=modifiedExpression(s); if(event.key!=Key.none) return event;
			}
			import std.algorithm:canFind;
			switch(c){
				case 'A':return Event(Key.up);
				case 'B':return Event(Key.down);
				case 'C':return Event(s.canFind(";5")||s.canFind(";3")?Key.wordRight:Key.right);
				case 'D':return Event(s.canFind(";5")||s.canFind(";3")?Key.wordLeft:Key.left);
				case 'H':return Event(Key.home);
				case 'F':return Event(Key.end);
				case '~':
					switch(s){
						case "\x1b[1~","\x1b[7~":return Event(Key.home);
						case "\x1b[4~","\x1b[8~":return Event(Key.end);
						case "\x1b[3~":return Event(Key.del);
						case "\x1b[3;5~","\x1b[3;3~":return Event(Key.killWordAfter);
						case "\x1b[200~":return Event(Key.pasteStart);
						case "\x1b[201~":return Event(Key.pasteEnd);
						default:return Event.init;
					}
				default:return Event.init;
			}
		}
		if(utf8.length){
			if((c&0xc0)!=0x80){ utf8=null; expected=0; return feed(c); }
			utf8~=cast(char)c;
			if(utf8.length<expected) return Event.init;
			auto s=utf8; utf8=null; expected=0;
			try{ size_t i; auto value=decode(s,i); if(value>=0xa0) return Event(Key.text,s); }catch(Exception){}
			return Event.init;
		}
		if(c>=0x80){
			expected=c>=0xc2&&c<=0xdf?2:c>=0xe0&&c<=0xef?3:c>=0xf0&&c<=0xf4?4:0;
			if(expected) utf8=[cast(char)c].idup;
			return Event.init;
		}
		switch(c){
			case 1:return Event(Key.home);
			case 2:return Event(Key.left);
			case 3:return Event(Key.cancel);
			case 4:return Event(Key.eof);
			case 5:return Event(Key.end);
			case 6:return Event(Key.right);
			case 7:return Event(Key.escape);
			case 8,127:return Event(Key.backspace);
			case 9:return Event(Key.complete);
			case 10,13:return Event(Key.enter);
			case 11:return Event(Key.killAfter);
			case 12:return Event(Key.clear);
			case 14:return Event(Key.down);
			case 16:return Event(Key.up);
			case 20:return Event(Key.transpose);
			case 21:return Event(Key.killBefore);
			case 23:return Event(Key.killWord);
			case 25:return Event(Key.yank);
			case 26:return Event(Key.suspend);
			case 27:escape="\x1b"; return Event.init;
			case 31:return Event(Key.undo);
			default:return c>=32?Event(Key.text,[cast(char)c].idup):Event.init;
		}
	}
}

enum Action{ redraw,accept,cancel,eof,beep,clear,suspend,none }
final class KillRing{ private string[] entries; }
struct EditBuffer{
	enum limit=64*1024;
	private enum absent=size_t.max;
	private struct Draft{ string text; size_t cursor,composition=absent; }
	private Draft current;
	private Draft[] drafts;
	private size_t selected;
	private bool paste;
	private KillRing kills;
	private Draft[] undo;
	private Key lastKey;
	private size_t yankStart,yankEnd,killIndex;
	private bool yanking;
	this(string[] history,KillRing kills=null){
		this.kills=kills is null?new KillRing:kills;
		foreach(s;history) drafts~=Draft(s,s.length);
		drafts~=Draft.init; selected=history.length;
	}
	string text()const{ return current.text; }
	size_t cursor()const{ return current.cursor; }
	private size_t previous(size_t at){
		size_t p;
		for(size_t i;i<at;i+=graphemeStride(text,i)) p=i;
		return p;
	}
	private size_t following(size_t at){ return at<text.length?at+graphemeStride(text,at):at; }
	private void snap(){
		size_t i;
		while(i<cursor) i=following(i);
		current.cursor=i;
	}
	private bool insert(string s){
		if(text.length+s.length>limit) return false;
		current.text=text[0..cursor]~s~text[cursor..$]; current.cursor+=s.length; snap(); return true;
	}
	private void remove(size_t start,size_t end){
		current.text=text[0..start]~text[end..$]; current.cursor=start; snap();
		if(start<=current.composition) current.composition=absent;
	}
	private bool composing()const{ return current.composition!=absent; }
	private string spelling(){ return text[current.composition+1..cursor]; }
	private bool substitute(string value){
		auto start=current.composition;
		if(text.length-(cursor-start)+value.length>limit) return false;
		current.text=text[0..start]~value~text[cursor..$]; current.cursor=start+value.length;
		current.composition=absent; snap(); return true;
	}
	private void finish(){
		if(!composing) return;
		auto m=symbolMatch(spelling);
		if(m.exact.length) substitute(m.exact);
		current.composition=absent;
	}
	private bool type(string s){
		if(!composing){
			auto start=cursor;
			if(!insert(s)) return false;
			if(s=="\\") current.composition=start;
			return true;
		}
		auto old=symbolMatch(spelling),next=symbolMatch(spelling~s);
		if(!next.prefix){
			finish();
			if(s==" "&&old.exact.length) return true;
			return type(s);
		}
		if(!insert(s)) return false;
		if(next.exact.length&&!next.longer) return substitute(next.exact);
		return true;
	}
	private void history(bool up){
		if(!drafts.length||up&&selected==0||!up&&selected+1==drafts.length) return;
		drafts[selected]=current; selected=up?selected-1:selected+1; current=drafts[selected];
	}
	private bool white(size_t at){ auto i=at; return isWhite(decode(text,i)); }
	private size_t spaceLeft(){
		auto p=cursor;
		while(p&&white(previous(p))) p=previous(p);
		while(p&&!white(previous(p))) p=previous(p);
		return p;
	}
	private bool word(size_t at){ auto i=at,c=decode(text,i); return c=='_'||isAlphaNum(c); }
	private size_t wordLeft(){
		auto p=cursor;
		while(p&&!word(previous(p))) p=previous(p);
		while(p&&word(previous(p))) p=previous(p);
		return p;
	}
	private size_t wordRight(){
		auto p=cursor;
		while(p<text.length&&!word(p)) p=following(p);
		while(p<text.length&&word(p)) p=following(p);
		return p;
	}
	private bool expression(bool forward,out size_t result){
		struct Cell{ size_t end; byte bracket; bool space; }
		Cell[] cells; size_t point; bool comment;
		for(size_t i;i<text.length;){
			auto next=following(i),j=i,c=decode(text,j); byte bracket;
			if(c=='#') comment=true;
			if(!comment) switch(c){
				case '(':bracket=1; break; case ')':bracket=-1; break;
				case '[':bracket=2; break; case ']':bracket=-2; break;
				case '{':bracket=3; break; case '}':bracket=-3; break;
				default:break;
			}
			cells~=Cell(next,bracket,comment||isWhite(c));
			if(c=='\n') comment=false;
			i=next; if(i<=cursor) ++point;
		}
		auto at=point;
		bool more(){ return forward?at<cells.length:at!=0; }
		size_t index(){ return forward?at:at-1; }
		void step(){ if(forward) ++at; else --at; }
		while(more()&&cells[index()].space) step();
		if(!more()) return false;
		int sign=forward?1:-1,b=cells[index()].bracket*sign;
		if(b<0) return false;
		if(!b){
			while(more()&&!cells[index()].space&&!cells[index()].bracket) step();
		}else{
			byte[] stack;
			do{
				b=cells[index()].bracket*sign;
				if(b>0) stack~=cast(byte)b;
				else if(b<0){ if(!stack.length||stack[$-1]!=-b) return false; --stack.length; }
				step();
			}while(more()&&stack.length);
			if(stack.length) return false;
		}
		result=at?cells[at-1].end:0; return true;
	}
	private static bool killing(Key k){
		return k==Key.killBefore||k==Key.killAfter||k==Key.killWord||k==Key.killWordBefore||k==Key.killWordAfter;
	}
	private void kill(size_t start,size_t end,bool backward){
		if(start==end) return;
		auto s=text[start..end];
		if(killing(lastKey)&&kills.entries.length&&kills.entries[0].length+s.length<=limit){
			auto old=kills.entries[0]; kills.entries[0]=backward?s~old:old~s;
		}else{
			if(kills.entries.length==32) kills.entries=kills.entries[0..31];
			kills.entries=[s]~kills.entries;
		}
		remove(start,end);
	}
	Action handle(Event e){
		if(e.key==Key.none) return Action.none;
		if(e.key!=Key.yankPop) yanking=false;
		// Save text changes, grouping ordinary typing and each bracketed paste.
		auto before=current;
		scope(exit){
			if(e.key!=Key.undo&&text!=before.text){
				if((!(e.key==Key.text&&lastKey==Key.text)&&!(paste&&lastKey!=Key.pasteStart))||!undo.length){
					if(undo.length==256) undo=undo[1..$];
					undo~=before;
				}
			}
			lastKey=e.key;
		}
		if(e.key==Key.pasteStart){ finish(); paste=true; return Action.none; }
		if(e.key==Key.pasteEnd){ paste=false; return Action.redraw; }
		if(paste){
			if(e.key==Key.text) return insert(e.text)?Action.redraw:Action.beep;
			if(e.key==Key.enter||e.key==Key.complete) return insert(" ")?Action.redraw:Action.beep;
			return Action.none;
		}
		if(e.key!=Key.text&&e.key!=Key.backspace&&e.key!=Key.complete&&e.key!=Key.escape&&e.key!=Key.up&&e.key!=Key.down) finish();
		final switch(e.key){
			case Key.none,Key.pasteStart,Key.pasteEnd:return Action.none;
			case Key.text:return type(e.text)?Action.redraw:Action.beep;
			case Key.left:current.cursor=previous(cursor); break;
			case Key.right:current.cursor=following(cursor); break;
			case Key.home:current.cursor=0; break;
			case Key.end:current.cursor=text.length; break;
			case Key.wordLeft:current.cursor=wordLeft(); break;
			case Key.wordRight:current.cursor=wordRight(); break;
			case Key.expressionLeft,Key.expressionRight:
				size_t target;
				if(!expression(e.key==Key.expressionRight,target)) return Action.beep;
				current.cursor=target; break;
			case Key.up:history(true); break;
			case Key.down:history(false); break;
			case Key.first:while(selected) history(true); break;
			case Key.last:while(selected+1<drafts.length) history(false); break;
			case Key.backspace:if(cursor) remove(previous(cursor),cursor); break;
			case Key.del:if(cursor<text.length) remove(cursor,following(cursor)); break;
			case Key.killBefore:kill(0,cursor,true); break;
			case Key.killAfter:kill(cursor,text.length,false); break;
			case Key.killWord:kill(spaceLeft(),cursor,true); break;
			case Key.killWordBefore:kill(wordLeft(),cursor,true); break;
			case Key.killWordAfter:kill(cursor,wordRight(),false); break;
			case Key.yank:
				if(!kills.entries.length) return Action.beep;
				yankStart=cursor; killIndex=0;
				if(!insert(kills.entries[0])) return Action.beep;
				yankEnd=yankStart+kills.entries[0].length; yanking=true; break;
			case Key.yankPop:
				if(!yanking) return Action.beep;
				auto index=(killIndex+1)%kills.entries.length,s=kills.entries[index];
				if(text.length-(yankEnd-yankStart)+s.length>limit) return Action.beep;
				current.text=text[0..yankStart]~s~text[yankEnd..$];
				yankEnd=yankStart+s.length; current.cursor=yankEnd; snap(); killIndex=index; break;
			case Key.undo:
				if(!undo.length) return Action.beep;
				current=undo[$-1]; --undo.length; break;
			case Key.transpose:
				if(!cursor) return Action.beep;
				auto end=cursor<text.length?following(cursor):cursor,mid=previous(end),start=previous(mid);
				if(start==mid) return Action.beep;
				current.text=text[0..start]~text[mid..end]~text[start..mid]~text[end..$]; current.cursor=end; snap(); break;
			case Key.enter:return Action.accept;
			case Key.cancel:return Action.cancel;
			case Key.eof:
				if(!text.length) return Action.eof;
				if(cursor<text.length) remove(cursor,following(cursor)); break;
			case Key.complete:
				if(!composing) return Action.beep;
				auto m=symbolMatch(spelling),value=m.exact.length?m.exact:m.unique;
				if(!value.length) return Action.beep;
				if(!substitute(value)) return Action.beep;
				break;
			case Key.escape:
				if(composing) remove(current.composition,cursor);
				break;
			case Key.suspend:return Action.suspend;
			case Key.clear:return Action.clear;
		}
		return Action.redraw;
	}
}

struct View{ string text; size_t start; uint cursor; }
View viewport(W)(string text,size_t cursor,size_t start,uint columns,W width){
	struct Cell{ size_t begin,end; uint width; }
	Cell[] cells; size_t point,first;
	for(size_t i;i<text.length;){
		auto end=i+graphemeStride(text,i); uint n,largest,regional; bool joined;
		foreach(dchar c;text[i..end]){
			auto w=width(c); if(w>0){ n+=w; if(w>largest) largest=w; }
			if(c==0x200d||c>=0x1f3fb&&c<=0x1f3ff) joined=true;
			if(c>=0x1f1e6&&c<=0x1f1ff) ++regional;
		}
		cells~=Cell(i,end,regional==2?2:joined?largest:n); i=end;
	}
	while(point<cells.length&&cells[point].begin<cursor) ++point;
	while(first<point&&cells[first].begin<start) ++first;
	uint offset; foreach(c;cells[first..point]) offset+=c.width;
	while(first<point&&offset>=columns){ offset-=cells[first].width; ++first; }
	auto last=first; uint used;
	while(last<cells.length&&used+cells[last].width<=columns){ used+=cells[last].width; ++last; }
	auto from=first<cells.length?cells[first].begin:text.length;
	auto end=last<cells.length?cells[last].begin:text.length;
	return View(text[from..end],from,offset);
}

unittest{
	import qsym.tools.unicode:symbols;
	auto e=EditBuffer(["x+x","y+y"]); KeyDecoder keys;
	void type(string s){ foreach(ubyte c;s) e.handle(keys.feed(c)); }
	foreach(s;symbols){
		auto check=EditBuffer(null); KeyDecoder decoder;
		foreach(ubyte c;"\\"~s.key) check.handle(decoder.feed(c));
		check.handle(Event(Key.complete)); assert(check.text==s.text,s.key);
	}
	type("draft"); e.handle(Event(Key.up)); assert(e.text=="y+y");
	e.handle(Event(Key.home)); type("2·"); e.handle(Event(Key.up)); assert(e.text=="x+x");
	e.handle(Event(Key.down)); assert(e.text=="2·y+y");
	e.handle(Event(Key.down)); assert(e.text=="draft"&&e.cursor==5);
	e=EditBuffer(null); type("\\alpha+\\bR\\_1+\\ii"); assert(e.text=="α+ℝ₁+ⅈ");
	e=EditBuffer(null); type("x\\ne0"); assert(e.text=="x≠0");
	e=EditBuffer(null); type("x\\le"); e.handle(Event(Key.complete)); type("2"); assert(e.text=="x≤2");
	e=EditBuffer(null); type("\\lam"); e.handle(Event(Key.complete)); assert(e.text=="λ");
	e=EditBuffer(null); type("\\alpha\\_1+1");
	e.handle(Event(Key.left)); e.handle(Event(Key.backspace)); assert(e.text=="α₁1");
	e=EditBuffer(null); type("e\u0301界+1"); e.handle(Event(Key.home)); e.handle(Event(Key.del)); assert(e.text=="界+1");
	e.handle(Event(Key.right)); e.handle(Event(Key.backspace)); assert(e.text=="+1"&&e.cursor==0);
	e=EditBuffer(null); type("a\\alp"); e.handle(Event(Key.escape)); assert(e.text=="a");
	type("\\\\alpha"); assert(e.text=="a\\alpha");
	e=EditBuffer(null); type("\\zzunknown"); assert(e.text=="\\zzunknown");
	e=EditBuffer(null); type("\x1b[200~x+x\n\\alpha\x1b[201~"); assert(e.text=="x+x \\alpha");
	assert(e.handle(Event(Key.enter))==Action.accept);
	e=EditBuffer(null); type("\\al"); e.handle(Event(Key.backspace)); type("lpha"); assert(e.text=="α");
	auto v=viewport("α界x",5,0,3,(dchar c)=>c=='界'?2:1);
	assert(v.cursor<3&&v.text=="界x"&&v.start==2);
	assert(keys.feed(0xff).key==Key.none);
}

unittest{
	import std.utf:validate;
	import std.array:replicate;
	// Editing arbitrary key streams must preserve valid UTF-8 and grapheme boundaries.
	auto e=EditBuffer(["α+β","e\u0301界"]); KeyDecoder keys; uint seed=12345;
	string[] inputs=["x","α","界","\u0301","\\","alp","ne","\x1b[A","\x1b[B","\x1b[C","\x1b[D",
		"\x1b[H","\x1b[F","\x1b[3~","\x7f","\x01","\x05","\x07","\t","\x15","\x17","\x0b",
		"\x19","\x1by","\x1bb","\x1bf","\x1bd","\x1b\x7f","\x1f","\x14","\x1b<","\x1b>"];
	foreach(i;0..5000){
		seed=1664525*seed+1013904223;
		foreach(ubyte c;inputs[seed%inputs.length]) e.handle(keys.feed(c));
		validate(e.text); assert(e.cursor<=e.text.length&&e.text.length<=EditBuffer.limit);
		size_t p; while(p<e.cursor) p+=graphemeStride(e.text,p);
		assert(p==e.cursor);
		auto columns=1+seed%20;
		auto v=viewport(e.text,e.cursor,0,columns,(dchar c)=>1);
		assert(v.cursor<columns&&v.start<=e.cursor); validate(v.text);
	}
	e=EditBuffer(null); e.handle(Event(Key.pasteStart));
	e.handle(Event(Key.text,"x".replicate(EditBuffer.limit-2))); e.handle(Event(Key.pasteEnd));
	e.handle(Event(Key.text,"\\"));
	assert(e.handle(Event(Key.text,"["))==Action.beep&&e.text.length==EditBuffer.limit);
}

unittest{
	auto e=EditBuffer(null); KeyDecoder keys;
	void type(string s){ foreach(ubyte c;s) e.handle(keys.feed(c)); }
	type("α+β\x01\x0b\x19"); assert(e.text=="α+β","Ctrl+Y must restore killed text");
	type("\x01\x06\x0b\x15\x19"); assert(e.text=="α+β","backward kills prepend");
	type("\x01\x0bnew\x15\x19\x1by"); assert(e.text=="α+β","Alt+Y cycles the kill ring");
	type("\x01\x1bf"); assert(e.cursor=="α".length,"Alt+F moves by Unicode words");
	type("\x1bd"); assert(e.text=="α","Alt+D kills the next word");
	type("\x19"); assert(e.text=="α+β");
	type("\x1b\x7f"); assert(e.text=="α+","Alt+Backspace kills the previous word");
	type("\x1f"); assert(e.text=="α+β","Ctrl+_ undoes a kill");
	e=EditBuffer(null); type("αβ\x14"); assert(e.text=="βα","Ctrl+T transposes characters");
	type("\x1f"); assert(e.text=="αβ");
	e=EditBuffer(null); type("e\u0301界\x14"); assert(e.text=="界e\u0301","transpose preserves graphemes");
}
