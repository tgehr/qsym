module qsym.tools.edit;
import qsym.tools.unicode:symbolMatch;
import std.uni:graphemeStride,isWhite;
import std.utf:decode;
@safe:

enum Key{ none,text,left,right,home,end,up,down,backspace,del,enter,cancel,eof,
	killBefore,killAfter,killWord,complete,escape,suspend,clear,pasteStart,pasteEnd,wordLeft,wordRight }
struct Event{ Key key; string text; }

// Streaming decoder: UTF-8 and escape sequences may cross read boundaries.
struct KeyDecoder{
	private string escape,utf8;
	private size_t expected;
	bool pendingEscape()const{ return escape.length!=0; }
	Event timeout(){ escape=null; return Event(Key.escape); }
	Event feed(ubyte c){
		if(escape.length){
			if(escape.length==1&&c!='['&&c!='O'){ escape=null; return feed(c); }
			escape~=cast(char)c;
			if(escape.length>32){ escape=null; return Event.init; }
			if(escape.length<3||c<0x40||c>0x7e) return Event.init;
			auto s=escape; escape=null;
			import std.algorithm:canFind;
			switch(c){
				case 'A':return Event(Key.up);
				case 'B':return Event(Key.down);
				case 'C':return Event(s.canFind(";5")?Key.wordRight:Key.right);
				case 'D':return Event(s.canFind(";5")?Key.wordLeft:Key.left);
				case 'H':return Event(Key.home);
				case 'F':return Event(Key.end);
				case '~':
					switch(s){
						case "\x1b[1~","\x1b[7~":return Event(Key.home);
						case "\x1b[4~","\x1b[8~":return Event(Key.end);
						case "\x1b[3~":return Event(Key.del);
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
			case 21:return Event(Key.killBefore);
			case 23:return Event(Key.killWord);
			case 26:return Event(Key.suspend);
			case 27:escape="\x1b"; return Event.init;
			default:return c>=32?Event(Key.text,[cast(char)c].idup):Event.init;
		}
	}
}

enum Action{ redraw,accept,cancel,eof,beep,clear,suspend,none }
struct EditBuffer{
	enum limit=64*1024;
	private enum absent=size_t.max;
	private struct Draft{ string text; size_t cursor,composition=absent; }
	private Draft current;
	private Draft[] drafts;
	private size_t selected;
	private bool paste;
	this(string[] history){
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
	private size_t wordLeft(){
		auto p=cursor;
		while(p&&white(previous(p))) p=previous(p);
		while(p&&!white(previous(p))) p=previous(p);
		return p;
	}
	private size_t wordRight(){
		auto p=cursor;
		while(p<text.length&&!white(p)) p=following(p);
		while(p<text.length&&white(p)) p=following(p);
		return p;
	}
	Action handle(Event e){
		if(e.key==Key.none) return Action.none;
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
			case Key.up:history(true); break;
			case Key.down:history(false); break;
			case Key.backspace:if(cursor) remove(previous(cursor),cursor); break;
			case Key.del:if(cursor<text.length) remove(cursor,following(cursor)); break;
			case Key.killBefore:remove(0,cursor); break;
			case Key.killAfter:remove(cursor,text.length); break;
			case Key.killWord:remove(wordLeft(),cursor); break;
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
		"\x1b[H","\x1b[F","\x1b[3~","\x7f","\x01","\x05","\x07","\t","\x15","\x17","\x0b"];
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
