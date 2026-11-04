module qsym.tools.lineedit;
import qsym.tools.edit;
import std.stdio:stdin,stdout;
import std.process:environment;
import std.string:strip;
import std.algorithm:min,max;

version(Windows) private extern(C) int _isatty(int);

struct LineReader{
	private string[] history;
	private bool tty,editing;
	version(Posix){ private ubyte[4096] input; private size_t begin,end; }
	static LineReader open(){
		LineReader r;
		version(Posix){
			r.tty=isatty(stdin.fileno())!=0&&isatty(stdout.fileno())!=0;
			r.editing=r.tty&&environment.get("TERM","")!="dumb";
			if(r.editing) setlocale(LC_CTYPE,"");
		}else version(Windows) r.tty=_isatty(stdin.fileno())!=0&&_isatty(stdout.fileno())!=0;
		return r;
	}
	bool interactive()const{ return tty; }
	bool readLine(out string line,string prompt=">>> "){
		version(Posix) if(editing) return readEdited(line,prompt);
		if(tty){ stdout.write(prompt); stdout.flush(); }
		line=stdin.readln(); return line !is null;
	}
	private void remember(string line){
		if(!strip(line).length||history.length&&history[$-1]==line) return;
		if(history.length==512) history=history[1..$];
		history~=line;
	}
	version(Posix) private bool readEdited(out string line,string prompt){
		auto buffer=EditBuffer(history); KeyDecoder decoder; size_t start; uint paintedColumns;
		RawTerminal terminal;
		scope(exit) terminal.leave();
		terminal.enter();
		void draw(){
			auto columns=terminal.columns; paintedColumns=columns;
			auto p=prompt[0..min(prompt.length,columns-2)];
			auto v=viewport(buffer.text,buffer.cursor,start,cast(uint)(columns-p.length-1),&characterWidth);
			start=v.start;
			stdout.write("\r\x1b[2K",p,v.text,"\r");
			if(p.length+v.cursor) stdout.write("\x1b[",p.length+v.cursor,"C");
			stdout.flush();
		}
		void echo(string suffix=""){
			stdout.write("\r\x1b[2K",prompt,buffer.text,suffix,"\n"); stdout.flush();
		}
		draw();
		for(;;){
			if(terminal.columns!=paintedColumns){
				// Reflow differs between terminals; start a fresh row after a resize.
				stdout.write("\r\n"); draw();
			}
			auto signals=atomicExchange(&pendingSignals,0u);
			foreach(i,sig;handledSignals) if(signals&(1u<<i)){
				if(sig==SIGINT){ echo("^C"); return true; }
				else{
					terminal.leave(); raise(sig);
					terminal.enter(); draw();
				}
			}
			Event event;
			if(begin==end){
				pollfd fd=pollfd(stdin.fileno(),POLLIN,0);
				auto ready=poll(&fd,1,100);
				if(ready<0){ if(errno==EINTR) continue; throw new Exception("terminal poll failed"); }
				if(!ready){
					if(!decoder.pendingEscape) continue;
					event=decoder.timeout();
				}else{
					auto n=read(fd.fd,input.ptr,input.length);
					if(n<0){ if(errno==EINTR) continue; throw new Exception("terminal read failed"); }
					if(!n){ echo(); return false; }
					begin=0; end=n;
				}
			}
			if(begin<end) event=decoder.feed(input[begin++]);
			final switch(buffer.handle(event)){
				case Action.accept:line=buffer.text; remember(line); echo(); return true;
				case Action.cancel:echo("^C"); return true;
				case Action.eof:echo(); return false;
				case Action.suspend:
					terminal.leave(); raise(SIGTSTP); terminal.enter(); draw(); break;
				case Action.clear:stdout.write("\x1b[2J\x1b[H"); draw(); break;
				case Action.beep:stdout.write("\a"); break;
				case Action.redraw:break;
				case Action.none:break;
			}
			if(begin==end) draw();
		}
	}
}

version(Posix){
	import core.sys.posix.unistd:isatty,read;
	import core.sys.posix.termios;
	import core.sys.posix.poll;
	import core.sys.posix.signal;
	import core.sys.posix.sys.ioctl:ioctl,winsize,TIOCGWINSZ;
	import core.stdc.errno:errno,EINTR;
	import core.stdc.locale:setlocale,LC_CTYPE;
	import core.atomic:atomicOp,atomicExchange;
	private extern(C) int wcwidth(dchar) nothrow @nogc;
	private int characterWidth(dchar c)@trusted{ auto n=wcwidth(c); return n<0?1:n; }
	private enum handledSignals=[SIGTERM,SIGHUP,SIGQUIT,SIGTSTP,SIGINT];
	private shared uint pendingSignals;
	private extern(C) void onSignal(int sig)nothrow @nogc{
		foreach(i,s;handledSignals) if(s==sig) atomicOp!"|="(pendingSignals,1u<<i);
	}
	// Only the CLI's terminal boundary uses unsafe C interfaces; editing is @safe.
	private struct RawTerminal{
		termios saved;
		sigaction_t[handledSignals.length] handlers;
		size_t installed;
		bool active;
		void enter(){
			if(tcgetattr(stdin.fileno(),&saved)!=0) throw new Exception("cannot read terminal settings");
			sigaction_t action; action.sa_handler=&onSignal; sigemptyset(&action.sa_mask);
			foreach(sig;handledSignals){
				if(sigaction(sig,&action,&handlers[installed])!=0) throw new Exception("cannot install terminal signal handler");
				++installed;
			}
			auto raw=saved;
			raw.c_iflag&=~(BRKINT|ICRNL|INLCR|IGNCR|INPCK|ISTRIP|IXON);
			raw.c_cflag=(raw.c_cflag&~(CSIZE|PARENB))|CS8;
			raw.c_lflag&=~(ECHO|ICANON|IEXTEN|ISIG);
			raw.c_cc[VMIN]=1; raw.c_cc[VTIME]=0;
			if(tcsetattr(stdin.fileno(),TCSANOW,&raw)!=0) throw new Exception("cannot enable terminal editing");
			active=true;
			stdout.write("\x1b[?2004h"); stdout.flush();
		}
		void leave(){
			if(active){
				// Restore termios before any output operation that could throw.
				while(tcsetattr(stdin.fileno(),TCSANOW,&saved)<0&&errno==EINTR){}
				active=false;
			}
			bool disable=installed!=0;
			while(installed){ --installed; sigaction(handledSignals[installed],&handlers[installed],null); }
			if(disable){ stdout.write("\x1b[?2004l"); stdout.flush(); }
		}
		uint columns(){
			winsize size;
			return ioctl(stdout.fileno(),TIOCGWINSZ,&size)==0&&size.ws_col?max(2u,size.ws_col):80;
		}
	}
}
