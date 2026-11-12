#!/usr/bin/env python3
import errno
import os
import pathlib
import select
import signal
import struct
import subprocess
import time

if(os.name!="posix"):
	print("Terminal checks skipped (POSIX only).")
	raise SystemExit
import fcntl
import pty
import termios

root=pathlib.Path(__file__).resolve().parents[1]
ready=b"\x1b[?2004h\r\x1b[2K>>> \r\x1b[4C"
left=b"\x1b[D"
right=b"\x1b[C"
up=b"\x1b[A"
down=b"\x1b[B"
home=b"\x1b[H"
end=b"\x1b[F"
delete=b"\x1b[3~"

class Terminal:
	def __init__(self,term="xterm-256color"):
		self.master,self.slave=pty.openpty()
		self.resize(80)
		self.saved=termios.tcgetattr(self.slave)
		self.pending=b""
		self.process=subprocess.Popen([str(root/"build/qsym")],stdin=self.slave,
			stdout=self.slave,stderr=self.slave,preexec_fn=os.setpgrp,
			env={**os.environ,"TERM":term,"LC_ALL":"C.UTF-8"})
	def resize(self,columns):
		fcntl.ioctl(self.slave,termios.TIOCSWINSZ,struct.pack("HHHH",24,columns,0,0))
	def send(self,data):
		if(isinstance(data,str)): data=data.encode()
		while(data): data=data[os.write(self.master,data):]
	def until(self,marker,timeout=10):
		deadline=time.monotonic()+timeout
		while(marker not in self.pending):
			remaining=deadline-time.monotonic()
			assert remaining>0,("terminal timeout",marker,self.pending)
			if(not select.select([self.master],[],[],remaining)[0]): continue
			try: chunk=os.read(self.master,65536)
			except OSError as e:
				if(e.errno!=errno.EIO): raise
				chunk=b""
			assert chunk,("unexpected terminal EOF",self.pending)
			self.pending+=chunk
		at=self.pending.index(marker)+len(marker)
		result,self.pending=self.pending[:at],self.pending[at:]
		return result
	def submit(self,keys,expected,expression=None):
		if(isinstance(keys,str)): keys=keys.encode()
		self.send(keys+b"\r")
		output=self.until(ready)
		if(expected is not None): assert b"\x1b[?2004l"+expected.encode()+b"\r\n" in output,output
		if(expression is not None): assert (">>> "+expression+"\r\n").encode() in output,output
		return output
	def finish(self,key=b"\x04",code=0):
		self.send(key)
		assert self.process.wait(timeout=10)==code
		assert termios.tcgetattr(self.slave)==self.saved,"terminal settings were not restored"
	def close(self):
		if(self.process.poll() is None): self.process.kill(); self.process.wait()
		os.close(self.master); os.close(self.slave)
	def __enter__(self): return self
	def __exit__(self,*args): self.close()

with Terminal() as t:
	t.until(ready)
	assert not termios.tcgetattr(t.slave)[3]&(termios.ECHO|termios.ICANON)
	t.submit("x+x","2·x")
	t.submit(up+home+b"2*"+end,"3·x","2*x+x")
	t.submit(b"1+2"+home+b"\x0b\x19","3","1+2")
	# Killed text survives submission and cancellation; successive kills join.
	t.submit(b"\x19","3","1+2")
	t.send(b"9+8"+home+b"\x0b\x03"); t.until(ready)
	t.submit(b"\x19","17","9+8")
	t.submit(b"3+4"+home+right+b"\x0b\x15\x19","7","3+4")
	t.submit(b"5+6"+home+b"\x0b1+2"+home+b"\x0b\x19\x1by","11","5+6")
	t.submit(b"1+23"+left+b"\x14","33","1+32")
	t.submit(b"1+23"+left+b"\x14\x1f","24","1+23")
	t.submit("α+β".encode()+b"\x1bb\x1bd"+"α".encode(),"2·α","α+α")
	t.submit(b"1+234\x1b\x7f2","3","1+2")
	t.submit("2*x+x","3·x")
	# Recalled entries and the unfinished draft keep their edits and cursor.
	t.submit(b"5+6"+left+up+home+b"3*"+up+down+down+delete+b"7","12","5+7")
	t.submit(b"1+3"+left+delete+b"2"+home+right+right+b"4","43","1+42")
	t.submit(b"2+34\x7f","5","2+3")
	t.submit(b"junk\x151+2","3","1+2")
	t.submit(b"1+2 garbage\x17\x7f","3","1+2")
	t.submit(b"1+2garbage"+left*7+b"\x0b","3","1+2")
	t.send(b"abc\x03"); t.until(ready)
	t.submit("1+2","3")
	t.submit(b"\\alpha+\\alpha","2·α","α+α")
	t.submit(b"[x\\ne0]\\cdot x\\^-1","[x≠0]·x⁻¹","[x≠0]· x⁻¹")
	t.submit(b":vars z:\\bC",None,":vars z:ℂ")
	t.submit(b"(1+\\ii)\\^2","2·ⅈ","(1+ⅈ)²")
	t.submit(b"\\lam\t+\\lambda","2·λ","λ+λ")
	t.submit(b"[x\\le 2]","[x≤2]","[x≤2]")
	t.submit(b"1\\alp\x07+2","3","1+2")
	t.send(b"1\\alp\x1b"); t.until(b"\x1b[5C")
	t.submit("+2","3","1+2")
	t.submit(b"1+2\\^",None,"1+2\\^") # Unknown/incomplete spellings stay literal.
	# UTF-8 bytes may arrive in separate reads, including supplementary characters.
	for b in "α+α".encode():
		t.send(bytes([b])); time.sleep(0.002)
	t.submit(home+delete+"β".encode()+end,None,"β+α")
	t.submit(b"e\xcc\x81+1"+home+delete+b"2","3","2+1")
	t.submit("界+1".encode()+home+right+b"\x7f2","3","2+1")
	# Bracketed paste neither expands backslashes nor submits embedded newlines.
	t.send(b"\x1b[200~x+\nx\x1b[201~")
	t.until(b"x+ x\r")
	t.submit(b"","2·x","x+ x")
	t.send(b"\x1b[200~\\alpha\x1b[201~")
	t.until(b"\\alpha\r")
	t.submit(b"\x15"+b"2+2","4","2+2")
	# Resize a scrolled line, then edit its beginning and end.
	t.resize(20)
	t.send(b"1+"*30+b"1")
	t.until(b"\x1b[18C")
	t.resize(36)
	t.submit(home+b"2+"+end,"33","2+"+"1+"*30+"1")
	t.resize(80)
	assert b"\\bR  "+"ℝ".encode() in t.submit(":symbols bR",None)
	t.finish()

# Typeahead after Enter must not disappear when it shares one read buffer.
with Terminal() as t:
	t.until(ready)
	t.send(b"1+2\r3+4\r")
	assert b"3\r\n" in t.until(ready)
	assert b"7\r\n" in t.until(ready)
	t.finish(b":quit\r")

# An externally delivered interrupt cancels input; termination restores termios.
with Terminal() as t:
	t.until(ready); t.send(b"partial"); t.until(b"partial\r")
	t.process.send_signal(signal.SIGINT); t.until(ready)
	t.submit("2+3","5")
	t.process.terminate()
	assert t.process.wait(timeout=10)==-signal.SIGTERM
	assert termios.tcgetattr(t.slave)==t.saved

# Job control releases the terminal while stopped and keeps the draft on resume.
with Terminal() as t:
	t.until(ready); t.send(b"1+\x1a")
	deadline=time.monotonic()+10
	while(True):
		pid,status=os.waitpid(t.process.pid,os.WUNTRACED|os.WNOHANG)
		if(pid):
			assert os.WIFSTOPPED(status),status
			break
		assert time.monotonic()<deadline,"terminal did not suspend"
		time.sleep(0.01)
	assert termios.tcgetattr(t.slave)==t.saved
	t.process.send_signal(signal.SIGCONT); t.until(b"\x1b[?2004h")
	t.submit("2","3","1+2")
	t.finish()

with Terminal("dumb") as t:
	assert b"\x1b" not in t.until(b">>> ")
	t.send(b"1+2\n")
	output=t.until(b">>> ")
	assert b"3\r\n" in output and b"\x1b" not in output,output
	t.finish(b":q\n")
print("Terminal editing checks passed.")

with Terminal() as t:
	t.until(ready)
	t.submit(":vars A:Set(ℝ),B:Set(ℝ)",None)
	t.submit(r"A\sub=A","true","A⊆A")
	t.submit(r"A\subseteq B","(A⊆B)","A⊆ B")
	t.submit(r"A\nsubseteq A","false","A⊈ A")
	t.finish()
print("Subset input-method checks passed.")
