import json
import os
import pathlib
import signal
import subprocess
import time

class Progress:
	def __init__(self,path,total,interval=10):
		self.path=pathlib.Path(path)
		self.total=total
		self.interval=interval
		self.started=self.last_report=time.monotonic()
		self.offset=0
		self.pending=b""
		self.active={}
		self.completed={}
		self.warned=False

	def emit(self,message):
		print(f"[Lean {time.monotonic()-self.started:.1f}s] {message}",flush=True)
		self.last_report=time.monotonic()

	def warn(self,message):
		if not self.warned:
			self.emit(message+"; Lean's exit status remains authoritative.")
			self.warned=True

	def read(self):
		try:
			with self.path.open("rb") as stream:
				stream.seek(self.offset)
				data=stream.read()
				self.offset+=len(data)
		except OSError as error:
			self.warn(f"Could not read progress: {error}")
			return
		lines=(self.pending+data).split(b"\n")
		self.pending=lines.pop()
		for line in lines:
			try:
				record=json.loads(line)
				name=record["name"]
				key=(record["module"],name)
				stamp=record["time_ms"]
				event=record["event"]
				if not isinstance(name,str) or not isinstance(key[0],str) or not isinstance(stamp,int):
					raise ValueError("invalid progress record")
			except (ValueError,KeyError,TypeError):
				self.warn("Ignoring malformed progress record")
				continue
			if event=="start":
				self.active[key]={"stamp":stamp,"received":time.monotonic(),"phase":"cache lookup"}
				if not self.completed and len(self.active)==1:
					self.emit(f"checking {name}")
			elif key in self.active:
				active=self.active[key]
				if event in ("cache","tactics"):
					active["phase"]="cached proof" if event=="cache" else "source tactics"
				elif event=="checked":
					elapsed=max(0,stamp-active["stamp"])/1000
					self.completed[key]=(elapsed,active["phase"])
					del self.active[key]
					if elapsed>=2 or len(self.completed)%50==0:
						self.emit(f"{len(self.completed)}/{self.total} rules checked; {name}: {elapsed:.2f}s ({active['phase']})")

	def heartbeat(self):
		if time.monotonic()-self.last_report<self.interval:
			return
		if self.active:
			items=sorted(self.active.items(),key=lambda item:item[1]["received"])
			current="; ".join(f"{key[1]} ({value['phase']}, {time.monotonic()-value['received']:.1f}s)" for key,value in items[:3])
			if len(items)>3: current+=f"; +{len(items)-3} more"
			self.emit(f"{len(self.completed)}/{self.total} rules checked; active: {current}")
		elif self.completed:
			self.emit(f"{len(self.completed)}/{self.total} rules checked; waiting for Lake to finish the build")
		else:
			self.emit("waiting for rule checks; Lake may be building dependencies or reusing compiled modules")

	def finish(self,code):
		self.read()
		status="succeeded" if code==0 else f"failed (exit {code})"
		self.emit(f"build {status}; {len(self.completed)} rule checks observed in this run")
		if self.active:
			self.emit("no completed check observed for: "+", ".join(key[1] for key in self.active))
		for key,(elapsed,phase) in sorted(self.completed.items(),key=lambda item:item[1][0],reverse=True)[:5]:
			self.emit(f"slow rule: {key[1]}: {elapsed:.2f}s ({phase})")

def run_build(command,cwd,env,path,total,interval=10):
	progress=Progress(path,total,interval)
	progress.emit(f"progress log: {path}")
	process=subprocess.Popen(command,cwd=cwd,env=env,start_new_session=os.name=="posix")
	interrupted=None
	interrupted_at=None
	def send(signum):
		try:
			if os.name=="posix": os.killpg(process.pid,signum)
			elif process.poll() is None: process.terminate()
		except ProcessLookupError:
			pass
	def forward(signum,frame):
		nonlocal interrupted,interrupted_at
		interrupted=signum
		interrupted_at=time.monotonic()
		send(signum)
	previous={s:signal.signal(s,forward) for s in (signal.SIGINT,signal.SIGTERM)}
	try:
		while process.poll() is None:
			progress.read()
			progress.heartbeat()
			if interrupted_at is not None and time.monotonic()-interrupted_at>5:
				send(signal.SIGKILL)
			try:
				process.wait(timeout=min(interval,0.2))
			except subprocess.TimeoutExpired:
				pass
		code=128+interrupted if interrupted else process.returncode
		if code<0: code=128-code
		progress.finish(code)
		return code
	finally:
		if process.poll() is None:
			send(signal.SIGTERM)
			try:
				process.wait(timeout=5)
			except subprocess.TimeoutExpired:
				send(signal.SIGKILL)
				process.wait()
		if interrupted and os.name=="posix": send(signal.SIGKILL)
		for s,handler in previous.items(): signal.signal(s,handler)
