"""Batch only known self-contained exporter namespaces, retaining source snapshots."""
import re

def make_batches(root,certificates,size):
	if size==1:
		return list(certificates),{}
	checks=[]; members={}; pending=[]; counters={}
	directory=root/"build/verification"
	directory.mkdir(exist_ok=True)
	def flush():
		if not pending:
			return
		category=pending[0][0].parent.relative_to(root).as_posix().replace("/","_")
		index=counters.get(category,0); counters[category]=index+1
		path=directory/f"{category}_{index}.lean"
		parts=["import QSym\n"]
		for i,(file,original) in enumerate(pending):
			source=re.sub(r"^import QSym\n","",original.decode(),flags=re.M)
			source=source.replace("QSym.Certificate","QSym.BatchCertificate"+str(i))
			source=source.replace("QSym.DomainCertificate","QSym.BatchDomainCertificate"+str(i))
			source=re.sub(r"\bCertificate\.","BatchCertificate"+str(i)+".",source)
			parts.append("-- "+str(file.relative_to(root))+"\n"+source)
		path.write_text("\n".join(parts))
		checks.append(path); members[path]=pending.copy(); pending.clear()
	for file in certificates:
		source=file.read_bytes(); text=source.decode()
		if pending and file.parent!=pending[-1][0].parent:
			flush()
		if re.findall(r"^namespace ([^\n]+)",text,re.M) in (["QSym.Certificate"],["QSym.Certificate","QSym.DomainCertificate"]) and re.findall(r"^import ([^\n]+)",text,re.M)==["QSym"]:
			pending.append((file,source))
			if len(pending)==size:
				flush()
		else:
			flush(); checks.append(file)
	flush()
	return checks,members
