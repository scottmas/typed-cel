"""Single-step one call between two int3 markers; print each executed RIP (file-relative, hex)."""
import ctypes, os, sys, signal
libc = ctypes.CDLL(None, use_errno=True)
libc.ptrace.restype = ctypes.c_long
libc.ptrace.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_void_p, ctypes.c_void_p]
TRACEME, PEEKTEXT, CONT, SINGLESTEP, GETREGS = 0, 1, 7, 9, 12
class Regs(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulonglong) for n in (
        "r15 r14 r13 r12 rbp rbx r11 r10 r9 r8 rax rcx rdx rsi rdi orig_rax rip cs eflags rsp ss "
        "fs_base gs_base ds es fs gs").split()]
pid = os.fork()
if pid == 0:
    libc.ptrace(TRACEME, 0, None, None)
    os.execv(sys.argv[1], sys.argv[1:])
os.waitpid(pid, 0)                                   # stopped at exec
libc.ptrace(CONT, pid, None, None); os.waitpid(pid, 0)   # stopped at the first int3
exe = os.path.basename(sys.argv[1])
base = next(int(l.split("-")[0], 16) for l in open(f"/proc/{pid}/maps") if exe in l)
out = []
while True:
    libc.ptrace(SINGLESTEP, pid, None, None)
    _, st = os.waitpid(pid, 0)
    if not os.WIFSTOPPED(st):
        break
    r = Regs(); libc.ptrace(GETREGS, pid, None, ctypes.byref(r))
    if libc.ptrace(PEEKTEXT, pid, ctypes.c_void_p(r.rip), None) & 0xff == 0xcc:
        break                                        # the second int3
    out.append(r.rip - base)
os.kill(pid, signal.SIGKILL)
print("\n".join("%x" % a for a in out))
