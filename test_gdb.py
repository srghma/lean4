import gdb

class BP(gdb.Breakpoint):
    def stop(self):
        r14 = gdb.parse_and_eval("$r14")
        rbx = gdb.parse_and_eval("$rbx")
        rbp = gdb.parse_and_eval("$rbp")
        if rbx == 1 and rbp == 2 and r14 == 32:
            print("Found lean_alloc_ctor(1, 2, 32)!")
            gdb.execute("backtrace")
            return True
        return False

BP("lean_alloc_ctor")
