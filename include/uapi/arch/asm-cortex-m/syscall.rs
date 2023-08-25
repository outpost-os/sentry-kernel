#[inline]
pub unsafe fn forge_syscall0(n: Sysno) -> usize {
    let mut ret: usize;
    asm!(
        "svc 0",
        in("r7") n as usize,
        lateout("r0") ret,
        options(nostack, preserves_flags)
    );
    ret
}

#[inline]
pub unsafe fn forge_syscall1(n: Sysno, arg1: usize) -> usize {
    let mut ret: usize;
    asm!(
        "svc 0",
        in("r7") n as usize,
        in("r0") arg1,
        lateout("r0") ret,
        options(nostack, preserves_flags)
    );
    ret
}

#[inline]
pub unsafe fn forge_syscall2(n: Sysno, arg1: usize, arg2: usize) -> usize {
    let mut ret: usize;
    asm!(
        "svc 0",
        in("r7") n as usize,
        in("r0") arg1,
        in("r1") arg2,
        lateout("r0") ret,
        options(nostack, preserves_flags)
    );
    ret
}

#[inline]
pub unsafe fn forge_syscall3(n: Sysno, arg1: usize, arg2: usize, arg3: usize) -> usize {
    let mut ret: usize;
    asm!(
        "svc 0",
        in("r7") n as usize,
        in("r0") arg1,
        in("r1") arg2,
        in("r2") arg3,
        lateout("r0") ret,
        options(nostack, preserves_flags)
    );
    ret
}

#[inline]
pub unsafe fn forge_syscall4(n: Sysno, arg1: usize, arg2: usize, arg3: usize, arg4: usize) -> usize {
    let mut ret: usize;
    asm!(
        "svc 0",
        in("r7") n as usize,
        in("r0") arg1,
        in("r1") arg2,
        in("r2") arg3,
        in("r3") arg4,
        lateout("r0") ret,
        options(nostack, preserves_flags)
    );
    ret
}
