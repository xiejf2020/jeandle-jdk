/*
 * Copyright (c) 2026, the Jeandle-JDK Authors. All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*
 * @test
 * @summary Jeandle primitive Unsafe weak compare-and-set lowering and fallback
 * @modules java.base/jdk.internal.misc
 * @library /test/lib /
 * @build compiler.jeandle.fileCheck.FileCheck
 * @run main/othervm compiler.jeandle.intrinsic.TestUnsafeWeakCompareAndSetV2
 */
package compiler.jeandle.intrinsic;

import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import compiler.jeandle.fileCheck.FileCheck;
import jdk.internal.misc.Unsafe;
import jdk.test.lib.Asserts;
import jdk.test.lib.process.OutputAnalyzer;
import jdk.test.lib.process.ProcessTools;

public class TestUnsafeWeakCompareAndSetV2 {
    private static final String[] MODES = {"Plain", "Acquire", "Release", ""};
    private static final String[] IDS = {
        "_weakCompareAndSetBytePlain", "_weakCompareAndSetByteAcquire",
        "_weakCompareAndSetByteRelease", "_weakCompareAndSetByte",
        "_weakCompareAndSetShortPlain", "_weakCompareAndSetShortAcquire",
        "_weakCompareAndSetShortRelease", "_weakCompareAndSetShort",
        "_weakCompareAndSetIntPlain", "_weakCompareAndSetIntAcquire",
        "_weakCompareAndSetIntRelease", "_weakCompareAndSetInt",
        "_weakCompareAndSetLongPlain", "_weakCompareAndSetLongAcquire",
        "_weakCompareAndSetLongRelease", "_weakCompareAndSetLong"};

    public static void main(String[] args) throws Exception {
        run(true, null);
        run(false, "-XX:ControlIntrinsic=-" + String.join(",-", IDS));
        run(false, "-XX:-InlineUnsafeOps");
    }

    private static void run(boolean enabled, String extra) throws Exception {
        String dump = Files.createTempDirectory("jeandle_weakcas_v2").toString();
        ArrayList<String> cmd = new ArrayList<>(List.of(
            "--add-exports", "java.base/jdk.internal.misc=ALL-UNNAMED",
            "-Xbatch", "-Xcomp", "-XX:-TieredCompilation", "-XX:+UseJeandleCompiler",
            "-XX:+UnlockDiagnosticVMOptions", "-XX:+JeandleDumpIR",
            "-XX:JeandleDumpDirectory=" + dump, "-Xlog:jeandle=debug",
            "-XX:CompileCommand=compileonly," + Workload.class.getName() + "::weak*"));
        if (extra != null) cmd.add(extra);
        cmd.add(Workload.class.getName());
        OutputAnalyzer out = ProcessTools.executeCommand(
            ProcessTools.createLimitedTestJavaProcessBuilder(cmd));
        out.shouldHaveExitValue(0);
        if (enabled) out.shouldMatch("Method `.*weakCompareAndSetInt.* is parsed as intrinsic");
        FileCheck ir = new FileCheck(dump,
            Workload.class.getMethod("weakInt", Holder.class, int.class, int.class), false);
        if (enabled) ir.checkPattern("cmpxchg weak.*unsafe_cas_int_heap_addr");
        else ir.checkPattern("Unsafe_weakCompareAndSetInt");
    }

    static class Holder { byte b; short s; int i; long l; }
    static class Workload {
        static final Unsafe U = Unsafe.getUnsafe();
        static final long BO, SO, IO, LO;
        static { try {
            BO = U.objectFieldOffset(Holder.class.getDeclaredField("b"));
            SO = U.objectFieldOffset(Holder.class.getDeclaredField("s"));
            IO = U.objectFieldOffset(Holder.class.getDeclaredField("i"));
            LO = U.objectFieldOffset(Holder.class.getDeclaredField("l"));
        } catch (Exception e) { throw new ExceptionInInitializerError(e); } }
        public static boolean weakByte(Holder h, byte e, byte x) { return U.weakCompareAndSetByte(h, BO, e, x); }
        public static boolean weakBytePlain(Holder h, byte e, byte x) { return U.weakCompareAndSetBytePlain(h, BO, e, x); }
        public static boolean weakByteAcquire(Holder h, byte e, byte x) { return U.weakCompareAndSetByteAcquire(h, BO, e, x); }
        public static boolean weakByteRelease(Holder h, byte e, byte x) { return U.weakCompareAndSetByteRelease(h, BO, e, x); }
        public static boolean weakShort(Holder h, short e, short x) { return U.weakCompareAndSetShort(h, SO, e, x); }
        public static boolean weakShortPlain(Holder h, short e, short x) { return U.weakCompareAndSetShortPlain(h, SO, e, x); }
        public static boolean weakShortAcquire(Holder h, short e, short x) { return U.weakCompareAndSetShortAcquire(h, SO, e, x); }
        public static boolean weakShortRelease(Holder h, short e, short x) { return U.weakCompareAndSetShortRelease(h, SO, e, x); }
        public static boolean weakInt(Holder h, int e, int x) { return U.weakCompareAndSetInt(h, IO, e, x); }
        public static boolean weakIntPlain(Holder h, int e, int x) { return U.weakCompareAndSetIntPlain(h, IO, e, x); }
        public static boolean weakIntAcquire(Holder h, int e, int x) { return U.weakCompareAndSetIntAcquire(h, IO, e, x); }
        public static boolean weakIntRelease(Holder h, int e, int x) { return U.weakCompareAndSetIntRelease(h, IO, e, x); }
        public static boolean weakLong(Holder h, long e, long x) { return U.weakCompareAndSetLong(h, LO, e, x); }
        public static boolean weakLongPlain(Holder h, long e, long x) { return U.weakCompareAndSetLongPlain(h, LO, e, x); }
        public static boolean weakLongAcquire(Holder h, long e, long x) { return U.weakCompareAndSetLongAcquire(h, LO, e, x); }
        public static boolean weakLongRelease(Holder h, long e, long x) { return U.weakCompareAndSetLongRelease(h, LO, e, x); }
        public static void main(String[] a) {
            Holder h = new Holder();
            h.b=0; Asserts.assertTrue(weakByte(h,(byte)0,(byte)1)); Asserts.assertFalse(weakByte(h,(byte)0,(byte)2));
            h.s=0; Asserts.assertTrue(weakShort(h,(short)0,(short)1)); Asserts.assertFalse(weakShort(h,(short)0,(short)2));
            h.i=0; Asserts.assertTrue(weakInt(h,0,1)); Asserts.assertFalse(weakInt(h,0,2));
            h.l=0; Asserts.assertTrue(weakLong(h,0,1)); Asserts.assertFalse(weakLong(h,0,2));
            h.b=0; Asserts.assertTrue(weakBytePlain(h,(byte)0,(byte)1)); h.b=0; Asserts.assertTrue(weakByteAcquire(h,(byte)0,(byte)1)); h.b=0; Asserts.assertTrue(weakByteRelease(h,(byte)0,(byte)1));
            h.s=0; Asserts.assertTrue(weakShortPlain(h,(short)0,(short)1)); h.s=0; Asserts.assertTrue(weakShortAcquire(h,(short)0,(short)1)); h.s=0; Asserts.assertTrue(weakShortRelease(h,(short)0,(short)1));
            h.i=0; Asserts.assertTrue(weakIntPlain(h,0,1)); h.i=0; Asserts.assertTrue(weakIntAcquire(h,0,1)); h.i=0; Asserts.assertTrue(weakIntRelease(h,0,1));
            h.l=0; Asserts.assertTrue(weakLongPlain(h,0,1)); h.l=0; Asserts.assertTrue(weakLongAcquire(h,0,1)); h.l=0; Asserts.assertTrue(weakLongRelease(h,0,1));
            long p=U.allocateMemory(4); try { U.putInt(p,0); Asserts.assertTrue(U.weakCompareAndSetInt(null,p,0,1)); } finally { U.freeMemory(p); }
            System.out.println("TestUnsafeWeakCompareAndSetV2 PASSED");
        }
    }
}
