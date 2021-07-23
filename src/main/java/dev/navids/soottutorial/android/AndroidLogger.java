package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import java.util.concurrent.locks.*;
public class AndroidLogger {

    private final static String USER_HOME = System.getProperty("user.home");
    private static String androidJar = USER_HOME + "/Documents/android/platforms";
    static String androidDemoPath = System.getProperty("user.dir") + File.separator + "demo" + File.separator + "Android";
    static String apkPath = androidDemoPath + File.separator + "/calc.apk";
    static String outputPath = androidDemoPath + File.separator + "/Instrumented";


    public static void main(String[] args){
        if(System.getenv().containsKey("ANDROID_HOME"))
            androidJar = System.getenv("ANDROID_HOME")+ File.separator+"platforms";
        // Clean the outputPath
        final File[] files = (new File(outputPath)).listFiles();
        if (files != null && files.length > 0) {
            Arrays.asList(files).forEach(File::delete);
        }
        // Initialize Soot
        ReentrantLock lock = new ReentrantLock();
        InstrumentUtil.setupSoot(androidJar, apkPath, outputPath);
        PackManager.v().getPack("jtp").add(new Transform("jtp.test", new BodyTransformer() {
            @Override
            protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
                // First we filter out Android framework methods
                if(AndroidUtil.isAndroidMethod(b.getMethod()))
                    return;
                JimpleBody body = (JimpleBody) b;
                UnitPatchingChain units = b.getUnits();
                Iterator<Unit> it = units.iterator();
                lock.lock();
                while (it.hasNext()) {
                    Unit unit = it.next();
                    if (unit instanceof JAssignStmt) {

                        System.out.println("\tUNIT: " + unit.toString());
                        System.out.println("\tSoot type: " + unit.getClass().getName());
                        Value lhs = ((JAssignStmt)unit).getLeftOp();
                        Value rhs = ((JAssignStmt)unit).getRightOp();
                        if (lhs instanceof JInstanceFieldRef) {
                            // TODO: Record write
                        }
                        if (rhs insanceof JInstanceFieldRef) {
                            // TODO: Record read
                        }
                        System.out.println("LHS " + lhs.toString() + " (type: " + lhs.getType().toString() + ") , ");
                        System.out.println("Soot type: "+ lhs.getClass().getName());
                        System.out.println("RHS " + rhs.toString() + " (type: " + rhs.getType().toString() + ") , ");
                        System.out.println("Soot type: "+ rhs.getClass().getName());
                        System.out.println("\n------------------\n");
                    }

                }

                lock.unlock();
            }
        }));
        // Add a transformation pack in order to add the statement "System.out.println(<content>) at the beginning of each Application method
        PackManager.v().getPack("jtp").add(new Transform("jtp.myLogger", new BodyTransformer() {
            @Override
            protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
                // First we filter out Android framework methods
                if(AndroidUtil.isAndroidMethod(b.getMethod()))
                    return;
                JimpleBody body = (JimpleBody) b;
                UnitPatchingChain units = b.getUnits();
                List<Unit> generatedUnits = new ArrayList<>();

                // The message that we want to log
                String content = String.format("%s Beginning of method %s", InstrumentUtil.TAG, body.getMethod().getSignature());
                // In order to call "System.out.println" we need to create a local containing "System.out" value
                Local psLocal = InstrumentUtil.generateNewLocal(body, RefType.v("java.io.PrintStream"));
                // Now we assign "System.out" to psLocal
                SootField sysOutField = Scene.v().getField("<java.lang.System: java.io.PrintStream out>");
                AssignStmt sysOutAssignStmt = Jimple.v().newAssignStmt(psLocal, Jimple.v().newStaticFieldRef(sysOutField.makeRef()));
                generatedUnits.add(sysOutAssignStmt);

                // Create println method call and provide its parameter
                SootMethod printlnMethod = Scene.v().grabMethod("<java.io.PrintStream: void println(java.lang.String)>");
                Value printlnParamter = StringConstant.v(content);
                InvokeStmt printlnMethodCallStmt = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(psLocal, printlnMethod.makeRef(), printlnParamter));
                generatedUnits.add(printlnMethodCallStmt);

                // Insert the generated statement before the first  non-identity stmt
                units.insertBefore(generatedUnits, body.getFirstNonIdentityStmt());
                // Validate the body to ensure that our code injection does not introduce any problem (at least statically)
                b.validate();
            }
        }));
        // Run Soot packs (note that our transformer pack is added to the phase "jtp")
        PackManager.v().runPacks();
        // Write the result of packs in outputPath
        PackManager.v().writeOutput();
    }

    static SootClass createCounterClass(String packageName) {
        String signature = packageName + ".StaticCounter";
        SootClass counterClass = new SootClass(signature, Modifier.PUBLIC);
        counterClass.setSuperclass(Scene.v().getSootClass("java.lang.Object")); 
        counterClass.setApplicationClass();
        return counterClass;
    }
    // Create new counter for every new object type encountered
    static SootField addCounter(SootClass counterClass, String typeName) {
        SootField counterField = new SootField(typeName + "counter", 
            IntType.v(), Modifier.PUBLIC | Modifier.STATIC);
        counterClass.addField(counterField);
        return counterField;
    }
    static SootMethod createMethod(SootClass counterClass, String typeName, SootField counterField) {
        SootMethod incMethod = new SootMethod("increment" + typeName,
            Arrays.asList(new Type[]{}),
            VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        counterClass.addMethod(incMethod);
        JimpleBody body = Jimple.v().newBody(incMethod);
        UnitPatchingChain units = body.getUnits();
        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        units.add(Jimple.v().newAssignStmt(counterLocal, Jimple.v().newStaticFieldRef(counterField.makeRef())));
 
        units.add(Jimple.v().newAssignStmt(counterLocal, 
                Jimple.v().newAddExpr(counterLocal, IntConstant.v(1))));
        units.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(counterField.makeRef()), counterLocal));
        units.addAll(InstrumentUtil.generateLogStmts(body, typeName + " counter = ", counterLocal));
        Unit returnUnit = Jimple.v().newReturnVoidStmt();
        units.add(returnUnit);
        body.validate();
        incMethod.setActiveBody(body);
        return incMethod;
    }
   
}
